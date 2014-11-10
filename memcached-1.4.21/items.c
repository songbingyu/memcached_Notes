/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/signal.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>

/* Forward Declarations */
static void item_link_q(item *it);
static void item_unlink_q(item *it);

#define LARGEST_ID POWER_LARGEST
typedef struct {
    uint64_t evicted;
    uint64_t evicted_nonzero;
    rel_time_t evicted_time;
    uint64_t reclaimed;
    uint64_t outofmemory;
    uint64_t tailrepairs;
    uint64_t expired_unfetched;
    uint64_t evicted_unfetched;
    uint64_t crawler_reclaimed;
    uint64_t lrutail_reflocked;
} itemstats_t;

static item *heads[LARGEST_ID];
static item *tails[LARGEST_ID];
static crawler crawlers[LARGEST_ID];
static itemstats_t itemstats[LARGEST_ID];
static unsigned int sizes[LARGEST_ID];

static int crawler_count = 0;
static volatile int do_run_lru_crawler_thread = 0;
static int lru_crawler_initialized = 0;
static pthread_mutex_t lru_crawler_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  lru_crawler_cond = PTHREAD_COND_INITIALIZER;

void item_stats_reset(void) {
    mutex_lock(&cache_lock);
    memset(itemstats, 0, sizeof(itemstats));
    mutex_unlock(&cache_lock);
}


/* Get the next CAS id for a new item. */
uint64_t get_cas_id(void) {
    static uint64_t cas_id = 0;
    return ++cas_id;
}

/* Enable this for reference-count debugging. */
#if 0
# define DEBUG_REFCNT(it,op) \
                fprintf(stderr, "item %x refcnt(%c) %d %c%c%c\n", \
                        it, op, it->refcount, \
                        (it->it_flags & ITEM_LINKED) ? 'L' : ' ', \
                        (it->it_flags & ITEM_SLABBED) ? 'S' : ' ')
#else
# define DEBUG_REFCNT(it,op) while(0)
#endif

/**
 * Generates the variable-sized part of the header for an object.
 *
 * key     - The key
 * nkey    - The length of the key
 * flags   - key flags
 * nbytes  - Number of bytes to hold value and addition CRLF terminator
 * suffix  - Buffer for the "VALUE" line suffix (flags, size).
 * nsuffix - The length of the suffix is stored here.
 *
 * Returns the total size of the header.
 */
static size_t item_make_header(const uint8_t nkey, const int flags, const int nbytes,
                     char *suffix, uint8_t *nsuffix) {
    /* suffix is defined at 40 chars elsewhere.. */
    *nsuffix = (uint8_t) snprintf(suffix, 40, " %d %d\r\n", flags, nbytes - 2);
    return sizeof(item) + nkey + *nsuffix + nbytes;
}

/*@null@*/
//分配一个指定大小的item 执行item的存储操作,该操作会将item挂载到LRU表和slabcalss中
//参考 http://blog.csdn.net/lcli2009/article/details/22091167
// http://blog.csdn.net/lcli2009/article/details/22095251
item *do_item_alloc(char *key, const size_t nkey, const int flags,
                    const rel_time_t exptime, const int nbytes,
                    const uint32_t cur_hv) {
    uint8_t nsuffix;
    item *it = NULL;
    char suffix[40];
    size_t ntotal = item_make_header(nkey + 1, flags, nbytes, suffix, &nsuffix);
	//如果使用了CAS 增加空间
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }
	//选择合适的slab
    unsigned int id = slabs_clsid(ntotal);
    if (id == 0)
        return 0;

	//执行LRU锁  
    mutex_lock(&cache_lock);
	//存储时，会尝试从LRU中选择合适的空间的空间  
    /* do a quick check if we have any expired items in the tail.. */
    int tries = 5;
    /* Avoid hangs if a slab has nothing but refcounted stuff in it. */
    int tries_lrutail_reflocked = 1000;
    int tried_alloc = 0;
    item *search;
    item *next_it;
    void *hold_lock = NULL;
	//初始化时选择的过期时间  
    rel_time_t oldest_live = settings.oldest_live;
	//heads和tails指针，分别指向最老的数据和最新的数据，这样便于LRU链表的操作
    search = tails[id];
    /* We walk up *only* for locked items. Never searching for expired.
     * Waste of CPU for almost all deployments */
    for (; tries > 0 && search != NULL; tries--, search=next_it) {
        /* we might relink search mid-loop, so search->prev isn't reliable */
        next_it = search->prev;
        if (search->nbytes == 0 && search->nkey == 0 && search->it_flags == 1) {
            /* We are a crawler, ignore it. */
            tries++;
            continue;
        }
        uint32_t hv = hash(ITEM_key(search), search->nkey);
        /* Attempt to hash item lock the "search" item. If locked, no
         * other callers can incr the refcount
         */
        /* Don't accidentally grab ourselves, or bail if we can't quicklock */
		//尝试执行锁操作，这里执行的乐观锁
		if (hv == cur_hv || (hold_lock = item_trylock(hv)) == NULL) 
            continue;
        /* Now see if the item is refcount locked */
		//判断item是否被锁住，item的引用次数其实充当的也是一种锁 
		//这段代码其实是try 最多tries_lrutail_reflocked 1000 遍，看是不是能够获得锁
        if (refcount_incr(&search->refcount) != 2) {
            /* Avoid pathological case with ref'ed items in tail */
            do_item_update_nolock(search);
            tries_lrutail_reflocked--;
            tries++;
            refcount_decr(&search->refcount);
            itemstats[id].lrutail_reflocked++;
            /* Old rare bug could cause a refcount leak. We haven't seen
             * it in years, but we leave this code in to prevent failures
             * just in case */
			//如果it的添加时间比当前时间小于3*3600  
            if (settings.tail_repair_time &&
                    search->time + settings.tail_repair_time < current_time) {
                itemstats[id].tailrepairs++;
                search->refcount = 1;
				// 执行分段解锁操作
                do_item_unlink_nolock(search, hv);
            }
            if (hold_lock)
                item_trylock_unlock(hold_lock);

            if (tries_lrutail_reflocked < 1)
                break;

            continue;
        }

        /* Expired or flushed */
        if ((search->exptime != 0 && search->exptime < current_time)
            || (search->time <= oldest_live && oldest_live <= current_time)) {
            itemstats[id].reclaimed++;
            if ((search->it_flags & ITEM_FETCHED) == 0) {
                itemstats[id].expired_unfetched++;
            }
            it = search;
			//slabclass申请合适的空间
			//其实只是slab已经分配的内存改变一下指针
            slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal);
            do_item_unlink_nolock(it, hv);
            /* Initialize the item block: */
            it->slabs_clsid = 0;
        } else if ((it = slabs_alloc(ntotal, id)) == NULL) {
            tried_alloc = 1;
            if (settings.evict_to_free == 0) {// 关闭LRU
                itemstats[id].outofmemory++;
            } else {
				//静态统计
				itemstats[id].evicted++; //这个slab的分配失败次数加1，后面的分析统计信息的线程会用到这个统计信息
                itemstats[id].evicted_time = current_time - search->time;//显示的统计信息
                if (search->exptime != 0)
                    itemstats[id].evicted_nonzero++;
                if ((search->it_flags & ITEM_FETCHED) == 0) {
                    itemstats[id].evicted_unfetched++;
                }
                it = search;
				//slabclass申请合适的空间
				//其实只是slab已经分配的内存改变一下指针
                slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal);
                do_item_unlink_nolock(it, hv);
                /* Initialize the item block: */
                it->slabs_clsid = 0;

                /* If we've just evicted an item, and the automover is set to
                 * angry bird mode, attempt to rip memory into this slab class.
                 * TODO: Move valid object detection into a function, and on a
                 * "successful" memory pull, look behind and see if the next alloc
                 * would be an eviction. Then kick off the slab mover before the
                 * eviction happens.
                 */
				//激进模式
				///可以看到如果slab_automove=2(默认是1)，这样会导致angry模式，
				//就是只要分配失败了，马上就选择一个slab，把这个空间移动到当前slab-class中（不会有通过统计信息有选择的移动slab）
                if (settings.slab_automove == 2)
                    slabs_reassign(-1, id);
            }
        }

        refcount_decr(&search->refcount);
        /* If hash values were equal, we don't grab a second lock */
        if (hold_lock)
            item_trylock_unlock(hold_lock);
        break;
    }

	//此时还没找到对应的内存
    if (!tried_alloc && (tries == 0 || search == NULL))
        it = slabs_alloc(ntotal, id);

    if (it == NULL) {
        itemstats[id].outofmemory++;
        mutex_unlock(&cache_lock);
        return NULL;
    }

    assert(it->slabs_clsid == 0);
    assert(it != heads[id]);

    /* Item initialization can happen outside of the lock; the item's already
     * been removed from the slab LRU.
     */
	//下面就是各种xxx赋值
    it->refcount = 1;     /* the caller will have a reference */
    mutex_unlock(&cache_lock);
    it->next = it->prev = it->h_next = 0;
    it->slabs_clsid = id;

    DEBUG_REFCNT(it, '*');
    it->it_flags = settings.use_cas ? ITEM_CAS : 0;
    it->nkey = nkey;
    it->nbytes = nbytes;
    memcpy(ITEM_key(it), key, nkey);
    it->exptime = exptime;
    memcpy(ITEM_suffix(it), suffix, (size_t)nsuffix);
    it->nsuffix = nsuffix;
    return it;
}

void item_free(item *it) {
	// size
    size_t ntotal = ITEM_ntotal(it);
    unsigned int clsid;
	//各种判断
    assert((it->it_flags & ITEM_LINKED) == 0);
    assert(it != heads[it->slabs_clsid]);
    assert(it != tails[it->slabs_clsid]);
	//ref 0 
    assert(it->refcount == 0);

    /* so slab size changer can tell later if item is already free or not */
    clsid = it->slabs_clsid;
    it->slabs_clsid = 0;
    DEBUG_REFCNT(it, 'F');
	//放到free list 里面
    slabs_free(it, ntotal, clsid);
}

/**
 * Returns true if an item will fit in the cache (its size does not exceed
 * the maximum for a cache entry.)
 */
bool item_size_ok(const size_t nkey, const int flags, const int nbytes) {
    char prefix[40];
    uint8_t nsuffix;

    size_t ntotal = item_make_header(nkey + 1, flags, nbytes,
                                     prefix, &nsuffix);
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

    return slabs_clsid(ntotal) != 0;
}
//将item加入到对应classid的LRU链的head，这里是item加入到LRU链表中  
static void item_link_q(item *it) { /* item is the new head */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    assert(it != *head);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = 0;
    it->next = *head;
    if (it->next) it->next->prev = it;
    *head = it;
    if (*tail == 0) *tail = it;
    sizes[it->slabs_clsid]++;
    return;
}
//将item从对应classid的LRU链上移除，这里是item从LRU链表中删除  
static void item_unlink_q(item *it) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    sizes[it->slabs_clsid]--;
    return;
}

// 将item放入hashtable和LRU队列  
//http://blog.csdn.net/tankles/article/details/7048483
int do_item_link(item *it, const uint32_t hv) {

    MEMCACHED_ITEM_LINK(ITEM_key(it), it->nkey, it->nbytes);
	//标志判断
    assert((it->it_flags & (ITEM_LINKED|ITEM_SLABBED)) == 0);
   //cache_lock主要用于保护hashtable 及其相关链表。
	mutex_lock(&cache_lock);//http://www.fanzhihui.com/2012/04/memcache-sync/
    it->it_flags |= ITEM_LINKED;
	// 最近访问时间为当前时间
    it->time = current_time;

    STATS_LOCK();
    stats.curr_bytes += ITEM_ntotal(it);
    stats.curr_items += 1;
    stats.total_items += 1;
    STATS_UNLOCK();

    /* Allocate a new CAS ID on link. */
	// 调用get_cas_id()给item的cas_id赋值
    ITEM_set_cas(it, (settings.use_cas) ? get_cas_id() : 0);
	// 将item指针插入hash表中 
    assoc_insert(it, hv);
	//加入ＬＲＵ
    item_link_q(it);
    refcount_incr(&it->refcount);

    mutex_unlock(&cache_lock);

    return 1;
}
// 从hashtable及LRU队列摘除item项 
//http://blog.csdn.net/tankles/article/details/7048483

void do_item_unlink(item *it, const uint32_t hv) {
	
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    mutex_lock(&cache_lock);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
        assoc_delete(ITEM_key(it), it->nkey, hv);
        item_unlink_q(it);
        do_item_remove(it);
    }
    mutex_unlock(&cache_lock);
}

// 从hashtable及LRU队列摘除item项 
/* FIXME: Is it necessary to keep this copy/pasted code? */
void do_item_unlink_nolock(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
        assoc_delete(ITEM_key(it), it->nkey, hv);
        item_unlink_q(it);
        do_item_remove(it);
    }
}
// 引用计数为0的时候，就将其释放  
void do_item_remove(item *it) {
    MEMCACHED_ITEM_REMOVE(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);
    assert(it->refcount > 0);
	//引用计数为0
    if (refcount_decr(&it->refcount) == 0) {
        item_free(it);
    }
}

/* Copy/paste to avoid adding two extra branches for all common calls, since
 * _nolock is only used in an uncommon case. */
// 更新item时间戳  
// 先调用item_unlink_q(),更新了时间以后，再调用item_link_q(),  
// 将其重新连接到LRU队列之中，即让该item移到LRU队列的最前
void do_item_update_nolock(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        if ((it->it_flags & ITEM_LINKED) != 0) {
            item_unlink_q(it);
            it->time = current_time;
            item_link_q(it);
        }
    }
}

// 更新item时间戳  
// 先调用item_unlink_q(),更新了时间以后，再调用item_link_q(),  
// 将其重新连接到LRU队列之中，即让该item移到LRU队列的最前
void do_item_update(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        mutex_lock(&cache_lock);
        if ((it->it_flags & ITEM_LINKED) != 0) {
            item_unlink_q(it);
            it->time = current_time;
            item_link_q(it);
        }
        mutex_unlock(&cache_lock);
    }
}

// 调用do_item_unlink()解除原有it的连接，再调用do_item_link()连接到新的new_it  
int do_item_replace(item *it, item *new_it, const uint32_t hv) {
    MEMCACHED_ITEM_REPLACE(ITEM_key(it), it->nkey, it->nbytes,
                           ITEM_key(new_it), new_it->nkey, new_it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    do_item_unlink(it, hv);
    return do_item_link(new_it, hv);
}

/*@null@*/
char *do_item_cachedump(const unsigned int slabs_clsid, const unsigned int limit, unsigned int *bytes) {
    unsigned int memlimit = 2 * 1024 * 1024;   /* 2MB max response size */
    char *buffer;
    unsigned int bufcurr;
    item *it;
    unsigned int len;
    unsigned int shown = 0;
    char key_temp[KEY_MAX_LENGTH + 1];
    char temp[512];

    it = heads[slabs_clsid];

    buffer = malloc((size_t)memlimit);
    if (buffer == 0) return NULL;
    bufcurr = 0;

    while (it != NULL && (limit == 0 || shown < limit)) {
        assert(it->nkey <= KEY_MAX_LENGTH);
        if (it->nbytes == 0 && it->nkey == 0) {
            it = it->next;
            continue;
        }
        /* Copy the key since it may not be null-terminated in the struct */
        strncpy(key_temp, ITEM_key(it), it->nkey);
        key_temp[it->nkey] = 0x00; /* terminate */
        len = snprintf(temp, sizeof(temp), "ITEM %s [%d b; %lu s]\r\n",
                       key_temp, it->nbytes - 2,
                       (unsigned long)it->exptime + process_started);
        if (bufcurr + len + 6 > memlimit)  /* 6 is END\r\n\0 */
            break;
        memcpy(buffer + bufcurr, temp, len);
        bufcurr += len;
        shown++;
        it = it->next;
    }

    memcpy(buffer + bufcurr, "END\r\n", 6);
    bufcurr += 5;

    *bytes = bufcurr;
    return buffer;
}

void item_stats_evictions(uint64_t *evicted) {
    int i;
    mutex_lock(&cache_lock);
    for (i = 0; i < LARGEST_ID; i++) {
        evicted[i] = itemstats[i].evicted;
    }
    mutex_unlock(&cache_lock);
}

void do_item_stats_totals(ADD_STAT add_stats, void *c) {
    itemstats_t totals;
    memset(&totals, 0, sizeof(itemstats_t));
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        totals.expired_unfetched += itemstats[i].expired_unfetched;
        totals.evicted_unfetched += itemstats[i].evicted_unfetched;
        totals.evicted += itemstats[i].evicted;
        totals.reclaimed += itemstats[i].reclaimed;
        totals.crawler_reclaimed += itemstats[i].crawler_reclaimed;
        totals.lrutail_reflocked += itemstats[i].lrutail_reflocked;
    }
    APPEND_STAT("expired_unfetched", "%llu",
                (unsigned long long)totals.expired_unfetched);
    APPEND_STAT("evicted_unfetched", "%llu",
                (unsigned long long)totals.evicted_unfetched);
    APPEND_STAT("evictions", "%llu",
                (unsigned long long)totals.evicted);
    APPEND_STAT("reclaimed", "%llu",
                (unsigned long long)totals.reclaimed);
    APPEND_STAT("crawler_reclaimed", "%llu",
                (unsigned long long)totals.crawler_reclaimed);
    APPEND_STAT("lrutail_reflocked", "%llu",
                (unsigned long long)totals.lrutail_reflocked);
}

void do_item_stats(ADD_STAT add_stats, void *c) {
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        if (tails[i] != NULL) {
            const char *fmt = "items:%d:%s";
            char key_str[STAT_KEY_LEN];
            char val_str[STAT_VAL_LEN];
            int klen = 0, vlen = 0;
            if (tails[i] == NULL) {
                /* We removed all of the items in this slab class */
                continue;
            }
            APPEND_NUM_FMT_STAT(fmt, i, "number", "%u", sizes[i]);
            APPEND_NUM_FMT_STAT(fmt, i, "age", "%u", current_time - tails[i]->time);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted",
                                "%llu", (unsigned long long)itemstats[i].evicted);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_nonzero",
                                "%llu", (unsigned long long)itemstats[i].evicted_nonzero);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_time",
                                "%u", itemstats[i].evicted_time);
            APPEND_NUM_FMT_STAT(fmt, i, "outofmemory",
                                "%llu", (unsigned long long)itemstats[i].outofmemory);
            APPEND_NUM_FMT_STAT(fmt, i, "tailrepairs",
                                "%llu", (unsigned long long)itemstats[i].tailrepairs);
            APPEND_NUM_FMT_STAT(fmt, i, "reclaimed",
                                "%llu", (unsigned long long)itemstats[i].reclaimed);
            APPEND_NUM_FMT_STAT(fmt, i, "expired_unfetched",
                                "%llu", (unsigned long long)itemstats[i].expired_unfetched);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_unfetched",
                                "%llu", (unsigned long long)itemstats[i].evicted_unfetched);
            APPEND_NUM_FMT_STAT(fmt, i, "crawler_reclaimed",
                                "%llu", (unsigned long long)itemstats[i].crawler_reclaimed);
            APPEND_NUM_FMT_STAT(fmt, i, "lrutail_reflocked",
                                "%llu", (unsigned long long)itemstats[i].lrutail_reflocked);
        }
    }

    /* getting here means both ascii and binary terminators fit */
    add_stats(NULL, 0, NULL, 0, c);
}

/** dumps out a list of objects of each size, with granularity of 32 bytes */
/*@null@*/
void do_item_stats_sizes(ADD_STAT add_stats, void *c) {

    /* max 1MB object, divided into 32 bytes size buckets */
    const int num_buckets = 32768;
    unsigned int *histogram = calloc(num_buckets, sizeof(int));

    if (histogram != NULL) {
        int i;

        /* build the histogram */
        for (i = 0; i < LARGEST_ID; i++) {
            item *iter = heads[i];
            while (iter) {
                int ntotal = ITEM_ntotal(iter);
                int bucket = ntotal / 32;
                if ((ntotal % 32) != 0) bucket++;
                if (bucket < num_buckets) histogram[bucket]++;
                iter = iter->next;
            }
        }

        /* write the buffer */
        for (i = 0; i < num_buckets; i++) {
            if (histogram[i] != 0) {
                char key[8];
                snprintf(key, sizeof(key), "%d", i * 32);
                APPEND_STAT(key, "%u", histogram[i]);
            }
        }
        free(histogram);
    }
    add_stats(NULL, 0, NULL, 0, c);
}

/** wrapper around assoc_find which does the lazy expiration logic */
item *do_item_get(const char *key, const size_t nkey, const uint32_t hv) {
    //mutex_lock(&cache_lock);

	//find 
    item *it = assoc_find(key, nkey, hv);
	//增加计数
    if (it != NULL) {
        refcount_incr(&it->refcount);
        /* Optimization for slab reassignment. prevents popular items from
         * jamming in busy wait. Can only do this here to satisfy lock order
         * of item_lock, cache_lock, slabs_lock. */
        if (slab_rebalance_signal &&
            ((void *)it >= slab_rebal.slab_start && (void *)it < slab_rebal.slab_end)) {
            do_item_unlink_nolock(it, hv);
            do_item_remove(it);
            it = NULL;
        }
    }
    //mutex_unlock(&cache_lock);
    int was_found = 0;

	//打印
    if (settings.verbose > 2) {
        int ii;
        if (it == NULL) {
            fprintf(stderr, "> NOT FOUND ");
        } else {
            fprintf(stderr, "> FOUND KEY ");
            was_found++;
        }
        for (ii = 0; ii < nkey; ++ii) {
            fprintf(stderr, "%c", key[ii]);
        }
    }

    if (it != NULL) {
		//超时了
        if (settings.oldest_live != 0 && settings.oldest_live <= current_time &&
            it->time <= settings.oldest_live) {
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by flush");
            }
        } else if (it->exptime != 0 && it->exptime <= current_time) {
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by expire");
            }
        } else {
            it->it_flags |= ITEM_FETCHED;
            DEBUG_REFCNT(it, '+');
        }
    }

    if (settings.verbose > 2)
        fprintf(stderr, "\n");

    return it;
}

item *do_item_touch(const char *key, size_t nkey, uint32_t exptime,
                    const uint32_t hv) {
    item *it = do_item_get(key, nkey, hv);
    if (it != NULL) {
        it->exptime = exptime;
    }
    return it;
}

/* expires items that are more recent than the oldest_live setting. */
void do_item_flush_expired(void) {
    int i;
    item *iter, *next;
    if (settings.oldest_live == 0)
        return;
    for (i = 0; i < LARGEST_ID; i++) {
        /* The LRU is sorted in decreasing time order, and an item's timestamp
         * is never newer than its last access time, so we only need to walk
         * back until we hit an item older than the oldest_live time.
         * The oldest_live checking will auto-expire the remaining items.
         */
        for (iter = heads[i]; iter != NULL; iter = next) {
            /* iter->time of 0 are magic objects. */
            if (iter->time != 0 && iter->time >= settings.oldest_live) {
                next = iter->next;
                if ((iter->it_flags & ITEM_SLABBED) == 0) {
                    do_item_unlink_nolock(iter, hash(ITEM_key(iter), iter->nkey));
                }
            } else {
                /* We've hit the first old item. Continue to the next queue. */
                break;
            }
        }
    }
}

static void crawler_link_q(item *it) { /* item is the new tail */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    assert(*tail != 0);
    assert(it != *tail);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = *tail;
    it->next = 0;
    if (it->prev) {
        assert(it->prev->next == 0);
        it->prev->next = it;
    }
    *tail = it;
    if (*head == 0) *head = it;
    return;
}

static void crawler_unlink_q(item *it) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    return;
}

/* This is too convoluted, but it's a difficult shuffle. Try to rewrite it
 * more clearly. */
static item *crawler_crawl_q(item *it) {
    item **head, **tail;
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    /* We've hit the head, pop off */
    if (it->prev == 0) {
        assert(*head == it);
        if (it->next) {
            *head = it->next;
            assert(it->next->prev == it);
            it->next->prev = 0;
        }
        return NULL; /* Done */
    }

    /* Swing ourselves in front of the next item */
    /* NB: If there is a prev, we can't be the head */
    assert(it->prev != it);
    if (it->prev) {
        if (*head == it->prev) {
            /* Prev was the head, now we're the head */
            *head = it;
        }
        if (*tail == it) {
            /* We are the tail, now they are the tail */
            *tail = it->prev;
        }
        assert(it->next != it);
        if (it->next) {
            assert(it->prev->next == it);
            it->prev->next = it->next;
            it->next->prev = it->prev;
        } else {
            /* Tail. Move this above? */
            it->prev->next = 0;
        }
        /* prev->prev's next is it->prev */
        it->next = it->prev;
        it->prev = it->next->prev;
        it->next->prev = it;
        /* New it->prev now, if we're not at the head. */
        if (it->prev) {
            it->prev->next = it;
        }
    }
    assert(it->next != it);
    assert(it->prev != it);

    return it->next; /* success */
}

/* I pulled this out to make the main thread clearer, but it reaches into the
 * main thread's values too much. Should rethink again.
 */
static void item_crawler_evaluate(item *search, uint32_t hv, int i) {
    rel_time_t oldest_live = settings.oldest_live;
    if ((search->exptime != 0 && search->exptime < current_time)
        || (search->time <= oldest_live && oldest_live <= current_time)) {
        itemstats[i].crawler_reclaimed++;

        if (settings.verbose > 1) {
            int ii;
            char *key = ITEM_key(search);
            fprintf(stderr, "LRU crawler found an expired item (flags: %d, slab: %d): ",
                search->it_flags, search->slabs_clsid);
            for (ii = 0; ii < search->nkey; ++ii) {
                fprintf(stderr, "%c", key[ii]);
            }
            fprintf(stderr, "\n");
        }
        if ((search->it_flags & ITEM_FETCHED) == 0) {
            itemstats[i].expired_unfetched++;
        }
        do_item_unlink_nolock(search, hv);
        do_item_remove(search);
        assert(search->slabs_clsid == 0);
    } else {
        refcount_decr(&search->refcount);
    }
}

static void *item_crawler_thread(void *arg) {
    int i;

    pthread_mutex_lock(&lru_crawler_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "Starting LRU crawler background thread\n");
    while (do_run_lru_crawler_thread) {
    pthread_cond_wait(&lru_crawler_cond, &lru_crawler_lock);

    while (crawler_count) {
        item *search = NULL;
        void *hold_lock = NULL;

        for (i = 0; i < LARGEST_ID; i++) {
            if (crawlers[i].it_flags != 1) {
                continue;
            }
            pthread_mutex_lock(&cache_lock);
            search = crawler_crawl_q((item *)&crawlers[i]);
            if (search == NULL ||
                (crawlers[i].remaining && --crawlers[i].remaining < 1)) {
                if (settings.verbose > 2)
                    fprintf(stderr, "Nothing left to crawl for %d\n", i);
                crawlers[i].it_flags = 0;
                crawler_count--;
                crawler_unlink_q((item *)&crawlers[i]);
                pthread_mutex_unlock(&cache_lock);
                continue;
            }
            uint32_t hv = hash(ITEM_key(search), search->nkey);
            /* Attempt to hash item lock the "search" item. If locked, no
             * other callers can incr the refcount
             */
            if ((hold_lock = item_trylock(hv)) == NULL) {
                pthread_mutex_unlock(&cache_lock);
                continue;
            }
            /* Now see if the item is refcount locked */
            if (refcount_incr(&search->refcount) != 2) {
                refcount_decr(&search->refcount);
                if (hold_lock)
                    item_trylock_unlock(hold_lock);
                pthread_mutex_unlock(&cache_lock);
                continue;
            }

            /* Frees the item or decrements the refcount. */
            /* Interface for this could improve: do the free/decr here
             * instead? */
            item_crawler_evaluate(search, hv, i);

            if (hold_lock)
                item_trylock_unlock(hold_lock);
            pthread_mutex_unlock(&cache_lock);

            if (settings.lru_crawler_sleep)
                usleep(settings.lru_crawler_sleep);
        }
    }
    if (settings.verbose > 2)
        fprintf(stderr, "LRU crawler thread sleeping\n");
    STATS_LOCK();
    stats.lru_crawler_running = false;
    STATS_UNLOCK();
    }
    pthread_mutex_unlock(&lru_crawler_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "LRU crawler thread stopping\n");

    return NULL;
}

static pthread_t item_crawler_tid;

int stop_item_crawler_thread(void) {
    int ret;
    pthread_mutex_lock(&lru_crawler_lock);
    do_run_lru_crawler_thread = 0;
    pthread_cond_signal(&lru_crawler_cond);
    pthread_mutex_unlock(&lru_crawler_lock);
    if ((ret = pthread_join(item_crawler_tid, NULL)) != 0) {
        fprintf(stderr, "Failed to stop LRU crawler thread: %s\n", strerror(ret));
        return -1;
    }
    settings.lru_crawler = false;
    return 0;
}

int start_item_crawler_thread(void) {
    int ret;

    if (settings.lru_crawler)
        return -1;
    pthread_mutex_lock(&lru_crawler_lock);
    do_run_lru_crawler_thread = 1;
    settings.lru_crawler = true;
    if ((ret = pthread_create(&item_crawler_tid, NULL,
        item_crawler_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create LRU crawler thread: %s\n",
            strerror(ret));
        pthread_mutex_unlock(&lru_crawler_lock);
        return -1;
    }
    pthread_mutex_unlock(&lru_crawler_lock);

    return 0;
}

enum crawler_result_type lru_crawler_crawl(char *slabs) {
    char *b = NULL;
    uint32_t sid = 0;
    uint8_t tocrawl[POWER_LARGEST];
    if (pthread_mutex_trylock(&lru_crawler_lock) != 0) {
        return CRAWLER_RUNNING;
    }
    pthread_mutex_lock(&cache_lock);

    if (strcmp(slabs, "all") == 0) {
        for (sid = 0; sid < LARGEST_ID; sid++) {
            tocrawl[sid] = 1;
        }
    } else {
        for (char *p = strtok_r(slabs, ",", &b);
             p != NULL;
             p = strtok_r(NULL, ",", &b)) {

            if (!safe_strtoul(p, &sid) || sid < POWER_SMALLEST
                    || sid > POWER_LARGEST) {
                pthread_mutex_unlock(&cache_lock);
                pthread_mutex_unlock(&lru_crawler_lock);
                return CRAWLER_BADCLASS;
            }
            tocrawl[sid] = 1;
        }
    }

    for (sid = 0; sid < LARGEST_ID; sid++) {
        if (tocrawl[sid] != 0 && tails[sid] != NULL) {
            if (settings.verbose > 2)
                fprintf(stderr, "Kicking LRU crawler off for slab %d\n", sid);
            crawlers[sid].nbytes = 0;
            crawlers[sid].nkey = 0;
            crawlers[sid].it_flags = 1; /* For a crawler, this means enabled. */
            crawlers[sid].next = 0;
            crawlers[sid].prev = 0;
            crawlers[sid].time = 0;
            crawlers[sid].remaining = settings.lru_crawler_tocrawl;
            crawlers[sid].slabs_clsid = sid;
            crawler_link_q((item *)&crawlers[sid]);
            crawler_count++;
        }
    }
    pthread_mutex_unlock(&cache_lock);
    pthread_cond_signal(&lru_crawler_cond);
    STATS_LOCK();
    stats.lru_crawler_running = true;
    STATS_UNLOCK();
    pthread_mutex_unlock(&lru_crawler_lock);
    return CRAWLER_OK;
}

//主要是锁的初始化
int init_lru_crawler(void) {
    if (lru_crawler_initialized == 0) {
        if (pthread_cond_init(&lru_crawler_cond, NULL) != 0) {
            fprintf(stderr, "Can't initialize lru crawler condition\n");
            return -1;
        }
        pthread_mutex_init(&lru_crawler_lock, NULL);
        lru_crawler_initialized = 1;
    }
    return 0;
}
