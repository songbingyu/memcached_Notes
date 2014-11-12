/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Slabs memory allocation, based on powers-of-N. Slabs are up to 1MB in size
 * and are divided into chunks. The chunk sizes start off at the size of the
 * "item" structure plus space for a small key and value. They increase by
 * a multiplier factor from there, up to half the maximum slab size. The last
 * slab size is always 1MB, since that's the maximum item size allowed by the
 * memcached protocol.
 */
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
#include <assert.h>
#include <pthread.h>

/* powers-of-N allocation structures */

typedef struct {
    unsigned int size;      /* sizes of items */
    unsigned int perslab;   /* how many items per slab */

    void *slots;           /* list of item ptrs */
    unsigned int sl_curr;   /* total free items in list */

    unsigned int slabs;     /* how many slabs were allocated for this class */

    void **slab_list;       /* array of slab pointers */
    unsigned int list_size; /* size of prev array */

    unsigned int killing;  /* index+1 of dying slab, or zero if none */
    size_t requested; /* The number of requested bytes */
} slabclass_t;

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];
static size_t mem_limit = 0;
static size_t mem_malloced = 0;
static int power_largest;

static void *mem_base = NULL;
static void *mem_current = NULL;
static size_t mem_avail = 0;

/**
 * Access to the slab allocator is protected by this lock
 */
static pthread_mutex_t slabs_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t slabs_rebalance_lock = PTHREAD_MUTEX_INITIALIZER;

/*
 * Forward Declarations
 */
static int do_slabs_newslab(const unsigned int id);
static void *memory_allocate(size_t size);
static void do_slabs_free(void *ptr, const size_t size, unsigned int id);

/* Preallocate as many slab pages as possible (called from slabs_init)
   on start-up, so users don't get confused out-of-memory errors when
   they do have free (in-slab) space, but no space to make new slabs.
   if maxslabs is 18 (POWER_LARGEST - POWER_SMALLEST + 1), then all
   slab types can be made.  if max memory is less than 18 MB, only the
   smaller ones will be made.  */
static void slabs_preallocate (const unsigned int maxslabs);

/*
 * Figures out which slab class (chunk size) is required to store an item of
 * a given size.
 *
 * Given object size, return id to use when allocating/freeing memory for object
 * 0 means error: can't store such a large object
 */
// ����size ѡ����ʵ�slabclass
unsigned int slabs_clsid(const size_t size) {
    int res = POWER_SMALLEST;

    if (size == 0)
        return 0;
    while (size > slabclass[res].size)
        if (res++ == power_largest)     /* won't fit in the biggest slab */
            return 0;
    return res;
}

/**
 * Determines the chunk sizes and initializes the slab class descriptors
 * accordingly.
 */
// �ο� http://basiccoder.com/memcached-memory-mamagement.html
//http://www.cnblogs.com/moonlove/archive/2012/05/14/2509151.html
//http://blog.chinaunix.net/uid-26793016-id-3867739.html
void slabs_init(const size_t limit, const double factor, const bool prealloc) {

	//POWER_SMALLEST def 1
    int i = POWER_SMALLEST - 1;
	//chunk_size ����С����ռ䣬def 48
    unsigned int size = sizeof(item) + settings.chunk_size;

    mem_limit = limit;

	//�Ƿ�Ԥ�ȷ���
    if (prealloc) {
        /* Allocate everything in a big chunk with malloc */
        mem_base = malloc(mem_limit);
        if (mem_base != NULL) {
            mem_current = mem_base;
            mem_avail = mem_limit;
        } else {
            fprintf(stderr, "Warning: Failed to allocate requested memory in"
                    " one large chunk.\nWill allocate in smaller chunks\n");
        }
    }


	/*
										-------
		 ------------------- slab_list|	 slab1  | -------------->   *****************
		|	slab_class[1]	|-------->|	-------	|				   |   chunk1(used)	 |
		|-------------------|\		  |	 slab2	|				   |*****************|
		|	slab_class[2]   | \	      | ------- |				   |   chunk2(free)  |--------
		|-------------------|  \	  |	  ...	|				   |*****************|		  |
		|	slab_class[3]	|   \							       |   chunk3(used)	 |		  |
		|-------------------|    \      *********			       |*****************|		  |
		|   slab_class[4]	|	  --->|			 |				   |	........	 |		  |
		|-------------------|  slots[]| *********|											  |
		|	.............	|		  |	 chunk n |  <-----------------------------------------
									  | *********|	
									  |			 |

	*/


	//slab class ���� POWER_LARGEST + 1 POWER_LARGEST  200 
    memset(slabclass, 0, sizeof(slabclass));
	//slab class �� 1 ��ʼ CHUNK_ALIGN_BYTES = 8 8�ֽڶ���
    while (++i < POWER_LARGEST && size <= settings.item_size_max / factor) {
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES)
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);
		//settings.item_size_max def 1M  The famous 1MB upper limit. 
        slabclass[i].size = size;
        slabclass[i].perslab = settings.item_size_max / slabclass[i].size;
        size *= factor;
        if (settings.verbose > 1) {
            fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
                    i, slabclass[i].size, slabclass[i].perslab);
        }
    }

    power_largest = i;
    slabclass[power_largest].size = settings.item_size_max;
    slabclass[power_largest].perslab = 1;
    if (settings.verbose > 1) {
        fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
                i, slabclass[i].size, slabclass[i].perslab);
    }

	//TODO��
    /* for the test suite:  faking of how much we've already malloc'd */
    {
        char *t_initial_malloc = getenv("T_MEMD_INITIAL_MALLOC");
        if (t_initial_malloc) {
            mem_malloced = (size_t)atol(t_initial_malloc);
        }

    }
	//�Ƿ�Ԥ�ȷ���
    if (prealloc) {
        slabs_preallocate(power_largest);
    }
}

//Ԥ����
static void slabs_preallocate (const unsigned int maxslabs) {
    int i;
    unsigned int prealloc = 0;

    /* pre-allocate a 1MB slab in every size class so people don't get
       confused by non-intuitive "SERVER_ERROR out of memory" 
       messages.  this is the most common question on the mailing
       list.  if you really don't want this, you can rebuild without
       these three lines.  */
	//��ÿ��Ԥ�ȷ���1M
    for (i = POWER_SMALLEST; i <= POWER_LARGEST; i++) {
        if (++prealloc > maxslabs)
            return;
		//ʵ�ʷ������
        if (do_slabs_newslab(i) == 0) {
            fprintf(stderr, "Error while preallocating slab memory!\n"
                "If using -L or other prealloc options, max memory must be "
                "at least %d megabytes.\n", power_largest);
            exit(1);
        }
    }

}

//�ο� http://www.tuicool.com/articles/nY7fqy
static int grow_slab_list (const unsigned int id) {
    slabclass_t *p = &slabclass[id];
	//p->slabs:�Ѿ������slab����p->list_size: slab����ĳ���
    if (p->slabs == p->list_size) {
        size_t new_size =  (p->list_size != 0) ? p->list_size * 2 : 16;
        void *new_list = realloc(p->slab_list, new_size * sizeof(void *));
        if (new_list == 0) return 0;
        p->list_size = new_size;
        p->slab_list = new_list;
    }
    return 1;
}

//��һ��slab �ָ��  perslab �� size ��С��chunk �ŵ� freelist
static void split_slab_page_into_freelist(char *ptr, const unsigned int id) {
    slabclass_t *p = &slabclass[id];
    int x;
    for (x = 0; x < p->perslab; x++) {
        do_slabs_free(ptr, 0, id);
        ptr += p->size;
    }
}

//
static int do_slabs_newslab(const unsigned int id) {
    slabclass_t *p = &slabclass[id];
	//�Ƿ��ط���
    int len = settings.slab_reassign ? settings.item_size_max
        : p->size * p->perslab;
    char *ptr;

	//ע�������ǻ�Ĺ�ϵ������������ִ��
    if ((mem_limit && mem_malloced + len > mem_limit && p->slabs > 0) ||
        (grow_slab_list(id) == 0) ||
        ((ptr = memory_allocate((size_t)len)) == 0)) {

        MEMCACHED_SLABS_SLABCLASS_ALLOCATE_FAILED(id);
        return 0;
    }
	//���
    memset(ptr, 0, (size_t)len);

	//ȫ���ŵ�freelist
    split_slab_page_into_freelist(ptr, id);
	
	//���뵽slabclass �� slab list ����
    p->slab_list[p->slabs++] = ptr;
    mem_malloced += len;

	//trace 
    MEMCACHED_SLABS_SLABCLASS_ALLOCATE(id);

    return 1;
}

/*@null@*/
static void *do_slabs_alloc(const size_t size, unsigned int id) {
    slabclass_t *p;
    void *ret = NULL;
    item *it = NULL;
	//�߽���
    if (id < POWER_SMALLEST || id > power_largest) {
        MEMCACHED_SLABS_ALLOCATE_FAILED(size, 0);
        return NULL;
    }

    p = &slabclass[id];
    assert(p->sl_curr == 0 || ((item *)p->slots)->slabs_clsid == 0);

	//��������ȥ slots ����ȥ���䣬��������new slab 
    /* fail unless we have space at the end of a recently allocated page,
       we have something on our freelist, or we could allocate a new page */
    if (! (p->sl_curr != 0 || do_slabs_newslab(id) != 0)) {
        /* We don't have more memory available */
        ret = NULL;
    } else if (p->sl_curr != 0) {
        /* return off our freelist */
        it = (item *)p->slots;
        p->slots = it->next;
        if (it->next) it->next->prev = 0;
        p->sl_curr--;
        ret = (void *)it;
    }

	//����ͳ�Ʊ���
    if (ret) {
        p->requested += size;
        MEMCACHED_SLABS_ALLOCATE(size, id, p->size, ret);
    } else {
        MEMCACHED_SLABS_ALLOCATE_FAILED(size, id);
    }

    return ret;
}

static void do_slabs_free(void *ptr, const size_t size, unsigned int id) {
    slabclass_t *p;
    item *it;

	//�������ж�
    assert(((item *)ptr)->slabs_clsid == 0);
    assert(id >= POWER_SMALLEST && id <= power_largest);

    if (id < POWER_SMALLEST || id > power_largest)
        return;

	//�յģ�����ռλ
    MEMCACHED_SLABS_FREE(size, id, ptr);

    p = &slabclass[id];
	//ָ�����ذںܼ򵥣� ÿ�β�������ͷ��  p->slots �൱��ͷָ��
    it = (item *)ptr;
    it->it_flags |= ITEM_SLABBED;
    it->prev = 0;
    it->next = p->slots;
    if (it->next) it->next->prev = it;
    p->slots = it;
	//����ͳ�Ʊ���
    p->sl_curr++;
    p->requested -= size;
    return;
}

static int nz_strcmp(int nzlength, const char *nz, const char *z) {
    int zlength=strlen(z);
    return (zlength == nzlength) && (strncmp(nz, z, zlength) == 0) ? 0 : -1;
}

bool get_stats(const char *stat_type, int nkey, ADD_STAT add_stats, void *c) {
    bool ret = true;

    if (add_stats != NULL) {
        if (!stat_type) {
            /* prepare general statistics for the engine */
            STATS_LOCK();
            APPEND_STAT("bytes", "%llu", (unsigned long long)stats.curr_bytes);
            APPEND_STAT("curr_items", "%u", stats.curr_items);
            APPEND_STAT("total_items", "%u", stats.total_items);
            STATS_UNLOCK();
            item_stats_totals(add_stats, c);
        } else if (nz_strcmp(nkey, stat_type, "items") == 0) {
            item_stats(add_stats, c);
        } else if (nz_strcmp(nkey, stat_type, "slabs") == 0) {
            slabs_stats(add_stats, c);
        } else if (nz_strcmp(nkey, stat_type, "sizes") == 0) {
            item_stats_sizes(add_stats, c);
        } else {
            ret = false;
        }
    } else {
        ret = false;
    }

    return ret;
}

/*@null@*/
static void do_slabs_stats(ADD_STAT add_stats, void *c) {
    int i, total;
    /* Get the per-thread stats which contain some interesting aggregates */
    struct thread_stats thread_stats;
    threadlocal_stats_aggregate(&thread_stats);

    total = 0;
    for(i = POWER_SMALLEST; i <= power_largest; i++) {
        slabclass_t *p = &slabclass[i];
        if (p->slabs != 0) {
            uint32_t perslab, slabs;
            slabs = p->slabs;
            perslab = p->perslab;

            char key_str[STAT_KEY_LEN];
            char val_str[STAT_VAL_LEN];
            int klen = 0, vlen = 0;

            APPEND_NUM_STAT(i, "chunk_size", "%u", p->size);
            APPEND_NUM_STAT(i, "chunks_per_page", "%u", perslab);
            APPEND_NUM_STAT(i, "total_pages", "%u", slabs);
            APPEND_NUM_STAT(i, "total_chunks", "%u", slabs * perslab);
            APPEND_NUM_STAT(i, "used_chunks", "%u",
                            slabs*perslab - p->sl_curr);
            APPEND_NUM_STAT(i, "free_chunks", "%u", p->sl_curr);
            /* Stat is dead, but displaying zero instead of removing it. */
            APPEND_NUM_STAT(i, "free_chunks_end", "%u", 0);
            APPEND_NUM_STAT(i, "mem_requested", "%llu",
                            (unsigned long long)p->requested);
            APPEND_NUM_STAT(i, "get_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].get_hits);
            APPEND_NUM_STAT(i, "cmd_set", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].set_cmds);
            APPEND_NUM_STAT(i, "delete_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].delete_hits);
            APPEND_NUM_STAT(i, "incr_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].incr_hits);
            APPEND_NUM_STAT(i, "decr_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].decr_hits);
            APPEND_NUM_STAT(i, "cas_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].cas_hits);
            APPEND_NUM_STAT(i, "cas_badval", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].cas_badval);
            APPEND_NUM_STAT(i, "touch_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].touch_hits);
            total++;
        }
    }

    /* add overall slab stats and append terminator */

    APPEND_STAT("active_slabs", "%d", total);
    APPEND_STAT("total_malloced", "%llu", (unsigned long long)mem_malloced);
    add_stats(NULL, 0, NULL, 0, c);
}

//�����ڴ�
static void *memory_allocate(size_t size) {
    void *ret;

	//����
	/*
	
		------------------------------------------
	   |				mem_limit				  |
		------------------------------------------
	   ^					^
	   | --------used------	|------mem_avail------|
	   |					|
	   mem_base				mem_current

	*/

	//�Ƿ��Ѿ�Ԥ�ȷ���
    if (mem_base == NULL) {
        /* We are not using a preallocated large memory chunk */
        ret = malloc(size);
    } else {
        ret = mem_current;
		//ʣ�µĲ�����
        if (size > mem_avail) {
            return NULL;
        }
		//����
        /* mem_current pointer _must_ be aligned!!! */
        if (size % CHUNK_ALIGN_BYTES) {
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);
        }
		//�޸ĵ�ǰ �� size 
        mem_current = ((char*)mem_current) + size;
        if (size < mem_avail) {
            mem_avail -= size;
        } else {
            mem_avail = 0;
        }
    }

    return ret;
}

//����style
void *slabs_alloc(size_t size, unsigned int id) {
    void *ret;

    pthread_mutex_lock(&slabs_lock);
    ret = do_slabs_alloc(size, id);
    pthread_mutex_unlock(&slabs_lock);
    return ret;
}

//�ӻ�ȥ
void slabs_free(void *ptr, size_t size, unsigned int id) {
    pthread_mutex_lock(&slabs_lock);
    do_slabs_free(ptr, size, id);
    pthread_mutex_unlock(&slabs_lock);
}

void slabs_stats(ADD_STAT add_stats, void *c) {
    pthread_mutex_lock(&slabs_lock);
    do_slabs_stats(add_stats, c);
    pthread_mutex_unlock(&slabs_lock);
}

//�ı��������С
void slabs_adjust_mem_requested(unsigned int id, size_t old, size_t ntotal)
{
    pthread_mutex_lock(&slabs_lock);
    slabclass_t *p;
    if (id < POWER_SMALLEST || id > power_largest) {
        fprintf(stderr, "Internal error! Invalid slab class\n");
        abort();
    }

    p = &slabclass[id];
    p->requested = p->requested - old + ntotal;
    pthread_mutex_unlock(&slabs_lock);
}

static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t slab_rebalance_cond = PTHREAD_COND_INITIALIZER;
static volatile int do_run_slab_thread = 1;
static volatile int do_run_slab_rebalance_thread = 1;

#define DEFAULT_SLAB_BULK_CHECK 1
int slab_bulk_check = DEFAULT_SLAB_BULK_CHECK;

//��ֵ slab_rebalȫ�ֱ�������pageҳ����ֹλ�á�����λ�á�
//src slabclass id��dest slabclass id��ֵ��ȫ�ֱ��� slab_rebal�����ں��ڴ���
//�����dest slabclass��pageҳ�����Ƿ�ռ���㣬����ռ䲻������չ�ռ�Ϊԭ����������С��
static int slab_rebalance_start(void) {
    slabclass_t *s_cls;
    int no_go = 0;

    pthread_mutex_lock(&cache_lock);
    pthread_mutex_lock(&slabs_lock);

	//Խ���ж�
    if (slab_rebal.s_clsid < POWER_SMALLEST ||
        slab_rebal.s_clsid > power_largest  ||
        slab_rebal.d_clsid < POWER_SMALLEST ||
        slab_rebal.d_clsid > power_largest  ||
        slab_rebal.s_clsid == slab_rebal.d_clsid)
        no_go = -2;

	//src 
    s_cls = &slabclass[slab_rebal.s_clsid];
	//���dest��slabs�����Ѿ��ﵽ���������ݼ�¼slabs���ָ�������
    if (!grow_slab_list(slab_rebal.d_clsid)) {
        no_go = -1;
    }

    if (s_cls->slabs < 2)
        no_go = -3;

    if (no_go != 0) {
        pthread_mutex_unlock(&slabs_lock);
        pthread_mutex_unlock(&cache_lock);
        return no_go; /* Should use a wrapper function... */
    }

	//killing����ɾ������slabs
    s_cls->killing = 1;

    slab_rebal.slab_start = s_cls->slab_list[s_cls->killing - 1];
    slab_rebal.slab_end   = (char *)slab_rebal.slab_start +
        (s_cls->size * s_cls->perslab);
    slab_rebal.slab_pos   = slab_rebal.slab_start;
    slab_rebal.done       = 0;

    /* Also tells do_item_get to search for items in this slab */
    slab_rebalance_signal = 2;

    if (settings.verbose > 1) {
        fprintf(stderr, "Started a slab rebalance\n");
    }

    pthread_mutex_unlock(&slabs_lock);
    pthread_mutex_unlock(&cache_lock);

    STATS_LOCK();
    stats.slab_reassign_running = true;
    STATS_UNLOCK();

    return 0;
}

enum move_status {
    MOVE_PASS=0, MOVE_DONE, MOVE_BUSY, MOVE_LOCKED
};

/* refcount == 0 is safe since nobody can incr while cache_lock is held.
 * refcount != 0 is impossible since flags/etc can be modified in other
 * threads. instead, note we found a busy one and bail. logic in do_item_get
 * will prevent busy items from continuing to be busy
 */
//��ʼ move
static int slab_rebalance_move(void) {
    slabclass_t *s_cls;
    int x;
    int was_busy = 0;
    int refcount = 0;
    enum move_status status = MOVE_PASS;

    pthread_mutex_lock(&cache_lock);
    pthread_mutex_lock(&slabs_lock);

    s_cls = &slabclass[slab_rebal.s_clsid];

	//slab_bulk_check=1������ÿ��1��item��ɾ����������ΪΪ�˿���ӵ������ʱ��
    for (x = 0; x < slab_bulk_check; x++) {
        item *it = slab_rebal.slab_pos;//��õ�ǰ�Ǹ�slab��item��ÿ��������һ����ֱ������slab_end 
        status = MOVE_PASS;
        if (it->slabs_clsid != 255) {
            void *hold_lock = NULL;
            uint32_t hv = hash(ITEM_key(it), it->nkey);
            if ((hold_lock = item_trylock(hv)) == NULL) {
                status = MOVE_LOCKED;
            } else {
                refcount = refcount_incr(&it->refcount);
                if (refcount == 1) { /* item is unlinked, unused */
                    if (it->it_flags & ITEM_SLABBED) {
						//��freelist ���� 
                        /* remove from slab freelist */
                        if (s_cls->slots == it) {
                            s_cls->slots = it->next;
                        }
                        if (it->next) it->next->prev = it->prev;
                        if (it->prev) it->prev->next = it->next;
                        s_cls->sl_curr--;
                        status = MOVE_DONE;
                    } else {
                        status = MOVE_BUSY;
                    }
                } else if (refcount == 2) { /* item is linked but not busy */
                    if ((it->it_flags & ITEM_LINKED) != 0) {
                        do_item_unlink_nolock(it, hv);
                        status = MOVE_DONE;
                    } else {
                        /* refcount == 1 + !ITEM_LINKED means the item is being
                         * uploaded to, or was just unlinked but hasn't been freed
                         * yet. Let it bleed off on its own and try again later */
                        status = MOVE_BUSY;
                    }
                } else {
                    if (settings.verbose > 2) {
                        fprintf(stderr, "Slab reassign hit a busy item: refcount: %d (%d -> %d)\n",
                            it->refcount, slab_rebal.s_clsid, slab_rebal.d_clsid);
                    }
                    status = MOVE_BUSY;
                }
                item_trylock_unlock(hold_lock);
            }
        }

        switch (status) {
            case MOVE_DONE:
                it->refcount = 0;
                it->it_flags = 0;
                it->slabs_clsid = 255;
                break;
            case MOVE_BUSY:
                refcount_decr(&it->refcount);
            case MOVE_LOCKED:
                slab_rebal.busy_items++;
                was_busy++;
                break;
            case MOVE_PASS:
                break;
        }

        slab_rebal.slab_pos = (char *)slab_rebal.slab_pos + s_cls->size;
        if (slab_rebal.slab_pos >= slab_rebal.slab_end)
            break;
    }

    if (slab_rebal.slab_pos >= slab_rebal.slab_end) {
        /* Some items were busy, start again from the top */
        if (slab_rebal.busy_items) {
			//oh��mygod ��ֻ�����Ǵ�ͷ��������
            slab_rebal.slab_pos = slab_rebal.slab_start;
            slab_rebal.busy_items = 0;
        } else {
            slab_rebal.done++;
        }
    }

    pthread_mutex_unlock(&slabs_lock);
    pthread_mutex_unlock(&cache_lock);

    return was_busy;
}
//Ǩ����ɣ���ʼɨ�⹤��
static void slab_rebalance_finish(void) {
    slabclass_t *s_cls;
    slabclass_t *d_cls;

    pthread_mutex_lock(&cache_lock);
    pthread_mutex_lock(&slabs_lock);

    s_cls = &slabclass[slab_rebal.s_clsid];	//src 
    d_cls   = &slabclass[slab_rebal.d_clsid]; //dst

    /* At this point the stolen slab is completely clear */
	//����ɾ���˵�һ��slab�Ŀռ䣬����slab_list��һ��
	//ָ��ָ��ĺ���ԭ����ɾ�����Ǹ��ռ��ַ����Ҫ�ѵ�ǰ����slabs��
	//�׵�ַ���Ǹ���һ��ָ�룬ʹ����ָ���������Ŀռ�
    s_cls->slab_list[s_cls->killing - 1] =
        s_cls->slab_list[s_cls->slabs - 1];
    s_cls->slabs--;
    s_cls->killing = 0;

    memset(slab_rebal.slab_start, 0, (size_t)settings.item_size_max);

    d_cls->slab_list[d_cls->slabs++] = slab_rebal.slab_start;
	//�ŵ�freelist ����
    split_slab_page_into_freelist(slab_rebal.slab_start,
        slab_rebal.d_clsid);

	// clear
    slab_rebal.done       = 0;
    slab_rebal.s_clsid    = 0;
    slab_rebal.d_clsid    = 0;
    slab_rebal.slab_start = NULL;
    slab_rebal.slab_end   = NULL;
    slab_rebal.slab_pos   = NULL;

    slab_rebalance_signal = 0;

    pthread_mutex_unlock(&slabs_lock);
    pthread_mutex_unlock(&cache_lock);

    STATS_LOCK();
    stats.slab_reassign_running = false;
    stats.slabs_moved++;
    STATS_UNLOCK();

    if (settings.verbose > 1) {
        fprintf(stderr, "finished a slab move\n");
    }
}

/* Return 1 means a decision was reached.
 * Move to its own thread (created/destroyed as needed) once automover is more
 * complex.
 */
/*
	1.��ȡû��slabclass ����LRU�Ĵ�����itemstats[id].evicted����
	2.�ҳ�һ�������3�Σ�10����һ�Σ�����LRU����û�����ӵġ�pageҳ��3ҳ���ϵ�class��Ϊsrc slabclass��
	3.������μ���У�LRU������������slabclassΪ�������3�ζ���LRU��������slabclass����ѡȡ��ǰclassΪdest slabclass��
	4.�� src slabclass �� dest slabclass ��ѡ��ʱ��ͨ��pthread_cond_signal���� 
	  slab_rebalance_thread�߳̽���slabת�ƣ����������ѯ��飨10����һ�Σ���

	src��ѡ�����������slab-class�����������3�η���ʧ�ܴ���û�б仯��
	�Ϳ�����Ϊ���slab-class��������ȶ��ģ���ô���ڴ���ŵ�����£�
	������slab-class���ڿռ���������ʧ�ܣ�����ͨ������һ�����ȶ���slab-class�ռ䣬
	�����·�����ռ䲻���õ�slab-class��dest��ѡ��������ÿ��ͨ��ѡ������ѡ����ķ������ʧ��
	����slab-class���������3�ζ������class����ô��ѡ�����������dest

*/
static int slab_automove_decision(int *src, int *dst) {
    //static�ĳ�Ա��������¼�ϴεķ���ʧ��ͳ����Ϣ��һ��slab-classһ��Ԫ��
	static uint64_t evicted_old[POWER_LARGEST];
	//��¼ÿ��slab-class,����ʧ�ܴ������仯�Ĵ���
    static unsigned int slab_zeroes[POWER_LARGEST];
	// ��ʾ�ĸ�slab-classӦ�����Ǹ�dst
    static unsigned int slab_winner = 0;
    static unsigned int slab_wins   = 0;//ѡ�ٳɹ��Ĵ���
    uint64_t evicted_new[POWER_LARGEST];//�µ�slab����ʧ��ͳ����Ϣ
    uint64_t evicted_diff = 0;//��¼ÿ��slab�µ�ͳ����Ϣ�;ɵ�ͳ����Ϣ�Ĳ�
	uint64_t evicted_max = 0; // ��¼����ʧ�ܴ��������ֵ
    unsigned int highest_slab = 0;//��¼������������Ǹ�slab-class id
    unsigned int total_pages[POWER_LARGEST];
    int i;
    int source = 0;
    int dest = 0;
    static rel_time_t next_run;

    /* Run less frequently than the slabmove tester. */
	//10s ����һ��
    if (current_time >= next_run) {
        next_run = current_time + 10;
    } else {
        return 0;
    }

    item_stats_evictions(evicted_new);//���µ�ÿ��slab����ʧ�ܵ�ͳ����Ϣ���� evicted_new
	pthread_mutex_lock(&cache_lock); //�õ�����slab�������
    //ÿ��slabclass slab ����
	for (i = POWER_SMALLEST; i < power_largest; i++) {
        total_pages[i] = slabclass[i].slabs;
    }
    pthread_mutex_unlock(&cache_lock);

    /* Find a candidate source; something with zero evicts 3+ times */
    for (i = POWER_SMALLEST; i < power_largest; i++) {//�Ƚ�ÿ��slab-class�ķ���ʧ��ͳ����Ϣ
		evicted_diff = evicted_new[i] - evicted_old[i]; //������ʧ��ͳ����Ϣ���ϴ�ʧ�ܵĲ�
		if (evicted_diff == 0 && total_pages[i] > 2) {//������ϴη���ʧ�ܵĴ���û�б仯������slab�ĸ�����������
            slab_zeroes[i]++;
			//����ҵ��ĵ�һ��slab-class���㲢������3��û�б仯��ô���slab-class id 
			//�����Ǹ�src���ȴ����slab�г���ռ��������slab���·���
            if (source == 0 && slab_zeroes[i] >= 3)
                source = i;
        } else {
			slab_zeroes[i] = 0;  //ֻҪ��һ���б仯���Ǹ��ޱ仯�ļ�����������
            if (evicted_diff > evicted_max) { //ѡ����仯�����Ǹ�slab-class id
                evicted_max = evicted_diff;
                highest_slab = i;
            }
        }
        evicted_old[i] = evicted_new[i];
    }

    /* Pick a valid destination */
    if (slab_winner != 0 && slab_winner == highest_slab) {//dest��ѡ��Ҫ����������3��
        slab_wins++;
        if (slab_wins >= 3)
            dest = slab_winner;
    } else {//�����һ�β�����ô���slab_wins�ͱ�Ϊ1�����¿�ʼ
        slab_wins = 1;
        slab_winner = highest_slab;
    }

    if (source && dest) {
        *src = source;
        *dst = dest;
        return 1;
    }
    return 0;
}

/* Slab rebalancer thread.
 * Does not use spinlocks since it is not timing sensitive. Burn less CPU and
 * go to sleep if locks are contended
 */
//�߳�ΪSLAB���߳�
static void *slab_maintenance_thread(void *arg) {
    int src, dest;

    while (do_run_slab_thread) {
        if (settings.slab_automove == 1) {
			//�Զ�Ѱ�ҷ�����������Ҫ����pageҳת�Ƶ�����slabclass id��src��dest
            if (slab_automove_decision(&src, &dest) == 1) {
                /* Blind to the return codes. It will retry on its own */
                slabs_reassign(src, dest);
            }
            sleep(1);
        } else {
            /* Don't wake as often if we're not enabled.
             * This is lazier than setting up a condition right now. */
            sleep(5);
        }
    }
    return NULL;
}

/* Slab mover thread.
 * Sits waiting for a condition to jump off and shovel some memory about
 */
//slab_rebalance_thread�߳�ΪSLABҳ�ƶ��̡߳���src 
//slabclass�еĵ�һҳ�ƶ���dest slabclass�У�Ϊ���һҳ���������£�

//1.slab_rebalance_start����ֵ slab_rebalȫ�ֱ�����
//	��pageҳ����ֹλ�á�����λ�á�src slabclass id��dest slabclass id
//	��ֵ��ȫ�ֱ��� slab_rebal�����ں��ڴ���
//	�����dest slabclass��pageҳ�����Ƿ�ռ���㣬����ռ䲻������չ�ռ�Ϊԭ����������С��

//2.slab_rebalance_move���� slab_rebalָ��� pageҳ��
//	chunk�洢������item��hashtable��ɾ�����������ԭslabclass��head��
//	tail������ɾ�������ӻ���������ɾ����

//3.slab_rebalance_finish������slab_rebalȫ�ֱ�����
//	����ʼ��pageΪ0������page�ֳ�chunk��ӵ�dest slabclass��slots�����С�

static void *slab_rebalance_thread(void *arg) {
    int was_busy = 0;
    /* So we first pass into cond_wait with the mutex held */
    mutex_lock(&slabs_rebalance_lock);

    while (do_run_slab_rebalance_thread) {
        if (slab_rebalance_signal == 1) {
            if (slab_rebalance_start() < 0) {
                /* Handle errors with more specifity as required. */
                slab_rebalance_signal = 0;
            }

            was_busy = 0;
        } else if (slab_rebalance_signal && slab_rebal.slab_start != NULL) {
            was_busy = slab_rebalance_move();
        }

        if (slab_rebal.done) {
            slab_rebalance_finish();
        } else if (was_busy) {
            /* Stuck waiting for some items to unlock, so slow down a bit
             * to give them a chance to free up */
            usleep(50);
        }

        if (slab_rebalance_signal == 0) {
            /* always hold this lock while we're running */
            pthread_cond_wait(&slab_rebalance_cond, &slabs_rebalance_lock);
        }
    }
    return NULL;
}

/* Iterate at most once through the slab classes and pick a "random" source.
 * I like this better than calling rand() since rand() is slow enough that we
 * can just check all of the classes once instead.
 */
//���������һ��
//���ڴ治�㣬�޷������µ�itemʱ������LRU�󣬽���slabҳת�ƣ�ת�Ƶ���ǰҳ��
//src slabclassѡȡ����Ϊ���ѡȡ��ѡȡ�������£�
//1. ��һ��LRUʱ����slabclass1��ʼ�����ң����ҷ�ΧΪ����ҳ�����ϰ벿�֣�
//	 һ����2��slab page���ϵ�slabclass��Ϊsrc slabclass��
//2. �ڶ��η���LRU�󣬻����һ��ѡȡ��class֮����в���
//	�����ҷ�ΧΪ��ǰclass�����slabclass�������ϰ벿�֣����ʵ�class����Ϊsrc slabclass��

static int slabs_reassign_pick_any(int dst) {
    static int cur = POWER_SMALLEST - 1;
    int tries = power_largest - POWER_SMALLEST + 1;
    for (; tries > 0; tries--) {
        cur++;
        if (cur > power_largest)
            cur = POWER_SMALLEST;
        if (cur == dst)
            continue;
        if (slabclass[cur].slabs > 1) {
            return cur;
        }
    }
    return -1;
}

//����ģʽ
static enum reassign_result_type do_slabs_reassign(int src, int dst) {
    if (slab_rebalance_signal != 0)
        return REASSIGN_RUNNING;

    if (src == dst)
        return REASSIGN_SRC_DST_SAME;

    /* Special indicator to choose ourselves. */
    if (src == -1) {
        src = slabs_reassign_pick_any(dst);
        /* TODO: If we end up back at -1, return a new error type */
    }
	//bad ����
    if (src < POWER_SMALLEST || src > power_largest ||
        dst < POWER_SMALLEST || dst > power_largest)
        return REASSIGN_BADCLASS;

    if (slabclass[src].slabs < 2)
        return REASSIGN_NOSPARE;
	///��slab_rebal��ֵ
    slab_rebal.s_clsid = src;
    slab_rebal.d_clsid = dst;

    slab_rebalance_signal = 1;
	//ͨ���ź���ʹ��rebalance�߳̿�ʼ����
    pthread_cond_signal(&slab_rebalance_cond);

    return REASSIGN_OK;
}

enum reassign_result_type slabs_reassign(int src, int dst) {
    enum reassign_result_type ret;
    if (pthread_mutex_trylock(&slabs_rebalance_lock) != 0) {
        return REASSIGN_RUNNING;
    }
    ret = do_slabs_reassign(src, dst);
    pthread_mutex_unlock(&slabs_rebalance_lock);
    return ret;
}

//��ͣ
/* If we hold this lock, rebalancer can't wake up or move */
void slabs_rebalancer_pause(void) {
    pthread_mutex_lock(&slabs_rebalance_lock);
}

//�ָ�
void slabs_rebalancer_resume(void) {
    pthread_mutex_unlock(&slabs_rebalance_lock);
}

static pthread_t maintenance_tid;
static pthread_t rebalance_tid;

//slab move�߳�
int start_slab_maintenance_thread(void) {
    int ret;
    slab_rebalance_signal = 0;
    slab_rebal.slab_start = NULL;
    char *env = getenv("MEMCACHED_SLAB_BULK_CHECK");
    if (env != NULL) {
        slab_bulk_check = atoi(env);
        if (slab_bulk_check == 0) {
            slab_bulk_check = DEFAULT_SLAB_BULK_CHECK;
        }
    }

    if (pthread_cond_init(&slab_rebalance_cond, NULL) != 0) {
        fprintf(stderr, "Can't intiialize rebalance condition\n");
        return -1;
    }
    pthread_mutex_init(&slabs_rebalance_lock, NULL);

    if ((ret = pthread_create(&maintenance_tid, NULL,
                              slab_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create slab maint thread: %s\n", strerror(ret));
        return -1;
    }
    if ((ret = pthread_create(&rebalance_tid, NULL,
                              slab_rebalance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create rebal thread: %s\n", strerror(ret));
        return -1;
    }
    return 0;
}

void stop_slab_maintenance_thread(void) {
    mutex_lock(&cache_lock);
    do_run_slab_thread = 0;
    do_run_slab_rebalance_thread = 0;
    pthread_cond_signal(&maintenance_cond);
    pthread_mutex_unlock(&cache_lock);

    /* Wait for the maintenance thread to stop */
    pthread_join(maintenance_tid, NULL);
    pthread_join(rebalance_tid, NULL);
}
