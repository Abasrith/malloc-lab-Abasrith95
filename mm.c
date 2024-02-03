/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * Description as follows:-
 * 1. Implemented coalescing for 4 cases
 * 2a. Implemented explicit lists for free memory blocks
 * 2b. Impemented multiple doubly linked explicit lists for free memory blocks
 *      There are 13 free memory buckets currently implemented
 * 2c. Implemented singly linked explicit lists for block sizes of 16 bytes,
 * giving us a total of 14 freelists
 * 3.   Implemented first fit, goodfit and best fit functions for utilisation
 * and throughput optimisations
 * 4. Allocated blocks do not have footers and mini blocks of 16 bytes with no
 * footers for both allocated and free block has been implemented. The free
 * block does not have previous free block pointer, only employs a next free
 * block pointer.
 *
 * 4. Extensive heap check functionality with following features
 *    1.Memory alignment
 *    2.Checking header and footer match
 *    3.Checking if explicit lists count matches the implicit list free blocks
 *    4.Checking if implicit list contains adjacent free blocks
 *    5.Printing heap and free lists
 *    6.Heap size check
 *    7.Checking if address lies within the heap region
 *    8.Checking if the heap header and footer are correct
 *    9.Checking if explicit list member sizes fall within the list bucket size
 *    10.Checking if explicit list address fall withing heap boundaries
 *    11.Checking if next address and previous address of consecutive explicit
 * list members matches each other
 *
 * MALLOC - Allocates memory for an input size, this function checks a match in
 * the explicit free lists if no match is found extends the heap by max of
 * chunksize or input size
 *
 * FREE -  Deallocates memory corresponding to a previously allocated pointer
 *
 * REALLOC - If new size > old size just copy old size till end
 * if new Size < old Size, need to truncate and allocate to free list
 * provided the size if bigger than minimum size
 *
 * CALLOC - Performs malloc operation then all blocks initialised to zero.
 *
 * @author Abhishek Basrithaya <abasrith@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Free list count */
#define Total_Free_Lists 15
/* Fit scheme macros */
#define FIRST_FIT 0
#define BEST_FIT 1
#define GOOD_FIT 2

#define OFFSET_TO_SBRK 8
#define GOOD_Fit_MAX_COUNT 4

/* HEAP CHECK FUNCTIONS */
#define TRUE_FLAG 1
#define FALSE_FLAG 0

#define CHECK_EXPLICIT_IMPLICIT_MATCH FALSE_FLAG
#define PRINT_IMPLICIT_HEAP_EXPLICT_FREELISTS FALSE_FLAG
#define CHECK_ADJACENT_FREE_BLOCKS FALSE_FLAG
#define CHECK_HEADER_FOOTER_VAL FALSE_FLAG
#define CHECK_MEM_ALIGNMENT FALSE_FLAG
#define CHECK_MEM_HEAP_SIZE FALSE_FLAG
#define CHECK_MEM_REGION FALSE_FLAG
#define CHECK_MEM_HEAP_START_END FALSE_FLAG
#define CHECK_EXPLICIT_LIST_SIZE FALSE_FLAG
#define CHECK_EXPLICIT_LIST_ADDRESS_BOUNDARY FALSE_FLAG
#define CHECK_EXPLICIT_PREV_NEXT_ADDRESS FALSE_FLAG

/* Scheme 1*/
/*Maximum size limit of each list */
#define LIST0_LIMIT 16
#define LIST1_LIMIT 32
#define LIST2_LIMIT 64
#define LIST3_LIMIT 128
#define LIST4_LIMIT 256
#define LIST5_LIMIT 512
#define LIST6_LIMIT 1024
#define LIST7_LIMIT 2048
#define LIST8_LIMIT 4096
#define LIST9_LIMIT 8192
#define LIST10_LIMIT 16384
#define LIST11_LIMIT 32768
#define LIST12_LIMIT 65536
#define LIST13_LIMIT 131072

/*list offsets */
#define LIST0_INDEX 0
#define LIST1_INDEX 1
#define LIST2_INDEX 2
#define LIST3_INDEX 3
#define LIST4_INDEX 4
#define LIST5_INDEX 5
#define LIST6_INDEX 6
#define LIST7_INDEX 7
#define LIST8_INDEX 8
#define LIST9_INDEX 9
#define LIST10_INDEX 10
#define LIST11_INDEX 11
#define LIST12_INDEX 12
#define LIST13_INDEX 13
#define LIST14_INDEX 14

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * Chunksize is the size of the heap that is requested
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);
// static const size_t chunksize = 6144;

/**
 * Mask to check the allocation status
 */
static const word_t alloc_mask = 0x1;
/**
 * Mask to check the previous allocation status
 */
static const word_t prev_alloc_mask = 0x2;
/**
 * Mask to check if mini block
 */
static const word_t mini_block_mask = 0x4;
/**
 * Mask to check the size of the block
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    union {
        struct {
            void *nextPtr;
            void *prevPtr;
        };
        void *nextMini;
        char payload[0]; /* Pointer to the start of the payload */
    };
} block_t;

/* Function Prototyping */
static bool alignedAddressCheck(const void *p);
static block_t *find_fit(size_t asize, size_t fitScheme);
static inline block_t *searchList(size_t freeListHeadIndex, size_t asize,
                                  size_t fitScheme);
static block_t *find_first_fit(block_t *freeListHead, size_t asize);
static block_t *find_good_fit(block_t *freeListHead, size_t asize);
static block_t *find_best_fit(block_t *freeListHead, size_t asize);

/* Global variables */

/** @brief Pointer to first block in the heap and free list */
static block_t *heap_start = NULL;
/* Free list head pointers */
static block_t *heap_freeList[Total_Free_Lists];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size`, `prev_alloc` and `alloc` of a block into a word
 * suitable for use as a packed value.
 *
 * Packed values are used for both headers/footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] prev_mini True if the previous block is mini block
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool prev_mini, bool prev_alloc, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev_alloc) {
        word |= prev_alloc_mask;
    }
    if (prev_mini) {
        word |= mini_block_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    /* Move by block size starting from payload and go back by 2 word lengths */
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the previous block allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The previous block allocation status corresponding to the word
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)(word & prev_alloc_mask);
}
/**
 * @brief Returns the previous block allocation status, based on current block
 * header.
 * @param[in] block
 * @return The previous block allocation status.
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}
/**
 * @brief Returns the previous block is a mini block from a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The previous block is a mini block or not from the corresponding word
 */
static bool extract_prev_mini(word_t word) {
    return (bool)(word & mini_block_mask);
}
/**
 * @brief Returns an indicator if the previous block is a mini block, based on
 * current block header.
 * @param[in] block
 * @return The mini block status.
 */
static bool get_prev_mini(block_t *block) {
    return extract_prev_mini(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated, the previous
 * block as unallocated and not a mini block.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    // when heap extends previous block is always unallocated
    block->header = pack(0, false, false, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer(if free block), where the
 * location of the footer is computed in relation to the header.
 *
 * @pre Block!= NULL, size > 0
 * @post Header and footer(if free block) values match and allocation statuses
 * for both match "alloc" and previous allocation status already written to the
 * block
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_current_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    bool prev_alloc = false;
    bool prev_mini = false;
    bool miniBlock = false;
    if (size <= min_block_size) {
        miniBlock = true;
    }
    /* Write to the current header */
    prev_alloc = get_prev_alloc(block);
    prev_mini = get_prev_mini(block);
    block->header = pack(size, prev_mini, prev_alloc, alloc);

    /* If free block write to the footer as well and size is greater than 16 */
    if (!alloc && !miniBlock) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, prev_mini, prev_alloc, alloc);
    }
}

/**
 * @brief Writes to the next block to the given the current address.
 *
 * This function writes both a header and footer(if free block), where the
 * location of the footer is computed in relation to the header.
 *
 * @pre Block!= NULL, size > 0
 * @post Header and footer values match and allocation status for both match
 * current allocation status, newly written "prev_mini" and "prev_alloc"
 *
 * @param[out] block The location to begin writing the block header
 */
static void write_next_block(block_t *block) {
    dbg_requires(block != NULL);

    block_t *nextBlock = NULL;

    bool curr_alloc = false;
    bool prev_mini = false;
    bool prev_alloc = false;
    size_t blocksize = size_mask & (block->header);

    /* Write to the next block header and even footer if next block isnt
     * allocated */
    nextBlock = (block_t *)((char *)block + blocksize);
    size_t nextBlockSize = size_mask & (nextBlock->header);
    curr_alloc = get_alloc(nextBlock);
    if (blocksize <= min_block_size)
        prev_mini = true;
    prev_alloc = get_alloc(block);

    nextBlock->header = pack(nextBlockSize, prev_mini, prev_alloc, curr_alloc);
    if (!curr_alloc && !(nextBlockSize <= min_block_size)) {
        *(header_to_footer(nextBlock)) =
            pack(nextBlockSize, prev_mini, prev_alloc, curr_alloc);
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }
    return footer_to_header(footerp);
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_mini_header(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 2;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev_mini(block_t *block) {
    dbg_requires(block != NULL);
    word_t *headerp = find_prev_mini_header(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*headerp) == 0) {
        return NULL;
    }
    return (block_t *)headerp;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/
/**
 * @brief    Search the list for match, based on the scheme defined in the
 * parameter
 *
 *
 * @param[in]   freeListHeadIndex           Index to the free list head
 * @param[in]   asize                       size to be allocated from the free
 * lists blocks
 * @return      block_t*                    free block with matching fit
 */

static inline block_t *searchList(size_t freeListHeadIndex, size_t asize,
                                  size_t fitScheme) {
    block_t *fitBlock = NULL;
    if (freeListHeadIndex == LIST0_INDEX) {
        if (heap_freeList[LIST0_INDEX] != NULL)
            fitBlock = heap_freeList[freeListHeadIndex];
    } else {
        switch (fitScheme) {
        case FIRST_FIT:
            fitBlock = find_first_fit(heap_freeList[freeListHeadIndex], asize);
            break;
        case BEST_FIT:
            fitBlock = find_best_fit(heap_freeList[freeListHeadIndex], asize);
            break;
        case GOOD_FIT:
            fitBlock = find_good_fit(heap_freeList[freeListHeadIndex], asize);
            break;
        default:
            printf("Scheme chosen is not supported\n");
            break;
        }
    }
    return fitBlock;
}
/**
 * @brief    Finds fit in the free block lists based on the size requirment and
 * search scheme
 *
 *
 * @param[in]   asize           size to be allocated from the free lists blocks
 * @return      block_t*        free block with matching fit
 */

static block_t *find_fit(size_t asize, size_t fitScheme) {
    dbg_requires(asize > 0);
    block_t *block = NULL;
    size_t listIndex = 0;

    /* Segregated lists */
    if (asize <= LIST0_LIMIT) {
        for (listIndex = LIST0_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST1_LIMIT) {
        for (listIndex = LIST1_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST2_LIMIT) {
        for (listIndex = LIST2_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST3_LIMIT) {
        for (listIndex = LIST3_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST4_LIMIT) {
        for (listIndex = LIST4_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST5_LIMIT) {
        for (listIndex = LIST5_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST6_LIMIT) {
        for (listIndex = LIST6_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST7_LIMIT) {
        for (listIndex = LIST7_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST8_LIMIT) {
        for (listIndex = LIST8_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST9_LIMIT) {
        for (listIndex = LIST9_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST10_LIMIT) {
        for (listIndex = LIST10_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST11_LIMIT) {
        for (listIndex = LIST11_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST12_LIMIT) {
        for (listIndex = LIST12_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else if (asize <= LIST13_LIMIT) {
        for (listIndex = LIST13_INDEX; listIndex < Total_Free_Lists;
             listIndex++) {
            if ((block = searchList(listIndex, asize, fitScheme)) != NULL)
                return block;
        }
    } else {
        if ((block = searchList(LIST14_INDEX, asize, fitScheme)) != NULL)
            return block;
    }

    return block;
}
/**
 * @brief           Adds a block to the head of an appropriate explicit free
 * list.
 *
 *
 * @param[in]   block   A block in the heap
 * @return      void
 */
static void addToFreeList(block_t *block) {
    block_t *listHead = NULL;
    block_t **listHeadAddr = NULL;
    size_t size = get_size(block);
    bool miniBlockFlag = false;
    if (size <= min_block_size)
        miniBlockFlag = true;

    if (size <= LIST0_LIMIT) {
        listHead = heap_freeList[LIST0_INDEX];
        listHeadAddr = &heap_freeList[LIST0_INDEX];
    } else if (size <= LIST1_LIMIT) {
        listHead = heap_freeList[LIST1_INDEX];
        listHeadAddr = &heap_freeList[LIST1_INDEX];
    } else if (size <= LIST2_LIMIT) {
        listHead = heap_freeList[LIST2_INDEX];
        listHeadAddr = &heap_freeList[LIST2_INDEX];
    } else if (size <= LIST3_LIMIT) {
        listHead = heap_freeList[LIST3_INDEX];
        listHeadAddr = &heap_freeList[LIST3_INDEX];
    } else if (size <= LIST4_LIMIT) {
        listHead = heap_freeList[LIST4_INDEX];
        listHeadAddr = &heap_freeList[LIST4_INDEX];
    } else if (size <= LIST5_LIMIT) {
        listHead = heap_freeList[LIST5_INDEX];
        listHeadAddr = &heap_freeList[LIST5_INDEX];
    } else if (size <= LIST6_LIMIT) {
        listHead = heap_freeList[LIST6_INDEX];
        listHeadAddr = &heap_freeList[LIST6_INDEX];
    } else if (size <= LIST7_LIMIT) {
        listHead = heap_freeList[LIST7_INDEX];
        listHeadAddr = &heap_freeList[LIST7_INDEX];
    } else if (size <= LIST8_LIMIT) {
        listHead = heap_freeList[LIST8_INDEX];
        listHeadAddr = &heap_freeList[LIST8_INDEX];
    } else if (size <= LIST9_LIMIT) {
        listHead = heap_freeList[LIST9_INDEX];
        listHeadAddr = &heap_freeList[LIST9_INDEX];
    } else if (size <= LIST10_LIMIT) {
        listHead = heap_freeList[LIST10_INDEX];
        listHeadAddr = &heap_freeList[LIST10_INDEX];
    } else if (size <= LIST11_LIMIT) {
        listHead = heap_freeList[LIST11_INDEX];
        listHeadAddr = &heap_freeList[LIST11_INDEX];
    } else if (size <= LIST12_LIMIT) {
        listHead = heap_freeList[LIST12_INDEX];
        listHeadAddr = &heap_freeList[LIST12_INDEX];
    } else if (size <= LIST13_LIMIT) {
        listHead = heap_freeList[LIST13_INDEX];
        listHeadAddr = &heap_freeList[LIST13_INDEX];
    } else {
        listHead = heap_freeList[LIST14_INDEX];
        listHeadAddr = &heap_freeList[LIST14_INDEX];
    }

    if (listHead == NULL) {
        *listHeadAddr = block;
        if (!miniBlockFlag)
            block->nextPtr = NULL;
        else
            block->nextMini = NULL;

        if (!miniBlockFlag)
            block->prevPtr = NULL;

    } else {
        *listHeadAddr = block;
        if (!miniBlockFlag)
            block->prevPtr = NULL;

        if (!miniBlockFlag)
            block->nextPtr = listHead;
        else
            block->nextMini = listHead;

        if (!miniBlockFlag)
            listHead->prevPtr = block;
    }
}

/**
 * @brief           Removes a block from the appropraite free list.
 *
 *
 * @param[in]   block   A block in the heap
 * @return      void
 */
static void removeFromFreeList(block_t *block) {
    size_t size = get_size(block);
    bool miniBlockFlag = false;
    block_t *findPrev = NULL;
    if (size <= min_block_size)
        miniBlockFlag = true;

    block_t *nextFreeBlock = NULL;
    if (!miniBlockFlag)
        nextFreeBlock = block->nextPtr;
    else
        nextFreeBlock = block->nextMini;

    block_t *prevFreeBlock = NULL;
    if (!miniBlockFlag)
        prevFreeBlock = block->prevPtr;
    else {
        findPrev = heap_freeList[LIST0_INDEX];
        while (block != findPrev) {
            prevFreeBlock = findPrev;
            findPrev = findPrev->nextMini;
        }
    }

    /* If head of list is removed */
    if ((prevFreeBlock == NULL) && (nextFreeBlock != NULL)) {
        if (size <= LIST0_LIMIT) {
            heap_freeList[LIST0_INDEX] = nextFreeBlock;
        } else if (size <= LIST1_LIMIT) {
            heap_freeList[LIST1_INDEX] = nextFreeBlock;
        } else if (size <= LIST2_LIMIT) {
            heap_freeList[LIST2_INDEX] = nextFreeBlock;
        } else if (size <= LIST3_LIMIT) {
            heap_freeList[LIST3_INDEX] = nextFreeBlock;
        } else if (size <= LIST4_LIMIT) {
            heap_freeList[LIST4_INDEX] = nextFreeBlock;
        } else if (size <= LIST5_LIMIT) {
            heap_freeList[LIST5_INDEX] = nextFreeBlock;
        } else if (size <= LIST6_LIMIT) {
            heap_freeList[LIST6_INDEX] = nextFreeBlock;
        } else if (size <= LIST7_LIMIT) {
            heap_freeList[LIST7_INDEX] = nextFreeBlock;
        } else if (size <= LIST8_LIMIT) {
            heap_freeList[LIST8_INDEX] = nextFreeBlock;
        } else if (size <= LIST9_LIMIT) {
            heap_freeList[LIST9_INDEX] = nextFreeBlock;
        } else if (size <= LIST10_LIMIT) {
            heap_freeList[LIST10_INDEX] = nextFreeBlock;
        } else if (size <= LIST11_LIMIT) {
            heap_freeList[LIST11_INDEX] = nextFreeBlock;
        } else if (size <= LIST12_LIMIT) {
            heap_freeList[LIST12_INDEX] = nextFreeBlock;
        } else if (size <= LIST13_LIMIT) {
            heap_freeList[LIST13_INDEX] = nextFreeBlock;
        } else {
            heap_freeList[LIST14_INDEX] = nextFreeBlock;
        }
        if (!miniBlockFlag)
            nextFreeBlock->prevPtr = NULL;
    }

    /* If tail(end) of the list is removed */
    else if ((prevFreeBlock != NULL) && (nextFreeBlock == NULL)) {
        if (!miniBlockFlag)
            prevFreeBlock->nextPtr = NULL;
        else
            prevFreeBlock->nextMini = NULL;
    }

    /* If an entry in the middle is removed */
    else if ((prevFreeBlock != NULL) && (nextFreeBlock != NULL)) {
        if (!miniBlockFlag) {
            nextFreeBlock->prevPtr = prevFreeBlock;
            prevFreeBlock->nextPtr = nextFreeBlock;
        } else {
            prevFreeBlock->nextMini = nextFreeBlock;
        }
    }

    /* If only free block in list is being removed */
    else {
        if (size <= LIST0_LIMIT) {
            heap_freeList[LIST0_INDEX] = NULL;
        } else if (size <= LIST1_LIMIT) {
            heap_freeList[LIST1_INDEX] = NULL;
        } else if (size <= LIST2_LIMIT) {
            heap_freeList[LIST2_INDEX] = NULL;
        } else if (size <= LIST3_LIMIT) {
            heap_freeList[LIST3_INDEX] = NULL;
        } else if (size <= LIST4_LIMIT) {
            heap_freeList[LIST4_INDEX] = NULL;
        } else if (size <= LIST5_LIMIT) {
            heap_freeList[LIST5_INDEX] = NULL;
        } else if (size <= LIST6_LIMIT) {
            heap_freeList[LIST6_INDEX] = NULL;
        } else if (size <= LIST7_LIMIT) {
            heap_freeList[LIST7_INDEX] = NULL;
        } else if (size <= LIST8_LIMIT) {
            heap_freeList[LIST8_INDEX] = NULL;
        } else if (size <= LIST9_LIMIT) {
            heap_freeList[LIST9_INDEX] = NULL;
        } else if (size <= LIST10_LIMIT) {
            heap_freeList[LIST10_INDEX] = NULL;
        } else if (size <= LIST11_LIMIT) {
            heap_freeList[LIST11_INDEX] = NULL;
        } else if (size <= LIST12_LIMIT) {
            heap_freeList[LIST12_INDEX] = NULL;
        } else if (size <= LIST13_LIMIT) {
            heap_freeList[LIST13_INDEX] = NULL;
        } else {
            heap_freeList[LIST14_INDEX] = NULL;
        }
    }
    /* NULL assignment of hanging block pointers*/
    if (!miniBlockFlag) {
        block->nextPtr = NULL;
        block->prevPtr = NULL;
    } else {
        block->nextMini = NULL;
    }
}

/**
 * @brief   Function performs coalescing of free blocks and updates the
 * appropriate free list.
 *
 *
 * @param[in]   block       Block to be coalesced with adjacent blocks
 * @return      block_t*    Coalesced block
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(block != NULL);

    bool prevAlloc = true;
    bool nextAlloc = true;
    bool prevmini = false;
    block_t *prevBlock = NULL;
    block_t *nextBlock = NULL;
    prevmini = get_prev_mini(block);
    prevAlloc = get_prev_alloc(block);
    nextBlock = find_next(block);
    if (nextBlock != NULL) {
        nextAlloc = get_alloc(nextBlock);
    }
    /* Case 1 */
    if ((prevAlloc == 1) && (nextAlloc == 1)) {
        addToFreeList(block);
    }
    /* Case 2 */
    if ((prevAlloc == 1) && (nextAlloc == 0)) {
        removeFromFreeList(nextBlock);
        write_current_block(block, (get_size(block) + get_size(nextBlock)),
                            false);
        write_next_block(block);
        addToFreeList(block);
    }
    /* Case 3 */
    if ((prevAlloc == 0) && (nextAlloc == 1)) {
        // footer for previous block exists
        if (!prevmini) {
            prevBlock = find_prev(block);
        } else
            prevBlock = find_prev_mini(block);
        removeFromFreeList(prevBlock);
        write_current_block(prevBlock, (get_size(prevBlock) + get_size(block)),
                            false);
        write_next_block(prevBlock);
        addToFreeList(prevBlock);
        block = prevBlock;
    }
    /* Case 4 */
    if ((prevAlloc == 0) && (nextAlloc == 0)) {
        // footer for previous block exists
        if (!prevmini)
            prevBlock = find_prev(block);
        else
            prevBlock = find_prev_mini(block);

        removeFromFreeList(prevBlock);
        removeFromFreeList(nextBlock);
        write_current_block(
            prevBlock,
            (get_size(prevBlock) + get_size(block) + get_size(nextBlock)),
            false);
        write_next_block(prevBlock);
        addToFreeList(prevBlock);
        block = prevBlock;
    }
    dbg_ensures(!get_alloc(block));
    return block;
}

/**
 * @brief   This function extends the heap by size.
 *
 *
 * @param[in]   size
 * @return      block_t*    Returns pointer to a free block after heap extension
 */
static block_t *extend_heap(size_t size) {
    dbg_requires(size > 0);

    void *bp;
    bool prev_alloc;
    bool prev_mini;
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    // write size to get next block
    prev_alloc = get_prev_alloc(block);
    prev_mini = get_prev_mini(block);

    // update the header and footer of current block
    block->header = pack(size, prev_mini, prev_alloc, false);
    *(header_to_footer(block)) = pack(size, prev_mini, prev_alloc, false);
    /* Write size and alloc to current block, prev alloc to next block */
    block_t *block_next = find_next(block);
    // Create new epilogue header
    write_epilogue(block_next);
    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    return block;
}

/**
 * @brief   This function splits the block if assigned block to allocation is
 * bigger than required size for allocation and greater than size of
 * min_block_size
 *
 *
 * @param[in]   block   Block to be split into allocated block of input size and
 * remaining memeory is dubbed as a free block and added to appropriate free
 * list.
 * @param[in]   asize   Block size to be allocated
 * @return void
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(!get_alloc(block));
    size_t block_size = get_size(block);
    dbg_requires(block_size >= asize);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        // make block allocated of size 'asize'
        write_current_block(block, asize, true);
        block_next = find_next(
            block); /* While finding next block the size has been updated */
        // make next block unallocated with size = block_size - asize
        write_current_block(block_next, block_size - asize, false);
        // next blocks for block and nextblock are updated accordingly
        write_next_block(block);
        // This part isnt necessary but still doing it
        write_next_block(block_next);
        addToFreeList(block_next);
    } else {
        /* allocate block */
        write_current_block(block, block_size, true);
        write_next_block(block);
    }
    dbg_ensures(get_alloc(block));
}

/**
 * @brief    Finds free block that "Good" fits the input size
 *
 *
 * @param[in]   asize           size to be allocated from the free block
 * @return      block_t*        "Good" fit block
 */
static block_t *find_good_fit(block_t *freeListHead, size_t asize) {
    dbg_requires(asize > 0);
    block_t *block;

    /* Good fit */
    block_t *goodFitBlock = NULL;
    unsigned long goodFitCounter = 0;
    unsigned long goodFragmentSize = ~0;
    block = freeListHead;

    while (block != NULL && (goodFitCounter <= GOOD_Fit_MAX_COUNT)) {
        if (get_size(block) < asize) {
            block = block->nextPtr;
            continue;
        } else {
            goodFitCounter++;
        }
        if (goodFragmentSize > (unsigned long)(get_size(block) - asize)) {
            goodFragmentSize = (unsigned long)(get_size(block) - asize);
            goodFitBlock = block;
        }
        block = block->nextPtr;
    }
    if (goodFitBlock != NULL)
        return goodFitBlock;
    else
        return NULL; // no fit found
}

/**
 * @brief    Finds free block that best fits the input size
 *
 *
 * @param[in]   asize           size to be allocated from the free blocks
 * @return      block_t*        Best fit block
 */

static block_t *find_best_fit(block_t *freeListHead, size_t asize) {
    dbg_requires(asize > 0);
    block_t *block;
    /* Best fit */
    block_t *bestFitBlock = NULL;
    unsigned long bestFragmentSize = ~0;
    block = freeListHead;
    while (block != NULL) {
        if (get_size(block) < asize) {
            block = block->nextPtr;
            continue;
        }
        if (bestFragmentSize > (unsigned long)(get_size(block) - asize)) {
            bestFragmentSize = (unsigned long)(get_size(block) - asize);
            bestFitBlock = block;
        }
        block = block->nextPtr;
    }
    if (bestFitBlock != NULL)
        return bestFitBlock;
    else
        return NULL; // no fit found
}

/**
 * @brief    Finds free block that first fits the input size
 *
 *
 * @param[in]   asize           size to be allocated from the free blocks
 * @return      block_t*        First fit block
 */

static block_t *find_first_fit(block_t *freeListHead, size_t asize) {
    dbg_requires(asize > 0);
    block_t *block;
    /*First fit */
    block = freeListHead;
    while (block != NULL) {
        if (asize <= get_size(block)) {
            return block;
        }
        block = block->nextPtr;
    }
    return NULL; // no fit found
}

/**
 * @brief This is a debug function that performs following checks:-
 *    1.Memory alignment
 *    2.Checking header and footer match
 *    3.Checking if explicit lists count matches the implicit list free
 * blocks 4.Checking if implicit list contains adjacent free blocks
 *    5.Printing heap and free lists
 *    6.Heap size check
 *    7.Checking if address lies within the heap region
 *    8.Checking if the heap header and footer are correct
 *    9.Checking if explicit list member sizes fall within the list bucket
 * size 10.Checking if explicit list address fall withing heap boundaries
 *    11.Checking if next address and previous address of consecutive
 * explicit list members matches each other
 *
 * @param[in]   line    Line where the function was called in debug mode
 * @return      bool    Indicates if function ran successfully
 */
bool mm_checkheap(int line) {
    dbg_printf("Checkheap called at line %d\n", line);

    // Checking alignment of payload
    if (CHECK_MEM_ALIGNMENT) {
        for (block_t *block = heap_start; get_size(block) > 0;
             block = find_next(block)) {
            if (!alignedAddressCheck((void *)block->payload)) {
                printf("Payload not aligned\n");
            }
        }
    }

    // Checking if address falls outside the heap
    if (CHECK_MEM_REGION) {
        for (block_t *block = heap_start; get_size(block) > 0;
             block = find_next(block)) {
            if (!(((block->payload) > (char *)mem_heap_lo()) &&
                  ((block->payload) < (char *)mem_heap_hi()))) {
                printf("Payload lying outside heap region\n");
                printf("Block payload address=%lx\tHeap Low address=%lx\n",
                       (word_t)(block->payload), (word_t)mem_heap_lo());
                printf("Block payload address=%lx\tHeap High address=%lx\n",
                       (word_t)(block->payload), (word_t)mem_heap_hi());
                while (1)
                    ;
            }
        }
    }
    // Checking heap header and footers

    if (CHECK_MEM_HEAP_START_END) {
        block_t *block = heap_start;
        block_t *heapHeader = (block_t *)((char *)heap_start - wsize);
        block_t *heapFooter = NULL;
        while (!((get_size(block) == 0) && get_alloc(block)))
            block = (block_t *)((char *)block + get_size(block));
        heapFooter = (block_t *)((char *)block + get_size(block));

        if ((heapFooter != (block_t *)(mem_heap_hi() - (OFFSET_TO_SBRK - 1))) ||
            (heapHeader != (block_t *)mem_heap_lo())) {
            printf("Heap header footer boundary error\n");
            printf("Heap footer address=%lx\tHeap High address=%lx\n",
                   (word_t)(heapFooter),
                   (word_t)mem_heap_hi() - (OFFSET_TO_SBRK - 1));
            printf("Heap header address=%lx\tHeap Low address=%lx\n",
                   (word_t)(heapHeader), (word_t)mem_heap_lo());
            while (1)
                ;
        }
    }

    // Checking heap size
    if (CHECK_MEM_HEAP_SIZE) {
        block_t *heapHeader = (block_t *)((char *)heap_start - wsize);
        block_t *heapFooter = NULL;
        block_t *block = heap_start;
        while (!((get_size(block) == 0) && get_alloc(block)))
            block = (block_t *)((char *)block + get_size(block));
        heapFooter = (block_t *)((char *)block + get_size(block));

        if ((size_t)(((word_t)heapFooter + OFFSET_TO_SBRK) -
                     (word_t)heapHeader) != mem_heapsize()) {
            printf("Heap size not matching\n");
            printf("Heap size computed=%lu\tHeap size retrieved=%lu\n",
                   (((word_t)heapFooter + OFFSET_TO_SBRK) - (word_t)heapHeader),
                   (word_t)mem_heapsize());
            while (1)
                ;
        }
    }

    // Checking header and footer match
    if (CHECK_HEADER_FOOTER_VAL) {
        word_t heapHeaderVal = 0;
        word_t heapFooterVal = 0;
        for (block_t *block = heap_start; get_size(block) > 0;
             block = find_next(block)) {
            heapHeaderVal = (block->header);
            if (get_alloc(block) || (get_size(block) <= min_block_size))
                continue;
            heapFooterVal = *(header_to_footer(block));
            if (heapFooterVal != heapHeaderVal) {
                printf("Header Footer values not matching\n");
                while (1)
                    ;
            }
        }
    }

    // Checking if there are adjacent free blocks in implicit list
    if (CHECK_ADJACENT_FREE_BLOCKS) {
        for (block_t *block = heap_start; get_size(find_next(block)) > 0;
             block = find_next(block)) {
            if ((get_alloc(block) == 0) && (get_alloc(find_next(block)) == 0)) {
                printf("Adjacent blocks are free\n");
                while (1)
                    ;
            }
        }
    }

    // Checking for size and count match between explicit freelist and
    // implicit entries
    if (CHECK_EXPLICIT_IMPLICIT_MATCH) {
        word_t freelist_count_explicit = 0;
        word_t freelist_count_implicit = 0;
        word_t freelist_size_explicit = 0;
        word_t freelist_size_implicit = 0;
        for (int i = 0; i < Total_Free_Lists; i++) {
            for (block_t *block = heap_freeList[i]; block != NULL;
                 block = block->nextPtr) {
                freelist_count_explicit++;
                freelist_size_explicit += get_size(block);
            }
        }
        // Counting implicit freelist entries
        for (block_t *block = heap_start; get_size(block) > 0;
             block = find_next(block)) {
            if (get_alloc(block) == 0) {
                freelist_count_implicit++;
                freelist_size_implicit += get_size(block);
            }
        }
        if (freelist_count_implicit != freelist_count_explicit) {
            printf("freelist_count_implicit=%lu\n", freelist_count_implicit);
            printf("freelist_count_explicit=%lu\n", freelist_count_explicit);
            while (1)
                ;
        }
        if (freelist_size_implicit != freelist_size_explicit) {
            printf("freelist_size_implict=%lu\n", freelist_size_implicit);
            printf("freelist_size_explict=%lu\n", freelist_size_explicit);
            while (1)
                ;
        }
    }

    // Check if next and previous pointers of explicit list match
    if (CHECK_EXPLICIT_PREV_NEXT_ADDRESS) {
        block_t *nextPtr = NULL;
        /* Skipping index 0 as it corresponds to mini block that are singly
         * linked */
        for (int i = LIST1_INDEX; i < Total_Free_Lists; i++) {
            for (block_t *block = heap_freeList[i];
                 (block != NULL) && (block->nextPtr != NULL);
                 block = block->nextPtr) {
                nextPtr = block->nextPtr;
                if (block != nextPtr->prevPtr) {
                    printf("Explicit List %d, Previous and Next Pointers not "
                           "matching\n",
                           i);
                    while (1)
                        ;
                }
            }
        }
    }

    // Check if explicit list pointers are between heap header and footer
    if (CHECK_EXPLICIT_LIST_ADDRESS_BOUNDARY) {
        for (int i = 0; i < Total_Free_Lists; i++) {
            for (block_t *block = heap_freeList[i]; block != NULL;
                 block = block->nextPtr) {
                if (!((block > (block_t *)mem_heap_lo()) &&
                      (block < (block_t *)mem_heap_hi()))) {
                    printf("Explicit List %d, Address not within heap "
                           "boundaries\n",
                           i);
                    while (1)
                        ;
                }
            }
        }
    }

    // Check if explicit list sizes is within the list size bucket
    if (CHECK_EXPLICIT_LIST_SIZE) {
        block_t *block = NULL;
        size_t minimumBlockSize = 0;
        size_t maximumBlockSize = 0;
        for (int i = 0; i < Total_Free_Lists; i++) {
            switch (i) {
            case 0:
                block = heap_freeList[LIST0_INDEX];
                minimumBlockSize = 0;
                maximumBlockSize = LIST0_LIMIT;
                break;
            case 1:
                block = heap_freeList[LIST1_INDEX];
                minimumBlockSize = LIST0_LIMIT;
                maximumBlockSize = LIST1_LIMIT;
                break;
            case 2:
                block = heap_freeList[LIST2_INDEX];
                minimumBlockSize = LIST1_LIMIT;
                maximumBlockSize = LIST2_LIMIT;
                break;
            case 3:
                block = heap_freeList[LIST3_INDEX];
                minimumBlockSize = LIST2_LIMIT;
                maximumBlockSize = LIST3_LIMIT;
                break;
            case 4:
                block = heap_freeList[LIST4_INDEX];
                minimumBlockSize = LIST3_LIMIT;
                maximumBlockSize = LIST4_LIMIT;
                break;
            case 5:
                block = heap_freeList[LIST5_INDEX];
                minimumBlockSize = LIST4_LIMIT;
                maximumBlockSize = LIST5_LIMIT;
                break;
            case 6:
                block = heap_freeList[LIST6_INDEX];
                minimumBlockSize = LIST5_LIMIT;
                maximumBlockSize = LIST6_LIMIT;
                break;
            case 7:
                block = heap_freeList[LIST7_INDEX];
                minimumBlockSize = LIST6_LIMIT;
                maximumBlockSize = LIST7_LIMIT;
                break;
            case 8:
                block = heap_freeList[LIST8_INDEX];
                minimumBlockSize = LIST7_LIMIT;
                maximumBlockSize = LIST8_LIMIT;
                break;
            case 9:
                block = heap_freeList[LIST9_INDEX];
                minimumBlockSize = LIST8_LIMIT;
                maximumBlockSize = LIST9_LIMIT;
                break;
            case 10:
                block = heap_freeList[LIST10_INDEX];
                minimumBlockSize = LIST9_LIMIT;
                maximumBlockSize = LIST10_LIMIT;
                break;
            case 11:
                block = heap_freeList[LIST11_INDEX];
                minimumBlockSize = LIST10_LIMIT;
                maximumBlockSize = LIST11_LIMIT;
                break;
            case 12:
                block = heap_freeList[LIST12_INDEX];
                minimumBlockSize = LIST11_LIMIT;
                maximumBlockSize = LIST12_LIMIT;
                break;
            case 13:
                block = heap_freeList[LIST13_INDEX];
                minimumBlockSize = LIST12_LIMIT;
                maximumBlockSize = LIST13_LIMIT;
                break;
            default:
                block = heap_freeList[LIST14_INDEX];
                minimumBlockSize = LIST13_LIMIT;
                maximumBlockSize = ~0;
                break;
            }

            while (block != NULL) {
                if (!((get_size(block) > minimumBlockSize) &&
                      (get_size(block) <= maximumBlockSize))) {
                    printf("Explicit List %d, Sizes not within list bucket "
                           "size\n",
                           i);
                    while (1)
                        ;
                }
                block = block->nextPtr;
            }
        }
    }

    // Print Heap and Free lists
    if (PRINT_IMPLICIT_HEAP_EXPLICT_FREELISTS) {
        printf("----------Heap Start---------------\n");
        for (block_t *block = heap_start; get_size(block) > 0;
             block = find_next(block)) {

            printf("Address of block = %lx\n", (word_t)block);
            printf("size at header = %lu\n", (word_t)get_size(block));
            printf("allocation at header = %lu\n", (word_t)get_alloc(block));
            printf("previous allocation at header = %lu\n",
                   (word_t)get_prev_alloc(block));
            printf("previous mini at header = %lu\n",
                   (word_t)get_prev_mini(block));
            if (!get_alloc(block) && !get_prev_mini(block)) {
                printf("size at footer = %lu\n",
                       (word_t)extract_size(*header_to_footer(block)));
                printf("allocation at footer = %lu\n",
                       (word_t)extract_alloc(*header_to_footer(block)));
                printf("previous allocation at footer = %lu\n",
                       (word_t)extract_prev_alloc(*header_to_footer(block)));
                printf("previous mini at footer = %lu\n",
                       (word_t)extract_prev_mini(*header_to_footer(block)));
            }
        }
        printf("----------Heap End---------------\n");
        printf("----------Free Start---------------\n");
        for (int i = 0; i < Total_Free_Lists; i++) {
            printf("----------Free Start %d---------------\n", i);
            for (block_t *block = heap_freeList[i]; block != NULL;
                 block = block->nextPtr) {
                printf("Address of free block = %lx\n", (word_t)block);
                printf("size at header = %lu\n", (word_t)get_size(block));
                printf("allocation at header = %lu\n",
                       (word_t)get_alloc(block));
                printf("previous allocation at header = %lu\n",
                       (word_t)get_prev_alloc(block));
                printf("previous mini at header = %lu\n",
                       (word_t)get_prev_mini(block));
                if (!(i == LIST0_INDEX)) {
                    printf("size at footer = %lu\n",
                           (word_t)extract_size(*header_to_footer(block)));
                    printf("allocation at footer = %lu\n",
                           (word_t)extract_alloc(*header_to_footer(block)));
                    printf(
                        "previous allocation at footer = %lu\n",
                        (word_t)extract_prev_alloc(*header_to_footer(block)));
                    printf("previous mini at footer = %lu\n",
                           (word_t)extract_prev_mini(*header_to_footer(block)));
                }
            }
            printf("----------Free End %d---------------\n", i);
        }
        printf("----------Free End---------------\n");
    }
    return true;
}

/**
 * @brief   Checks the alignment of the input address
 *
 * @param[in]   p           Address to check the alignement
 * @return      bool        Indicates if the address is alogned or not
 */
static bool alignedAddressCheck(const void *p) {

    if (((word_t)p % dsize) == 0)
        return true;
    else
        return false;
}

/**
 * @brief   Returns the length of the explicit free list
 *
 * @param[in]   freeListHead                Head of the free list
 * @return      unsigned long               Length of the free list
 */
static unsigned long getFreeListLength(block_t *freeListHead) {
    unsigned long iFreeListLength = 0;
    block_t *block;
    for (block = freeListHead; block != NULL; block = block->nextPtr) {
        iFreeListLength++;
    }
    return (iFreeListLength);
}

/**
 * @brief   Initialises the heap with free list pointers, header and footer
 * of the heap and initial heap allocation of chunksize
 *
 * @return bool     Indicator of successful intialisation of the heap
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, false, true, true); // Heap prologue (block footer)
    start[1] = pack(0, false, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    /*Initialising heads of free lists*/
    for (int i = 0; i < Total_Free_Lists; i++) {
        heap_freeList[i] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }
    dbg_ensures(mm_checkheap(__LINE__));
    return true;
}

/**
 * @brief   Allocates memory of input size
 *
 * @param[in]   size    Size of memory to be allocated
 * @return      void*   Address of memory allocated
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    dbg_requires(size > 0);

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block = NULL;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment
    // requirements changed to 8 bytes only considering header
    asize = round_up(size + wsize, dsize);
    // Finding fit
    block = find_fit(asize, GOOD_FIT);

    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }
    removeFromFreeList(block);
    // Try to split the block if too large, here asize is the size
    // needed
    split_block(block, asize);

    bp = header_to_payload(block);
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief       Frees a previously allocated memory region
 *
 * @param[in]   bp    Pointer to memory region to be freed
 * @return      void
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_current_block(block, size, false);
    write_next_block(block);
    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief   Performs rellocation of memory by copying the contents to the
 * new region
 *
 *
 * @param[in] ptr       Pointer to memory that is to be reallocated
 * @param[in] size      Size of reallocation
 * @return    void*     Address to new memory region that was allocated
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;
    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data

    copysize = get_size(block) - wsize; // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief   Allocates memory of input size and initialises to '0'
 *
 * @param[in]   elements    Number of elements, each of 'size'
 * @param[in]   size        Size of a single element
 * @return      void*       Pointer to the allocated memory
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines! *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20 *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20 * 68 65 78 61
 *64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               * 6f 2e 2e
 *2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64 * 69 6e 67 21
 *20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               * 68 21 20
 *2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */