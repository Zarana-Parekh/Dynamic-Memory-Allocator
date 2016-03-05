/*
mm_init: 
This function allocates a free chunk of memory to be used for allocation using mem_sbrk function. Prologue and epilogue blocks are set with appropriate padding.

mm_malloc:
Given the required size of block to be allocated, first the adjusted size of the block is calculated based on alignment and overhead considerations. If the required size of block is found, it is allocated, else the heap is extended and then the required block is allocated,

mm_free:
When a block is freed, the status of the freed block is updated in the current block and the next block. Then the coalesce function is called to merge the previous or the next block in case either or both of those are free.

mm_realloc:
To reallocate a block so that it is of the required size as passed in the argument of the function, first calculate the adjusted size of the block considering the alignment and overhead. Now compare the required block size with the original size of the block we have.

If the adjusted size is lesser than or equal to the original block size, then the original block is allocated after splitting or allocated entirely depending upon the size of the block that would be left unused after allocation.

If the next block is free and the next block and current block size after coalescing can satisfy the required allocation request then this condition is checked next and the blocks are coalesced to satisfy the memory allcoation request. The status of the coalesced block is updated in the next block.

If all the above conditions fail, a new block of memory is allocated at some other location on the heap, with the contents of the block intact and the current block is freed.

coalesce:
With reference to the current block which is free,
(I) If the previous and next block are allocated, there is no coalescing,
(II) If the previous block is free and next block is allocated, the current block is coalsced with the previous block, with the block pointer and the contents of the header and footer (size of block and allocation status) updated.
(III) If the next block is free and previous block is allocated, the current block is coalsced with the next block, with the block pointer and the contents of the header and footer (size of block and allocation status) updated.
(IV) If the previous and the next block are both free, then both blocks are coalsced with the required update of the block pointer, header and footer.

extend_heap:
Based on the additional space required and after adjusting it to take into consideration the memory alignment and overhead, the required size block is placed in the heap and a new epilogue is created. The previous status in the new block corresponds to the allocation status of the last block in the heap before being extended. If this block was free, they are coalsced and the updated pointer  is returned.

find_fit:
The first fit method is used to search the list for a required size, with the search beginning at the start of the list.

place:
This function allocates a block based on the block size and memory request. If the block size left unused on allocating the entire block would be greater than 8 bytes, then the block is split up into two and one block is allocated while the other is free. If lesser size of the block will be left unused then the entire block is allocated. The status of the next block will be updated if necessary.
*/

/* 
Simple, 32-bit and 64-bit clean allocator based on an implicit free list, first fit placement, and boundary tag coalescing with the footer only for free blocks. The status of the current (bit 0) and previous (bit 1) block is stored in the header and footer.
 
Blocks are aligned to double-word boundaries.  This yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned blocks on a 64-bit processor.  However, 16-byte alignment is stricter than necessary; the assignment only requires 8-byte alignment. 
*/
 
 /* This allocator uses the size of a pointer, e.g., sizeof(void *), to define the size of a word.  This allocator also uses the standard type uintptr_t to define unsigned integers that are the same size as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"malloc",
	/* First member's full name */
	"Zarana Parekh",
	/* First member's email address */
	"201301177@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Zarana Parekh",
	/* Second member's email address (leave blank if none) */
	"201301177@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */
#define MINIMUM 24 /* minimum size of block to be allocated */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)
#define GET_PREV_ALLOC(p)  (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  (int *)((char *)(bp) - WSIZE)
#define FTRP(bp)  (int *)((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  (int *)((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  (int *)((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	
	if((size+WSIZE)%DSIZE==0)
		asize=size+WSIZE;
	else
		asize = (((size+WSIZE)/DSIZE)+1)*DSIZE;

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	if(!prev_alloc) {
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	} else {
	PUT(HDRP(bp), PACK(size, 2));
	PUT(FTRP(bp), PACK(size, 2));
	}	
	int *next = NEXT_BLKP(bp);
	size_t size_next = GET_SIZE(HDRP(next));
	bool next_alloc = GET_ALLOC(HDRP(next));
	if(!next_alloc) {
	PUT(HDRP(next), PACK(size_next, 0));
	PUT(FTRP(next), PACK(size_next, 0));		
	} else {
	PUT(HDRP(next), PACK(size_next, 1));
	}
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));
	oldsize = GET_SIZE(HDRP(ptr));
	size_t asize;
	if((size+WSIZE)%DSIZE==0)
			asize = size+WSIZE;
	else
		asize = (((size+WSIZE)/DSIZE+1)*DSIZE);
	if(oldsize == asize)
		return ptr;
	if(oldsize > asize) {
		if(oldsize-asize<=MINIMUM)
			return ptr;
		bool prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
		if(!prev_alloc) {
				PUT(HDRP(ptr),PACK(asize,1));
		} else {
				PUT(HDRP(ptr),PACK(asize,3));		
		}
		PUT(HDRP(ptr),PACK(oldsize-asize,2));
		PUT(FTRP(ptr),PACK(oldsize-asize,2));		
		int *next = NEXT_BLKP(ptr);
		bool next_alloc = GET_ALLOC(HDRP(next));
		size_t size_next = GET_SIZE(HDRP(next));
		if(!next_alloc) {
			PUT(HDRP(ptr),PACK(size_next,0));		
			PUT(FTRP(ptr),PACK(size_next,0));
		} else {
			PUT(HDRP(ptr),PACK(size_next,1));		
		}
	}
	int *next = NEXT_BLKP(ptr);
	bool next_alloc = GET_ALLOC(HDRP(next));
	if(!next_alloc) {
		size_t size_next = GET_SIZE(HDRP(next));
		if((size_next+oldsize)>=asize) {
			oldsize += size_next;
			if((oldsize-asize)>=(2*WSIZE)){
				bool prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
				if(!prev_alloc) {
					PUT(HDRP(ptr),PACK(asize,1));
				} else {
					PUT(HDRP(ptr),PACK(asize,3));
				}
				int *next = NEXT_BLKP(ptr);
				PUT(HDRP(next),PACK(oldsize-asize,2));
				PUT(FTRP(next),PACK(oldsize-asize,2));				
			} else {
				bool prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
				if(!prev_alloc) {
					PUT(HDRP(ptr),PACK(oldsize,1));
				} else {
					PUT(HDRP(ptr),PACK(oldsize,3));
				}
				int *next = NEXT_BLKP(ptr);
				size_t size_next = GET_SIZE(HDRP(next));
				bool next_alloc = GET_ALLOC(HDRP(next));
				if(!next_alloc) {
					PUT(HDRP(next),PACK(size_next,2));
					PUT(FTRP(next),PACK(size_next,2));
				} else {
					PUT(HDRP(next),PACK(size_next,3));
				}
			}
			return ptr;
		}
	}
	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *coalesce(void *bp) 
{
	bool prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 2));
		PUT(FTRP(bp), PACK(size, 2));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 2));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 2));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 2));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 2));
		bp = PREV_BLKP(bp);
	}
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);
	bool prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	/* Initialize free block header/footer and the epilogue header. */
	if(!prev_alloc) {
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	} else {
		PUT(HDRP(bp),PACK(size,2));
		PUT(FTRP(bp),PACK(size,2));
	}
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *find_fit(size_t asize)
{
	void *bp;

	/* Search for the first fit. */
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	}
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * WSIZE)) { 
		bool prev_alloc = GET_PREV_ALLOC(HDRP(bp));
		if(!prev_alloc) {
			PUT(HDRP(bp), PACK(asize, 1));
		} else {
			PUT(HDRP(bp), PACK(asize, 3));
		}
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 2));
		PUT(FTRP(bp), PACK(csize - asize, 2));
	} else {
		bool prev_alloc = GET_PREV_ALLOC(HDRP(bp));
		if(!prev_alloc) {
			PUT(HDRP(bp), PACK(csize, 1));
		} else {
			PUT(HDRP(bp), PACK(csize, 3));
		}
		int *next = NEXT_BLKP(bp);
		size_t size_next = GET_SIZE(HDRP(next));
		bool next_alloc = GET_ALLOC(HDRP(next));
		if(!next_alloc) {
			PUT(HDRP(next),PACK(size_next,2));
			PUT(FTRP(next),PACK(size_next,2));
		} else {
			PUT(HDRP(next),PACK(size_next,3));
		}
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
