
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
//221206
team_t team = {
    /* Team name */
    "team9",
    /* First member's full name */
    "jeonje",
    /* First member's email address */
    "whssodi@gmail.com",
    /* Second member's full name (leave blank if none) */
    "papeparrot",
    /* Second member's email address (leave blank if none) */
    "papeparrot"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*********************************************************
Basic constants and macros
 ********************************************************/
#define WSIZE 4 
#define DSIZE 8 /* bytes */
#define CHUNKSIZE (1<<12) /* extend heap by this amount(bytes) */
/*inital block size is 4GB in 64bits system*/

#define MAX(x,y) ((x) > (y)? (x) : (y))
/* Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
/* ~0x7 = 0x .... 000 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Give block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* GET Explicit free list Next/Prev pointer */
#define GET_PREV_PTR(bp) (*(char **)(bp + WSIZE))
#define GET_NEXT_PTR(bp) (*(char **)(bp))

/* SET Explicit free list Next/Prev pointer */
#define SET_PREV_PTR(bp, p) (GET_PREV_PTR(bp) = p)
#define SET_NEXT_PTR(bp, p) (GET_NEXT_PTR(bp) = p)
/*
 * mm_init - initialize the malloc package.
 */

/*********************************************************
forward declaration
 ********************************************************/
int mm_init(void);
static void *extend_heap(size_t);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_in_freelist(void *bp);
static void remove_from_freelist(void *bp);
/* heap list pointer */
static char *heap_listp = 0;
static char *start_of_freelist = 0;

static void insert_in_freelist(void *bp)
{
    SET_NEXT_PTR(bp, start_of_freelist);
    SET_PREV_PTR(start_of_freelist, bp);
    SET_PREV_PTR(bp, NULL);
    start_of_freelist = bp;
}

static void remove_from_freelist(void *bp)
{
    if(GET_PREV_PTR(bp)){
        SET_NEXT_PTR(GET_PREV_PTR(bp),GET_NEXT_PTR(bp));
    }else{
        start_of_freelist = GET_NEXT_PTR(bp);
    }
    SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}

static void *find_fit(size_t asize)
{
    void *bp;
    static int last_malloced_size = 0;
    static int repeat_counter = 0;
    if( last_malloced_size == (int)asize){
        if(repeat_counter>50){  
            int extendsize = MAX(asize, 4 * WSIZE);
            bp = extend_heap(extendsize/4);
            return bp;
        }
        else
            repeat_counter++;
    }
    else
        repeat_counter = 0;
    for (bp = start_of_freelist; GET_ALLOC(HDRP(bp)) == 0; bp = GET_NEXT_PTR(bp) ){
        if (asize <= (size_t)GET_SIZE(HDRP(bp)) ) {
        last_malloced_size = asize;
        return bp;
        }
    }
    return NULL;

 
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (4*WSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_from_freelist(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_from_freelist(bp);
    }
}
static void *coalesce(void *bp)
{
      //if previous block is allocated or its size is zero then PREV_ALLOC will be set.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

      /* Next block is only free */   
    if (prev_alloc && !next_alloc) {                  
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_freelist(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Prev block is only free */  
    else if (!prev_alloc && next_alloc) {               
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_from_freelist(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Both blocks are free */ 
    else if (!prev_alloc && !next_alloc) {                
        size += GET_SIZE( HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_freelist(PREV_BLKP(bp));
        remove_from_freelist(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }/* lastly insert bp into free list and return bp */
    insert_in_freelist(bp);
    return bp;

}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    /* Returns NULL if there is no additional heap allocation space. */

     if (size < 16){
        size = 16;
    }

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);

}

int mm_init(void)
{
    /* Create the inital empty heap */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alginment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE ,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE);
    start_of_freelist = heap_listp;

    /* Extend the empty heap with a free block of minimum possible block size */
    if (extend_heap(4) == NULL)
        return -1;
    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize;
    char *bp;

    /* Ignore spurious request */
    if (size ==0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs  */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    /* Search the free list for a fit */
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
   
    void *old_ptr = ptr;
    size_t old_size = GET_SIZE(HDRP(old_ptr));
    size_t size_with_hf = size + (2 * WSIZE);

    if (old_size < 0){
        return NULL;
    }
    else if (old_size == 0){
        mm_free(old_ptr);
        return NULL;
    }
    //현재 잡고 있는 메모리가 요청한 메모리보다 큰 경우
    //ptr을 재활용
    if (old_size >= size_with_hf){
        return ptr; 
    }
    // 새로 할당해야하는 크기가 ptr이 가리키고있는 블록보다 클 경우 
    else {
        size_t new_size = GET_SIZE(HDRP(NEXT_BLKP(ptr))) + old_size;
        //다음 블록이 비었고, 현재 블록크기와 다음 블록의 크기의 합이 요청한블록보다 클 경우 
        if(!GET_ALLOC(HDRP(NEXT_BLKP(old_ptr))) && new_size >= size_with_hf){
            // malloc을 하지 않고 기존의 old_ptr을 재사용
            remove_from_freelist(NEXT_BLKP(ptr)); 
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size ,1));
            return ptr; 
        }
        else{
            void *new_ptr;
            //위 케이스에 아무것도 해당되지 않아 새로 할당해줘야 하는 경우 
            new_ptr = mm_malloc(size_with_hf);
            
            if (new_ptr == NULL)
                return NULL;
            place(new_ptr, size_with_hf);
            memcpy(new_ptr, old_ptr, size_with_hf);
            // memmove(new_ptr, old_ptr, size_with_hf);
            mm_free(old_ptr);
            return new_ptr;
        }
    }
  
}

