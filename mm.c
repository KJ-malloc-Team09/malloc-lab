/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
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
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8

#define CHUNKSIZE (1<<12)   /* Extend heap by amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))    // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값 리턴

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))       // p가 참조하는 헤더 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // p가 가리키는 워드에 val 저장

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7) // 헤더 사이즈, 할당 비트 리턴
#define GET_ALLOC(p)    (GET(p) & 0x1) // 풋터 사이즈, 할당 비트 리턴

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)  // 헤더를 가리키는 포인터 리턴
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터를 가리키는 포인터 리턴

/* Given block ptr bp, comupte address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) // 다음 블록 포인터 리턴
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) // 이전 블록 포인터 리턴

/* 추가로 선언한 함수들 */
static void *heap_listp;
static void *last_bp;       // 이 변수는 다른 파일에서 여러번 접근할 때도 계속 기존 값을 유지해야 하므로 static이 필요하다.
/* last_bp를 업데이트 해주는 경우는 총 3가지. 첫 init때 last_bp = heap_listp로 초기화해주는 과정.
 * 다음은 place로 블록을 할당해줄 때 bp가 바뀌므로 한번.
 * coalesce로 블록 합치는 과정에서 앞 블록과 합쳐질 경우 bp가 바뀌므로 한번.
*/

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
// 힙 리스트를 힙에서 필요한 만큼 가져오기
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL; /* No fit */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); //현재 블록의 크기

    // 현재 사이즈가 할당할 사이즈보다 당연히 클텐데. 그 차이가 더블워드*2 이상이면? 헤더풋터가 합쳐서 8바이트니까 데이터까지 집어넣고 8의배수 맞추려면 최소 더블워드*2만큼 있어야지.
    // 필요한 만큼 할당하고 그 이후 공간은 빈 공간으로 남기기
    if ((csize - asize) >= (2*DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));        // 헤더에 할당할 사이즈 업데이트
        PUT(FTRP(bp), PACK(asize, 1));        // 풋터에 할당할 사이즈 업데이트
        bp = NEXT_BLKP(bp);                   // bp를 다음 블록의 앞부분으로 옮기기
        PUT(HDRP(bp), PACK(csize-asize, 0));  // 할당하고 남은 크기만큼 가용 공간 남기기, 헤더에 사이즈 업데이트
        PUT(FTRP(bp), PACK(csize-asize, 0));  // 풋터에 사이즈 업데이트
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));    // 현재 블록에 사이즈 업데이트
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














