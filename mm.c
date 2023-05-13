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
    "7",
    /* First member's full name */
    "Sangyoon Kim\n",
    /* First member's email address */
    "w2300n@gmail.com\n",
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

/*
 * 기본 상수와 매크로
 */
/* 기본 단위 - word, double word, 새로 할당받는 힙의 크기 CHUNKSIZE 정의 */
#define WSIZE 8                 // 워드, 헤더/푸터 사이즈 (bytes)
#define DSIZE 16                 // 더블워드 사이즈 (bytes)
#define CHUNKSIZE (1 << 12)     // 힙 사이즈 확장 크기 기준 : 4,096bytes -> 4KB

#define MAX(x, y) (x > y ? x : y)

/* header 및 footer 값(size + allocated) 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서의 word를 읽어오거나 쓰는 함수 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에 있는 header 또는 footer의 사이즈와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7) // NOT 연산자로 SIZE만 뽑아오기 위해
#define GET_ALLOC(p) (GET(p) & 0x1) // 0x1과 곱해서 끝 자리가 여전히 1이라면 allocated

/* 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소 반환 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 인자로 받아 이후, 이전 블록의 주소 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // (char*)(bp) + GET_SIZE(지금 블록의 header값)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // (char*)(bp) - GET_SIZE(이전 블록의 footer값)

/* 전역 변수 & 함수 목록 */
static char *heap_listp;

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);

/*
 * mm_init : 4 words 사이즈의 free 리스트를 초기화하고, 초기 free 블록 생성
 */
int mm_init(void)
{
    // mm_malloc, mm_free를 호출하기 전에 mm_init으로 초기화
    // 초기 힙 생성
    // 4 words 사이즈의 빈 가용 리스트 초기화
    // 4 words 구성 : unused padding, prologue_header, prologue_footer, epilogue_header
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                         /* 정렬 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    // 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/*
 * extend_heap(words) : 워드 단위 메모리를 인자로 받아, 새 가용 블록으로 힙을 확장한다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 더블 워드 정렬에 따라 mem_sbrk함수로 추가 힙 메모리를 할당받는다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL; // brk 포인터에 size만큼 더해서 힙을 늘림. 실패시 -1

    // 가용 블록의 헤더와 풋터, 에필로그 헤더를 초기화
    PUT(HDRP(bp), PACK(size, 0));         // 가용 블록의 헤더 - 초기에는 할당 비트를 0(free)으로 준다.
    PUT(FTRP(bp), PACK(size, 0));         // 가용 블록의 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더 - 다음 sbrk 호출 시 새로운 가용블록의 헤더가 됨

    // 이전 블록이 가용하다면 coalesce
    return coalesce(bp);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 블록 사이즈 조정 
    size_t extendsize; // 들어갈 자리가 없을 때 늘려야 하는 힙의 용량
    char *bp;

    if (size == 0)
        return NULL;

    /* 최소 16바이트 크기의 블록 구성. 8바이트 for 정렬 조건 만족 위해, 추가 8바이트 for 헤더, 풋터 오버헤드를 위해 */  
    if (size <= DSIZE)
    {   // adjust size : 조정된 사이즈. 2*8 = 16 , 8보다 작은 요청값은 다 16으로 만든다
        asize = 2 * DSIZE;
    }
    else
    {   // 8바이트 넘는 요청 : 오버헤드 바이트 내에 더해주고, 인접 8의 배수로 반올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    } 

    if ((bp = find_fit(asize)) != NULL)
    { // 맞는 블록 찾으면 - 할당기 : place로 요청 블록 배치, 옵션으로 초과부분 분할, 새 할당 블록 리턴(반환)
        place(bp, asize); // put해서 bp를 헤더에 asize만큼 넣어준다(할당해준다) 
        return bp;
    }

    // 못찾으면 : extend_heap으로 힙을 새 가용 블록으로 확장(메모리 공간 더 할당), 요청 블록을 이 새 가용 블록에 배치
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize); // 필요하면 블럭 분할
    return bp;
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

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;

    for(bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; 
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
