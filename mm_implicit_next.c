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
    "Sangyoon Kim",
    /* First member's email address */
    "w2300n@gmail.com",
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
#define WSIZE 8                 // word, header/footer size (bytes)
#define DSIZE 16                // double word size (bytes)
#define CHUNKSIZE (1 << 12)     // 힙 사이즈 확장 크기 기준 : 4,096bytes -> 4KB
/* Calculate Max Value */
#define MAX(x, y) (x > y ? x : y)

/* header 및 footer 값(size + allocated) 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서의 word를 읽어오거나 쓰는 함수 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에 있는 Header 또는 Footer의 사이즈와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7) // NOT 연산자로 SIZE만 뽑아오기 위해
#define GET_ALLOC(p) (GET(p) & 0x1) // 0x1과 곱해서 끝 자리가 여전히 1이라면 allocated

/* block pointer(bp)를 인자로 받아 block의 Header와 Footer의 주소 반환 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* block pointer(bp)를 인자로 받아 이후, 이전 블록의 주소 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // (char*)(bp) + GET_SIZE(지금 블록의 Header값)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // (char*)(bp) - GET_SIZE(이전 블록의 Footer값)

/* 전역 변수 & 함수 목록 */
static char *heap_listp;    // heap의 첫번째 pointer--------------------------------------
void *prev_bp;              // next_fit 이전 검색 종료 지점 저장용 변수

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_next_fit(size_t);
static void place(void *, size_t);

/*
 * mm_init : 4 words 사이즈의 free 리스트를 초기화하고, 초기 free 블록 생성
 */
int mm_init(void) // 메모리 처음 만들기
{
    // mm_malloc, mm_free를 호출하기 전에 mm_init으로 초기화
    // 초기 힙 생성
    // 4 words 사이즈의 빈 가용 리스트 초기화
    // 4 words 구성 : unused padding, prologue_header, prologue_footer, epilogue_header
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1; // mem_sbrk 호출해서 4 words size 메모리 request하는데 실패하면 -1 리턴
        
    PUT(heap_listp, 0);                             // heap:0에 free 넣는다  /* alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // heap:1에 Double Size(DSIZE)와 allocated 넣는다.  /* Prologue Header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // heap:2에 Double Size(DSIZE)와 allocated 넣는다. /* Prologue Footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // heap:3에 allocated 넣는다. /* Epilogue Header */
    heap_listp += (2*WSIZE); // heap_listp 포인터를 옮겨준다.
    prev_bp = heap_listp;

    // 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // chunk size 확인(받을 수 있는 사이즈인지)
        return -1;
    return 0;
}

/*
 * extend_heap(words) : 워드 단위 메모리를 인자로 받아, 새 가용 블록으로 힙을 확장한다.
 */
static void *extend_heap(size_t words) // 힙을 넘어간다면 힙을 추가로 받아옴-----------------------
{
    char *bp;
    size_t size;

    // 더블 워드 정렬에 따라 mem_sbrk함수로 추가 힙 메모리를 할당받는다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 짝수로 만든다.
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 너무 커서 할당 못받으면 return -1
        return NULL;                                          // brk 포인터에 size만큼 더해서 힙을 늘림. 실패시 -1

    // free block의 Header와 Footer, Epilogue Header 초기화
    PUT(HDRP(bp), PACK(size, 0));         // free block의 Header - 초기에는 할당 비트를 0(free)으로 준다.
    PUT(FTRP(bp), PACK(size, 0));         // free block의 Footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 Epilogue Header - 다음 sbrk 호출 시 새로운 free block의 Header가 됨

    // 이전 block이 free였다면 coalesce(연결)
    return coalesce(bp);
}

/*
 * coalesce(bp) : 현재 free block을 이전, 다음 free block과 연결
 */
static void *coalesce(void *bp)  // 연속된 free 처리 ---------------------------------------
{  /* 이전, 다음 block의 free여부에 따라 4가지 케이스로 coalesce(연결)을 진행*/
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 block이 alloc 인가?
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 block이 alloc 인가?
    size_t size = GET_SIZE(HDRP(bp));                    // 현재 block의 사이즈

    if (prev_alloc && next_alloc)               // case 1 : 앞 뒤 다 allocated이면
        return bp;                              // block병합 없이 bp 리턴
    
    else if (prev_alloc && !next_alloc)         // case 2 : 이전 allocated 1, 다음 free 0
    {                                           // 다음 block 사이즈까지 합쳐서 free 시킨다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)         // case 3 : 이전 free 0, 다음 allocated 1
    {                                           // 이전 block 사이즈까지 합쳐서 free 시킨다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));           // Footer의 ptr을 구할 때, Header Pointer가 반영되므로 먼저 구함
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else                                        // case 4 : 이전 free 0, 다음 free 0
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    prev_bp = bp;
    return bp;
}

/*
 * mm_malloc(size) : 요청 받은 메모리 사이즈를 인접한 8의 배수로 올려 할당한다.
 *                   만약 맞는 크기의 가용 블록이 없다면 추가 힙 메모리를 확장 & 할당한다.
 */
void *mm_malloc(size_t size)   // 메모리 할당 -----------------------------------------------
{
    size_t asize;      // 할당된 block 사이즈 조정 
    size_t extendsize; // 들어갈 자리가 없을 때 늘려야 하는 힙의 용량
    char *bp;

    if (size == 0)     // 만약 입력받은 사이즈가 0이면 무시
        return NULL;

    /* 최소 16바이트 크기의 블록 구성. 8바이트 for 정렬 조건 만족 위해, 추가 8바이트 for 헤더, 풋터 오버헤드를 위해 */  
    if (size <= DSIZE) // 만약 입력받은 사이즈가 DSIZE보다 작아도 최소 SIZE로 생성
    {   // adjusted size(asize) : 조정된 사이즈. 2*8 = 16 , 8보다 작은 요청값은 다 16으로 만든다
        asize = 2 * DSIZE;
    }
    else // 8의 배수(DSIZE)로 생성
    {   // 8바이트 넘는 요청 : 오버헤드 바이트 내에 더해주고, 가까운 8의 배수로 반올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    } 

    if ((bp = find_next_fit(asize)) != NULL) // 들어갈 free block이 있다면 넣어준다.
    { // 맞는 블록 찾으면 - 할당기 : place로 요청 블록 배치, 옵션으로 초과부분 분할, 새 할당 블록 리턴(반환)
        place(bp, asize); // put해서 bp를 헤더에 asize만큼 넣어준다(할당해준다) 
        return bp;
    }

    // 맞는 free block이 없을 때
    // 힙을 새로운 free block으로 확장하고,
    // extend_heap으로 힙을 새로운 free block으로 확장(메모리 공간 더 할당), 
    // 요청한 블록을 새로운 free block에 배치(place)
    extendsize = MAX(asize, CHUNKSIZE); // 만약 chunk size(csize)보다 클 경우, 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // 넘긴 사이즈만큼의 heap을 할당 받는다.
        return NULL;    
    place(bp, asize); // 필요하면 block 분할
    return bp;
}

/*
 * find_next_fit(size) : 지난 탐색 종료 블록부터 탐색, 제일 처음 발견된 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환한다.
 */
static void *find_next_fit(size_t asize)
{
    void *bp;
    
    for (bp = prev_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }

    // 다음 블록에서부터 탐색했을 때 없었다면, 다시 처음부터 prev_bp 전까지 탐색
    for (bp = heap_listp; bp != prev_bp && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // Header가 Free이거나 주어진 size보다 fit하면
        {
            return bp;
        }
    }
    return NULL; 
}

/*
 * place(bp, size) : size만큼 할당 후 남는 부분이 분할되었다면 free 블록 처리를 해준다.
 */
static void place(void *bp, size_t asize) // free block에 넣어주는 함수 ---------------------------
{
    size_t csize = GET_SIZE(HDRP(bp));    // Header의 Size를 읽어옴

    if ((csize - asize) >= (2*DSIZE))     // 삽입하고 자리가 남으면 split 해준다.
    {   
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {                                // 딱 맞으면 그냥 넣어줌
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free(bp) - size와 할당 정보를 초기화한다.
 */
void mm_free(void *bp) // block free시키는 함수 --------------------------------------------
{
    size_t size = GET_SIZE(HDRP(bp)); // Header의 Size를 읽어옴

    PUT(HDRP(bp), PACK(size, 0));     // Header에 free 입력
    PUT(FTRP(bp), PACK(size, 0));     // Footer에 free 입력
    coalesce(bp);                     // Coalesce(연결) 시켜줌
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)        // Re-allocation
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);                   // 다른 곳에 다시 할당 받기

    if (newptr == NULL)                         // 실패하면 NULL 리턴
        return NULL;

    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE); // 원래 block 사이즈
    if (size < copySize)                        // 요청한 사이즈가 작다면 작은사이즈로 copy
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);                            // 기존 사이즈는 삭제
    return newptr;
}