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

team_t team = {
    /* Team name */
    "team 4",
    /* First member's full name */
    "Moon Seunghyeon",
    /* First member's email address */
    "victorymsh@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t: 해당 시스템에서 어떤 객체나 값이 포함할 수 있는 최대 크기의 데이터 
#define WSIZE 8 // header, footer 사이즈를 4byte로(1word)
#define DSIZE 16 // double word 사이즈 8byte
#define CHUNKSIZE (1<<12) // 1을 왼쪽으로 12칸 쉬프트 연산(2의 12승)/extend heap을 위해 메모리 최소단위 1페이지(4kib) 만큼의 데이터를 세팅

#define MAX(x, y) ((x) > (y) ? (x) : (y)) //x가 y보다 크면 x, 작으면 y를 return

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 리턴

#define GET(p) (*(unsigned int *)(p)) //인자 p가 참조하는 워드를 읽어서 리턴/p는 보통 void형인데 void형 포인터를 역참조할수 없으므로 캐스팅/32비트 시스템이라 unsigned int(2의 32승)
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val을 저장/GET과 동일하게 캐스팅

#define GET_SIZE(p) (GET(p) & ~0x7) //GET으로 가져온 p의 사이즈 정보/p는 size+allocated 값으로, 32비트 중 29비트까지의 사이즈값을 찾을 수 있음
#define GET_ALLOC(p) (GET(p) & 0x1) //할당 여부를 나타내는 맨 뒷자리 확인

#define HDRP(bp) ((char *)(bp) - WSIZE) //bp가 속한 블록의 헤더, bp는 페이로드 시작점이므로 헤더의 크기(wsize)를 빼면 헤더의 시작포인터가 나옴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //bp에 블록의 사이즈를 더하면 다음 블록의 페이로드를 가리키는 포인터가 됨

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 bp
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 bp

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);

static char* heap_listp = NULL;
static void* last_freep;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 mem_sbrk는 할당 요청이 들어왔을 때 요청받은 용량이 힙의 크기를 초과하지 않으면, 할당 요청 용량만큼 보내줌/초과하면 error
 */
int mm_init(void)  
{

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) //메모리에서 가져온 걸로 heap_listp 초기화
        return -1;

    PUT(heap_listp, 0); //더블워드 정렬을 위한 미사용 패딩(0) 할당
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더 할당
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터 할당
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 헤더 할당
    heap_listp += (2 * WSIZE); // heap_listp는 항상 프롤로그 블록의 가운데를 가리켜야함

    last_freep = heap_listp; // NEXTFIT 사용을 위한 선언

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) //chunksize(바이트 단위이므로 wsize로 나눠서 워드 단위로 구성)만큼 힙을 확장해 초기 free블록 가져오기
        return -1;

    return 0;   
}

static void *find_fit(size_t asize)
{
    void *bp;
    void *freeb = last_freep; //종료된 시점부터 찾기 위한 주소 부여

    for(bp = last_freep; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) { //이전 탐색이 종료된 시점부터 시작
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 할당되어있지 않고(free상태) && 넣어야 될 사이즈가 블록 size보다 작다면
            return bp; // 넣을 수 있는 블록이니 해당 bp 리턴
    }

    for(bp = heap_listp; bp < freeb; bp = NEXT_BLKP(bp)) { // 종료된 시점까지 처음부터 탐색
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 할당되어있지 않고(free상태) && 넣어야 될 사이즈가 블록 size보다 작다면
            return bp; // 넣을 수 있는 블록이니 해당 bp 리턴
    }

    last_freep = bp;

    return NULL;

    //first fit의 경우
    // for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // heap_listp의 bp부터 ep헤더까지(ep헤더는 bp사이즈가 0) 돌면서, size가 0이 아닌 블록들 중
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 할당되어있지 않고(free상태) && 넣어야 될 사이즈가 블록 size보다 작다면
    //         return bp; // 넣을 수 있는 블록이니 해당 bp 리턴
    // }
    // return NULL; // 에필로그까지 보고도 없으면 null 반환
}

static void place(void *bp, size_t asize)
{
    
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 할당할 수 있는 free 블록의 사이즈

    if((csize - asize) >= (2 * DSIZE)) { // // 2 * DSIZE는 총 4개의 word. csize - asize 부분에 헤더, 푸터, 페이로드, 패딩까지 총 4개가 들어갈 수 있어야 free 블록이 된다.
        //앞 블록은 할당
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        //뒷 블록은 free
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp); // free 이후 뒷블록과 병합 실행
    }

    else { // 분할이 불가능한경우-> 4개가 못 들어가므로 내부 단편화 발생
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize; // 블록 사이즈
    size_t extendsize; // 메모리가 부족할 때 힙을 연장할 크기
    char *bp;

    if(size == 0) // 가짜 요청 무시
        return NULL;

    if(size <= DSIZE) // 정렬과 헤더/푸터 크기를 고려해서 블록 사이즈 조정
        asize = 2 * DSIZE; // 크기가 8바이트보다 작으면 asize를 16바이트로 만들어줌
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
        // 8바이트 보다 클 경우, '최적화된 크기'로 재조정

    // fit에 맞는 free를 찾는다
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize); //찾았다면 할당

        return bp;
    }
    //크기가 맞는 블럭이 없다면, 힙을 늘린다
    extendsize = MAX(asize, CHUNKSIZE); // 둘 중 더 큰값으로 정해서
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) // extend_heap은 워드 단위로 받으니까 wsize로 나눠줌->null이면 확장 안 됨
        return NULL; // 힙 확장이 불가능하니 NULL

    place(bp, asize); //새 힙에 메모리 할당

    return bp; 
}

static void *extend_heap(size_t words)
{

    char *bp;  //블록 포인터
    size_t size;  // 힙 영역의 크기

    // 더블 워드 정렬에 따라 메모리를 mem_sbrk로 할당받음
    // 이때 size는 힙의 총 영역수가 됨
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //words가 홀수라면 1을 더하고 4바이트를 곱하고, 짝수라면 그대로 곱해서 size에 저장
    if((long)(bp = mem_sbrk(size)) == -1) //새 메모리의 첫 부분을 bp로 함. 이때 주소값은 int가 불가능하므로 long으로 캐스팅
        return NULL;

    // 새 free 블록의 헤더와 푸터를 정해주고 epilogue 블록을 free블록 맨 끝으로 옮김
    PUT(HDRP(bp), PACK(size, 0));  //free 블록의 헤더 생성(bp의 바로 앞)
    PUT(FTRP(bp), PACK(size, 0));  //free 블록의 푸터 생성
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //epilogue 블록의 위치 조정

    return coalesce(bp); // 이전 블록이 free 블록이라면 연결, 통합 블록의 포인터 리턴
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // free할 블록의 사이즈를 가져옴

    PUT(HDRP(bp), PACK(size, 0)); //헤더를 free 상태로 변경
    PUT(FTRP(bp), PACK(size, 0)); //푸터를 free 상태로 변경

    coalesce(bp); //앞뒤가 free라면 연결
}

// 해당 free 블록을 앞 뒤 free 블록과 연결하고 주소를 리턴
static void *coalesce(void *bp) // 이때 받아오는 bp는 free 상태 블록의 페이로드를 가리킴
{

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 직전 블록의 푸터가 free인지
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 직후 블록의 헤더가 free인지
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    if(prev_alloc && next_alloc) // case 1 : 직전, 직후 블록이 모두 할당
        return bp; // 불가능하니 즉시 리턴

    else if(prev_alloc && !next_alloc) { // case 2 : 직전 블록 할당, 직후 블록 free
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 직후 블록을 현재 블록과 합친 사이즈
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더값 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록 푸터값 갱신
    }

    else if(!prev_alloc && next_alloc) { // case 3 : 직전 블록 free, 직후 블록 할당
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 직전 블록을 현재 블록과 합친 사이즈 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 직전 블록 헤더값 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록 푸터값 갱신
        bp = PREV_BLKP(bp); // bp를 직전 블록으로 옮김
    }

    else { // case 4 : 둘 다 free
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 다 합침
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 직전 블록 헤더값 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 직후 블록 푸터값 갱신
        bp = PREV_BLKP(bp); // bp를 직전 블록으로 옮김
    }

    last_freep = bp;

    return bp; // 최종 bp값 리턴
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    
    size_t copySize;
    void *newp = mm_malloc(size); 

    copySize = GET_SIZE(HDRP(ptr));
    if(size < copySize) {
    	copySize = size; 
	}
    memcpy(newp, ptr, copySize); 
    mm_free(ptr);
    return newp;
}















