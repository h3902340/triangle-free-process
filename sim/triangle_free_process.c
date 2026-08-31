#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

static uint64_t rs=88172645463325252ULL;
static inline uint64_t rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}

int n; int MAXD;
int *deg, *adj;            /* adjacency lists, n x MAXD */
uint64_t *openbit;         /* bitset over i*n+j */
uint32_t *list; long len;

static inline int isopen(uint32_t idx){return (openbit[idx>>6]>>(idx&63))&1ULL;}
static inline void closep(uint32_t idx){openbit[idx>>6]&=~(1ULL<<(idx&63));}
static inline uint32_t PID(int a,int b){return (a<b)?((uint32_t)a*n+b):((uint32_t)b*n+a);}

int main(int argc,char**argv){
  n=atoi(argv[1]); if(argc>2) rs=strtoull(argv[2],0,10)|1;
  double L=log((double)n);
  MAXD=(int)(6.0*sqrt(n*L))+64;
  deg=calloc(n,sizeof(int));
  adj=malloc((size_t)n*MAXD*sizeof(int));
  size_t nb=((size_t)n*n+63)/64;
  openbit=malloc(nb*8); memset(openbit,0xff,nb*8);
  len=(long)n*(n-1)/2;
  list=malloc((size_t)len*4);
  long t=0;
  for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)list[t++]=(uint32_t)i*n+j;
  long m=0;
  while(len>0){
    long r=(long)(rnd()%(uint64_t)len);
    uint32_t idx=list[r];
    if(!isopen(idx)){ list[r]=list[--len]; continue; }
    int u=idx/n, v=idx%n;
    int du=deg[u],dv=deg[v];
    int *Nu=adj+(size_t)u*MAXD,*Nv=adj+(size_t)v*MAXD;
    for(int a=0;a<du;a++){int w=Nu[a]; if(w!=v) closep(PID(w,v));}
    for(int a=0;a<dv;a++){int w=Nv[a]; if(w!=u) closep(PID(w,u));}
    closep(idx);
    if(du>=MAXD||dv>=MAXD){fprintf(stderr,"MAXD overflow\n");return 1;}
    Nu[deg[u]++]=v; Nv[deg[v]++]=u;
    m++;
  }
  double d=2.0*m/n; int mx=0; for(int i=0;i<n;i++) if(deg[i]>mx) mx=deg[i];
  double s=sqrt(n*L);
  /* greedy independent sets (random order), best of 20 */
  int best=0; char*used=malloc(n); int*perm=malloc(n*sizeof(int)); char*blocked=malloc(n);
  for(int rep=0;rep<20;rep++){
    for(int i=0;i<n;i++)perm[i]=i;
    for(int i=n-1;i>0;i--){int j=rnd()%(uint64_t)(i+1);int tt=perm[i];perm[i]=perm[j];perm[j]=tt;}
    memset(blocked,0,n); int cnt=0;
    for(int a=0;a<n;a++){int x=perm[a]; if(blocked[x])continue; cnt++;
      int*Nx=adj+(size_t)x*MAXD; for(int b=0;b<deg[x];b++) blocked[Nx[b]]=1; }
    if(cnt>best)best=cnt;
  }
  printf("n=%d  m=%ld  avgdeg=%.2f  maxdeg=%d  sqrt(n ln n)=%.2f  d/s=%.4f  maxdeg/s=%.4f  greedyalpha=%d  ga/s=%.4f  m/(n^1.5 sqrt(ln n))=%.4f\n",
    n,m,d,mx,s,d/s,mx/s,best,best/s, m/(pow(n,1.5)*sqrt(L)));
  return 0;
}
