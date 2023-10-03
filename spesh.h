/*
 *   Copyright (c) 2023 Talas
 *   Copyright (c) 2022,2023 ktye
 *
 *  This program is free software: you can redistribute it and/or modify it
 *  under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation, either version 3 of the License,
 *  or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *  See the GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program. If not, see <https://www.gnu.org/licenses/>.
 *
 *  Based on ktye/k and k+, which are in the Public Domain.
 */
#include<stdio.h>
#include<stdlib.h>
#include<stdint.h>
#include<string.h>
#include<math.h>
#include "mathlib.h"
#define SPESH_MAX_MEM 32
#define SPESH_MAX_RECURSION 8
#define SPESH_MAX_OPS 0
typedef int32_t I;
typedef int64_t J;
typedef uint32_t UI;
typedef uint64_t UJ;
typedef char C;
typedef double F; //64 bit double
typedef uint64_t K; // K value
typedef int32_t T; // K type
typedef struct { K a,b,c; I p,e,j; } exec_state;
//   0....7  key
//   8...15  val
//  16...19
//  20..127  free list
// 128..135  src (aligned)
// 256..511  stack
#define POS_SRC 128
#define POS_STACK 256
#define QUOTE 576
static C *M_;
static I  *I_;
static UJ *U_;
static void **Fn_;
static I memorysize_;
static I memorycount_;
static K loc_=0ull, xyz_=0ull;
static I PP=0, PE=0, SP=0, SRCP=0, PS=0; // parse or execution position/end, stack position, src pointer
static I rand_=0;
static I exec_d=0;
static exec_state exec_s[SPESH_MAX_RECURSION+1];
static I ops_=0;

static void Memory(I x){ memorysize_=x; U_=(UJ*)calloc((size_t)x,64*1024); M_=(C*)U_; I_=(I*)U_; }

static I Memorygrow(I delta){
    I r=memorysize_;
    memorysize_+=delta;
    U_=(UJ*)realloc(U_,64*1024*(size_t)memorysize_); M_=(C*)U_; I_=(I*)U_;
    return (U_==NULL) ? -1 : r;
}

#define GetC(x)           (M_[x])
#define GetI(x)           (I_[(x)>>2])
#define GetJ(x)        (J)(U_[(x)>>3])
#define GetF(x)       ((F*)U_)[(x)>>3]
static void SetC(I x,C y){ M_[x]=y; }
static void SetI(I x,I y){ I_[(x)>>2]=y; }
static void SetJ(I x,J y){ U_[(x)>>3]=(UJ)y; }
static void SetF(I x,F y){ ((F*)U_)[(x)>>3]=y; }
static void Memorycopy(I dst, I src, I n){ memcpy(M_ +dst, M_ +src, (size_t)n); }
static void Memoryfill(I p, I v, I n){ memset(M_+p, (int)v, (size_t)n); }
static I Iclz(I x){ return (I)__builtin_clz((unsigned int)x); }
#ifdef SPESH_IO_SYS
static I Read(I file, I nfile, I dst){
    static C *filebuf = NULL;
    static size_t      n = 0;
    if(dst != 0){ memcpy(M_+dst,filebuf,n); return 0; }
    C name[512];
    if(nfile>511) return -1;
    memcpy(name, M_+file, (size_t)nfile);
    name[nfile]=(C)0;
    FILE *fp = fopen(name, "rb");
    if(fp==NULL){ if(filebuf!=NULL)free(filebuf); filebuf=NULL; n=0; return -1; }
    fseek(fp, 0, SEEK_END);
    n=(size_t)ftell(fp);
    fseek(fp, 0, SEEK_SET);
    if(filebuf!=NULL){ free(filebuf); filebuf=NULL; }
    filebuf = malloc(n);
    if(n!=fread(filebuf,1,n,fp)){ fclose(fp); return -1; }
    fclose(fp);
    return (I)n;
}

static I Write(I file, I nfile, I src, I n){
    if(nfile==0){ fwrite(M_+src, 1, (size_t)n, stdout); return 0; }
    C name[512];
    memcpy(name, M_+file, (size_t)nfile);
    name[nfile]=(C)0;
    FILE *fp = fopen(name, "wb");
    if(fp==NULL){ return -1; }
    fwrite(M_+src, 1, (size_t)n, fp);
    fclose(fp);
    return 0;
}

static I ReadIn(I dst, I n){
    C *r = fgets(M_+dst, n, stdin);
    if(r==NULL){ //TODO: eof
      return 0;
    } else {
      const C* found = memchr(M_+dst, '\0', (size_t)n);
      return found ? (I)(found-(M_+dst)) : n;
    }
}
#endif //SPESH_IO_SYS

void panic(I ecode); // Must be defined by user.

static const I E_Err=0;
static const I E_Type=1;
static const I E_Value=2;
static const I E_Index=3;
static const I E_Length=4;
static const I E_Rank=5;
static const I E_Parse=6;
static const I E_Stack=7;
static const I E_Grow=8;
static const I E_Unref=9;
static const I E_Io=10;
static const I E_Limit=11;
static const I E_Nyi=12; // Not yet implemented

K trap(I x);
static void minit(I a, I b){
    I p;
    if(a>30){ trap(E_Grow); } // 1<<a would wrap
    p=(I)(1<<a);
    for(I i=a; i<b; i++, p*=2) {
      if(p<0){ trap(E_Grow); }
      SetI(4*i, p); SetI(p, 0);
    }
    memorycount_=b;
}

static I grow(I p){
    I m,n,g;
    m=memorycount_; // old total mem (log2)
    n=1+(p>>2); // required total mem (log2)
    g=(n>16) ? 1<<(n-16) : 16 ; // grow by 64k blocks
    if(g>SPESH_MAX_MEM){
      g=SPESH_MAX_MEM; if(g<n){ trap(E_Grow); }
    }
    g-=memorysize_;
    if(g>0){ if(Memorygrow(g)<0){ trap(E_Grow); } }
    minit(m,n);
    return n;
}

static I bucket(I size){
    I r=((I)(32) - Iclz(15+size));
    if(r<5){ r=5; }
    return r;
}

static I alloc(I n, I s){
    I t,i,m,a,u;
    if(((J)(n)*(J)(s))>2147483647ll){ trap(E_Grow); }
    t=bucket(n*s);
    i=4*t;
    m=4*memorycount_;
    for(;!GetI(i);){ if(i>=m){ m=4*grow(i); } else { i+=4; } }
    a=GetI(i);
    SetI(i,GetI(a));
    for(I j=i-4;j>=4*t;j=j-4){
      u=(a+((I)(1)<<(j>>2)));
      SetI(u, GetI(j)); SetI(j, u);
    }
    if((a&31)){ trap(E_Unref); } // memory corruption
    return a;
}

static void mfree(I x, I bs){
    if((x&31)){ trap(E_Unref); }
    I t=(4*bs);
    SetI(x,GetI(t)); SetI(t,x);
}

static I sz(T t){
    if(t<16) return 8;
    if(t<19) return 1;
    if(t<21) return 4;
    return 8;
}

K mk(T t, I n){
    if(t<17){ trap(E_Value); }
    K r=(K)((K)(t)<<(K)59ull);
    I x=alloc(n,sz(t));
    SetI(x+12,1); SetI(x+4,n);
    return r | (K)(x+16);
}

static const I nai=(I)0x80000000; // 0N

// typeof(x K): t=x>>59
// isatom:      t<16
// isvector:    t>16
// isflat:      t<22
// basetype:    t&15  0..9
// istagged:    t<5
// haspointers: t>5   (recursive unref)
// elementsize: $[t<19;1;t<21;4;8]
// base t&15		bytes	atom	vector
// ct 		char	 1	2	18
// it 		int	 4	3	19
// st 		symbol	 4	4	20
// ft 		float	 8	5	21
// zt 		complex	(8)	6	22

// dt 		dict	(8)		24
// tt 		table	(8)		25
// cf 		comp	(8)	10
// df 		derived	(8)	11
// pf 		proj	(8)	12
// lf 		lambda	(8)	13

// Lt 		list
// Dt 		dict
// Tt 		table

#define T_ct	2
#define T_it	3
#define T_st	4
#define T_ft	5

#define T_dt	8
#define T_tt	9
#define T_cf	10
#define T_df	11
#define T_pf	12
#define T_lf	13
#define T_xf	14

#define T_Ct	18
#define T_It	19
#define T_St	20
#define T_Ft	21

#define T_Lt	23
#define T_Dt	24
#define T_Tt	25

static const C Types[26] = "vbcisf0ldtmdplx00BCISF0LDT";
static const C Verbs[26] = ":+-*%&|<>=~!,^#_$?@.':/:\\:";

static I isfunc(T t){ return (I)(t==0 || (t<16 && t>T_tt)); }
static K src(void){ return (K)(GetJ(POS_SRC)); }
static K Kc(I x){ return ((K)((UI)(x))|((K)(T_ct)<<59ull)); }
static K Ki(I x){ return ((K)((UI)(x))|((K)(T_it)<<59ull)); }
static K Ks(I x){ return ((K)((UI)(x))|((K)(T_st)<<59ull)); }

static K Kf(F x){
    K r=mk(T_Ft,1); SetF((I)r,x);
    return ((K)((I)(r))|((K)(T_ft)<<59ull));
}

static K l1(K x){
    K r=mk(T_Lt,1); SetJ((I)r,(J)x);
    return r;
}

static K l2t(K x, K y, T t){
    K r=mk(T_Lt,2); SetJ((I)r,(J)x); SetJ(8+(I)r,(J)y);
    return ((K)((UI)(r))|((K)(t)<<59ull));
}

static K l2(K x, K y){ return l2t(x,y,T_Lt); }
static K cat1(K x, K y);
static K l3(K x, K y, K z){ return cat1(l2(x,y),z); }
static T tp(K x){ return (T)((K)(x)>>59ull); }
static I nn(K x){ return GetI((I)(x)-12); }
static I ep(K x){ return (I)(x)+(sz(tp(x))*nn(x)); }
static I arity(K f){ return (tp(f)>T_df) ? nn(f) : 2; }

static I conform(K x, K y){
    I r=2*(I)(tp(x)>16) + (I)(tp(y)>16);
    if(r==3 && nn(x)!=nn(y)){ trap(E_Length); }
    return r;
}

static K rx(K x){
    if(tp(x)<T_ft){ return x; }
    I p=(I)(x)-4;
    SetI(p,1+GetI(p));
    return x;
}

static void dx(K x){
    T t=tp(x);
    if(t<T_ft){ return; }
    I p=(I)(x)-4;
    I rc=GetI(p);
    SetI(p,rc-1);
    if(!rc){ trap(E_Unref); }
    if(rc>1){ return; }
    I n=nn(x);
    if((t&15) > 6) {
      if(t==T_xf || t==T_Dt || t==T_Tt){ n=2; }
      else if(t==T_pf || t==T_lf){ n=3; }
      for(I i=0, xp=(I)x; i<n; i++, xp+=8){ dx((K)GetJ(xp)); }
    }
    mfree(p-12,bucket(sz(t)*n));
}

static void rl(K x){ // ref list elements
    I xp=(I)x, xn=nn(x);
    for(I i=0; i<xn; i++, xp+=8){ rx((K)GetJ(xp)); }
}

static void lfree(K x){ mfree((I)(x)-16, bucket(8*nn(x))); }

static K uspc(K x, T xt, I ny){
    K r=(K)0ull;
    I nx=nn(x), s=sz(xt);
    if(GetI((I)(x)-4)==1 && bucket(s*nx)==bucket(s*(nx+ny))){ r=x; }
    else {
      r=mk(xt, nx+ny);
      Memorycopy((I)r, (I)x, s*nx);
      if(xt==T_Lt){ rl(x); }
      dx(x);
    }
    SetI((I)(r)-12, nx+ny);
    return r;
}

static K x0(K x){ return rx((K)GetJ((I)x)); }
static K x1(K x){ return x0(x+8ull); }
static K x2(K x){ return x0(x+16ull); }
static K x3(K x){ return x0(x+24ull); }
static K r0(K x){ K r=x0(x); dx(x); return r; }
static K r1(K x){ K r=x1(x); dx(x); return r; }
static K r3(K x){ K r=x3(x); dx(x); return r; }

static K uptype(K x, T dst){
    T xt=tp(x);
    I xp=(I)x;
    if((xt&15)==dst){ return x; }
    if(xt<16){
      if(dst==T_ct){ return Kc(xp); }
      if(dst==T_it){ return Ki(xp); }
      if(dst==T_ft){ return Kf((F)xp); }
      return trap(E_Type);
    }
    if(xt<T_It && dst==T_ft){
      x=uptype(x,T_it);
      xt=T_It;
      xp=(I)x;
    }
    I xn=nn(x);
    K r=mk(dst+16,xn);
    I rp=(I)r;
    if(dst==T_it){
      for(I i=0;i<xn;i++, xp++, rp+=4){ SetI(rp,GetC(xp)); }
    } else if(dst==T_ft){
      for(I i=0;i<xn;i++, xp+=4, rp+=8){ SetF(rp,(F)GetI(xp)); }
    } else { trap(E_Type); }
    dx(x);
    return r;
}

static K KCn(const C *x, I n){
    K r = mk(T_Ct, n);
    if(x)memcpy(M_+(I)r, x, (size_t)n);
    return r;
}

static K KC(const C *x){ return KCn(x, (I)strlen(x)); }

static K Ku(UJ x){
    K r=mk(T_Ct,0);
    I p=(I)r;
    for(;(x!=0ull); p++){
      SetC(p,(C)x);
      x=(x>>(UJ)8ull);
    }
    SetI((I)(r)-12,p-(I)(r));
    return r;
}

static K Asn(K x, K y){
    if(tp(x)!=T_st){ trap(E_Type); }
    I vp=GetI(8)+(I)x;
    dx((K)GetJ(vp));
    SetJ(vp, (J)rx(y));
    return y;
}

static K ucats(K x){
    K xi,r;
    I xn=nn(x),xp,rn=0,s;
    T rt=0, t;
    if(!xn){ return x; }
    xp=(I)x;
    for(I i=0;i<xn;i++, rn+=nn(xi), xp+=8){
      xi=(K)GetJ(xp);
      t=tp(xi);
      if(!i){ rt=t; }
      if(rt!=t || rt<16 || t>=T_Lt){ return 0ull; }
    }
    r=mk(rt,rn);
    s=sz(rt);
    xp=(I)x;
    for(I i=0, rp=(I)r; i<xn; i++, rp+=rn, xp+=8){
      xi=(K)GetJ(xp);
      rn=s*nn(xi);
      Memorycopy(rp,(I)xi,rn);
    }
    dx(x); return r;
}

static K use1(K x){ return (GetI((I)(x)-4)==1) ? rx(x) : mk(tp(x),nn(x)); }
static K use2(K x, K y){ return (GetI((I)(y)-4)==1) ? rx(y) : use1(x); }

static K use(K x){
    T xt=tp(x);
    if(xt<16 || xt>T_Lt){ trap(E_Type); }
    if(GetI((I)(x)-4)==1){ return x; }
    I nx=nn(x);
    K r=mk(xt,nx);
    Memorycopy((I)r,(I)x,sz(xt)*nx);
    if(xt==T_Lt){ rl(r); }
    dx(x); return r;
}

static K missing(T t){
    switch(t){
      case T_ct: return Kc(32);
      case T_it: return Ki(nai);
      case T_st: return Ks(0);
      case T_ft: return Kf(F64na);
      default: return mk(T_Ct,0);
    }
}

static K ov0(K f, K x){
    dx(f); dx(x);
    return missing(tp(x));
}

static I match(K x, K y);
K sc(K c){
    K x=(K)GetJ(0);
    I xp=(I)x, xn=nn(x);
    for(I i=0;i<xn;i++, xp+=8){
      if(match(c,(K)GetJ(xp))){
        dx(c);
        return (K)(xp-(I)x) | ((K)(T_st)<<59ull);
      }
    }
    SetJ(0,(J)cat1(x,c));
    SetJ(8,(J)cat1((K)GetJ(8),0ull));
    return (K)((8*xn)) | ((K)(T_st)<<59ull);
}

static K cs(K x){ return x0((K)(GetI(0))+x); }

// forward decls for common functions
static K nd(I f, I ff, K x, K y);
static K nf(I f, K x, K y);
static K nm(I f, K x);
static K nc(I f, I ff, K x, K y);
static K Kst(K x);
static K ntake(I n, K y);
static K ndrop(I n, K y);

#ifdef SPESH_IO_SYS
static K readfile(K x){
    K r=(K)0ull;
    if(!nn(x)){
      r=mk(T_Ct,496);
      return ntake(ReadIn((I)r,496),r);
    }
    I n=Read((I)x,nn(x),0);
    if(n<0){
      dx(x); return mk(T_Ct,0);
    }
    r=mk(T_Ct,n);
    Read((I)x,nn(x),(I)r);
    dx(x); return r;
}
#ifdef SPESH_IO_VERBS
static K writefile(K x, K y){
    I r=Write((I)x, nn(x), (I)y, nn(y));
    if(r){ trap(E_Io); }
    dx(x); return y;
}
#endif //SPESH_IO_VERBS
static K read(void){
    K r=mk(T_Ct,504);
    return ntake(ReadIn((I)r,504),r);
}

static void write(K x){
    Write(0,0,(I)x,nn(x));
    dx(x);
}

static K Out(K x){
    write(cat1(Kst(rx(x)),Kc('\n')));
    return x;
}

static K Otu(K x, K y){
    write(cat1(Kst(x),Kc(':')));
    return Out(y);
}
#else //!SPESH_IO_SYS
static K Out(K x){ return x; }
static K Otu(K x, K y){ dx(x); return Out(y); }
#endif //SPESH_IO_SYS

static I maxi(I x, I y){ return (x>y) ? x : y; }
static F maxf(F x, F y){ return F64max(x,y); }

static K Max(K x, K y){
    if(tp(y)<16){  return nd(289,7,y,x); }
    return nd(289,7,x,y);
}

static void maxcC(C x, I yp, I rp, I e){ do{ SetC(rp,(C)maxi(x,GetC(yp))); }while(yp++, rp++, rp<e); }
static void maxiI(I x, I yp, I rp, I e){ do{ SetI(rp,maxi(x,GetI(yp))); }while(yp+=4, rp+=4, rp<e); }
static void maxfF(F x, I yp, I rp, I e){ do{ SetF(rp,F64max(x,GetF(yp))); }while(yp+=8, rp+=8, rp<e); }
static void maxC(I xp, I yp, I rp, I e){ do{ SetC(rp,(C)maxi(GetC(xp),GetC(yp))); }while(xp++, yp++, rp++, rp<e); }
static void maxI(I xp, I yp, I rp, I e){ do{ SetI(rp,maxi(GetI(xp),GetI(yp))); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void maxF(I xp, I yp, I rp, I e){ do{ SetF(rp,F64max(GetF(xp),GetF(yp))); }while(xp+=8, yp+=8, rp+=8, rp<e); }

static K max(I yp, T t, I n){
    F f;
    I xp=0;
    switch (t) {
      case T_Ct:
        xp=-128;
        for(I i=0; i<n; i++) xp=maxi(xp,GetC(yp+i));
        return Kc(xp);
      case T_It:
        xp=nai;
        for(I i=0; i<n; i++, yp+=4){ xp=maxi(xp,GetI(yp)); }
        return Ki(xp);
      case T_St:
        for(I i=0; i<n; i++, yp+=4){ xp=maxi(xp,GetI(yp)); }
        return Ks(xp);
      case T_Ft:
        f=F64reinterpret_i64((UJ)0xfff0000000000000ull);
        for(I i=0; i<n; i++, yp+=8){ f=F64max(f,GetF(yp)); }
        return Kf(f);
      default: return 0ull;
    }
}

static T maxtype(K x, K y){
    T t=(T)maxi((I)(tp(x)&15), (I)(tp(y)&15));
    return t ? t : T_it;
}

static K Min(K x, K y){
    if(tp(y)<16){ return nd(278,6,y,x); }
    return nd(278,6,x,y);
}

static I mini(I x, I y){ return (x<y) ? x : y; }
static F minf(F x, F y){ return F64min(x,y); }
static void mincC(C x, I yp, I rp, I e){ do{ SetC(rp,(C)mini(x,GetC(yp))); }while(yp++, rp++, rp<e); }
static void miniI(I x, I yp, I rp, I e){ do{ SetI(rp,mini(x,GetI(yp))); }while(yp+=4, rp+=4, rp<e); }
static void minfF(F x, I yp, I rp, I e){ do{ SetF(rp,minf(x,GetF(yp))); }while(yp+=8, rp+=8, rp<e); }
static void minC(I xp, I yp, I rp, I e){ do{ SetC(rp,(C)mini(GetC(xp),GetC(yp))); }while(xp++, yp++, rp++, rp<e); }
static void minI(I xp, I yp, I rp, I e){ do{ SetI(rp,mini(GetI(xp),GetI(yp))); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void minF(I xp, I yp, I rp, I e){ do{ SetF(rp,minf(GetF(xp),GetF(yp))); }while(xp+=8, yp+=8, rp+=8, rp<e); }

static K min(I yp, T t, I n){
    F f;
    I xp=0;
    switch (t) {
      case T_Ct:
        xp=127;
        for(I i=0; i<n; i++) xp=mini(xp,GetC(yp+i));
        return Kc(xp);
      case T_It:
        xp=2147483647;
        for(I i=0; i<n; i++, yp+=4){ xp=mini(xp,GetI(yp)); }
        return Ki(xp);
      case T_St:
        xp=(nn((K)GetJ(8))<<3) - 8;
        for(I i=0; i<n; i++, yp+=4){ xp=mini(xp,GetI(yp)); }
        return Ks(xp);
      case T_Ft:
        f=F64reinterpret_i64((UJ)0x7ff0000000000000ull);
        for(I i=0; i<n; i++, yp+=8){ f=F64min(f,GetF(yp)); }
        return Kf(f);
      default: return 0ull;
    }
}

static K Add(K x, K y){
    if(tp(y)<16){ return nd(234,2,y,x); }
    return nd(234,2,x,y);
}

static I addi(I x, I y){ return (x+y); }
static F addf(F x, F y){ return (x+y); }
static void addcC(C x, I yp, I rp, I e){ do{ SetC(rp,x+GetC(yp)); }while(yp++, rp++, rp<e); }
static void addiI(I x, I yp, I rp, I e){ do{ SetI(rp,x+GetI(yp)); }while(yp+=4, rp+=4, rp<e); }
static void addfF(F x, I yp, I rp, I e){ do{ SetF(rp,x+GetF(yp)); }while(yp+=8, rp+=8, rp<e); }
static void addC(I xp, I yp, I rp, I e){ do{ SetC(rp,GetC(xp)+GetC(yp)); }while(xp++, yp++, rp++, rp<e); }
static void addI(I xp, I yp, I rp, I e){ do{ SetI(rp,GetI(xp)+GetI(yp)); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void addF(I xp, I yp, I rp, I e){ do{ SetF(rp,GetF(xp)+GetF(yp)); }while(xp+=8, yp+=8, rp+=8, rp<e); }
static K Neg(K x){ return nm(220,x); } // 220=negi
static I negi(I x){ return -x; }
static F negf(F x){ return -x; }
static void negC(I xp, I rp, I e){ do{ SetC(rp,-GetC(xp)); }while(xp++, rp++, rp<e); }
static void negI(I xp, I rp, I e){ do{ SetI(rp,-GetI(xp)); }while(xp+=4, rp+=4, rp<e); }
static void negF(I xp, I rp, I e){ do{ SetF(rp,-GetF(xp)); }while(xp+=8, rp+=8, rp<e); }

static K Sub(K x, K y){
    if(tp(y)<16){ return nd(234,2,Neg(y),x); }
    return nd(245,3,x,y);
}

static I subi(I x, I y){ return (x-y); }
static F subf(F x, F y){ return (x-y); }
static void subcC(C x, I yp, I rp, I e){ do{ SetC(rp,x-GetC(yp)); }while(yp++, rp++, rp<e); }
static void subiI(I x, I yp, I rp, I e){ do{ SetI(rp,x-GetI(yp)); }while(yp+=4, rp+=4, rp<e); }
static void subfF(F x, I yp, I rp, I e){ do{ SetF(rp,x-GetF(yp)); }while(yp+=8, rp+=8, rp<e); }
static void subC(I xp, I yp, I rp, I e){ do{ SetC(rp,GetC(xp)-GetC(yp)); }while(xp++, yp++, rp++, rp<e); }
static void subI(I xp, I yp, I rp, I e){ do{ SetI(rp,GetI(xp)-GetI(yp)); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void subF(I xp, I yp, I rp, I e){ do{ SetF(rp,GetF(xp)-GetF(yp)); }while(xp+=8, yp+=8, rp+=8, rp<e); }

static K Mul(K x, K y){
    T yt=tp(y);
    if(yt<16){ return nd(256,4,y,x); } // 256=muli
    return nd(256,4,x,y);
}

static I muli(I x, I y){ return (x*y); }
static F mulf(F x, F y){ return (x*y); }
static void mulcC(C x, I yp, I rp, I e){ do{ SetC(rp,x*GetC(yp)); }while(yp++, rp++, rp<e); }
static void muliI(I x, I yp, I rp, I e){ do{ SetI(rp,x*GetI(yp)); }while(yp+=4, rp+=4, rp<e); }
static void mulfF(F x, I yp, I rp, I e){ do{ SetF(rp,x*GetF(yp)); }while(yp+=8, rp+=8, rp<e); }
static void mulC(I xp, I yp, I rp, I e){ do{ SetC(rp,GetC(xp)*GetC(yp)); }while(xp++, yp++, rp++, rp<e); }
static void mulI(I xp, I yp, I rp, I e){ do{ SetI(rp,GetI(xp)*GetI(yp)); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void mulF(I xp, I yp, I rp, I e){ do{ SetF(rp,GetF(xp)*GetF(yp)); }while(xp+=8, yp+=8, rp+=8, rp<e); }

static K scale(F s, K x){
    K r;
    if(tp(x)<T_Ft){ x=uptype(x,T_ft); }
    r=use1(x);
    if(nn(r)){ mulfF(s,(I)x,(I)r,ep(r)); }
    dx(x); return r;
}

static I divi(I x, I y){return (x/y);}
static F divf(F x, F y){return (x/y);}
static void divfF(F x, I yp, I rp, I e){ do{ SetF(rp,x/GetF(yp)); }while(yp+=8, rp+=8, rp<e); }
static void divF(I xp, I yp, I rp, I e){ do{ SetF(rp,GetF(xp)/GetF(yp)); }while(rp+=8, xp+=8, yp+=8, rp<e); }

static void divIi(I xp, I yp, I e){
    I s=(I)(31) - Iclz(yp);
    if(yp==((I)(1)<<s)){
      do{ SetI(xp,GetI(xp)>>s); }while(xp+=4, xp<e);
    } else {
      for(; xp<e; xp+=4){ SetI(xp,GetI(xp)/yp); }
    }
}

static K idiv(K x, K y, I mod){
    I av,xp,yp,rp,e,xn;
    K r=(K)0ull;
    T t=maxtype(x,y);
    x=uptype(x,t); y=uptype(y,t);
    av=conform(x,y);
    if(t!=T_it){ trap(E_Type); }
    xp=(I)x; yp=(I)y;
    switch (av) {
      case 0: return mod ? Ki(xp%yp) : Ki(xp/yp);
      case 1:
        r=use(y);
        rp=(I)r;
        e=rp+4*nn(r);
        if(mod){ for(;rp<e; rp+=4){ SetI(rp, xp%GetI(rp)); } }
        else { for(;rp<e; rp+=4){ SetI(rp, xp/GetI(rp)); } }
        return r;
      case 2:
        x=use(x);
        xp=(I)x;
        xn=nn(x);
        e=xp+4*xn;
        if(yp>0 && xn>0 && mod==0){ divIi(xp,yp,e); }
        if(mod){ for(;xp<e; xp+=4){ SetI(xp,GetI(xp)%yp); } }
        return x;
      default:
        r=use2(x,y);
        rp=(I)r;
        e=rp+4*nn(r);
        if(mod){ for(;rp<e; xp+=4, yp+=4, rp+=4){ SetI(rp,GetI(xp)%GetI(yp)); } }
        else { for(;rp<e; xp+=4, yp+=4, rp+=4){ SetI(rp,GetI(xp)/GetI(yp)); } }
        dx(x); dx(y);
        return r;
    }
}

static K Mod(K x, K y){
    T xt=tp(x),yt=tp(y);
    if((xt&15)<T_ft && (yt&15)<T_ft){ return idiv(x,y,1); }
    return (xt>=T_Lt || yt>=T_Lt) ? nd(0,41,x,y): trap(E_Type);
}

static K Div(K x, K y){
    F s;
    T xt=tp(x),yt=tp(y);
    if((xt&15)<T_ft && (yt&15)<T_ft){ return idiv(x,y,0); }
    if(yt<16 && xt>16 && xt<T_Lt){
      if(yt<T_ft){ y=uptype(y,T_ft); }
      s=1. / GetF((I)y);
      dx(y);
      return scale(s,x);
    }
    return nd(267,5,x,y);
}

static I eqi(I x, I y){ return (I)(x==y); }
static I eqf(F x, F y){ return (I)((x!=x && y!=y) || F64eq(x,y)); }
static void eqcC(I v, I yp, I rp, I e){ do{ SetI(rp,(I)(v==GetC(yp))); }while(yp++, rp+=4, rp<e); }
static void eqiI(I x, I yp, I rp, I e){ do{ SetI(rp,(I)(x==GetI(yp))); }while(yp+=4, rp+=4, rp<e); }
static void eqfF(F x, I yp, I rp, I e){ do{ SetI(rp,eqf(x,GetF(yp))); }while(yp+=8, rp+=4, rp<e); }
static void eqCc(I xp, I y, I rp, I e){ eqcC(y,xp,rp,e); }
static void eqIi(I xp, I y, I rp, I e){ eqiI(y,xp,rp,e); }
static void eqFf(I xp, F y, I rp, I e){ eqfF(y,xp,rp,e); }
static void eqC(I xp, I yp, I rp, I e){ do{ SetI(rp,(I)(GetC(xp)==GetC(yp))); }while(xp++, yp++, rp+=4, rp<e); }
static void eqI(I xp, I yp, I rp, I e){ do{ SetI(rp,(I)(GetI(xp)==GetI(yp))); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void eqF(I xp, I yp, I rp, I e){ do{ SetI(rp,eqf(GetF(xp),GetF(yp))); }while(xp+=8, yp+=8, rp+=4, rp<e); }

static K Eql(K x, K y){ return nc(308,10,x,y); }
static K Mor(K x, K y){ return nc(338,9,x,y); }

static K Les(K x, K y){
    if(tp(x)==T_st && tp(y)==T_Ct){
      if(!(I)x){
#ifdef SPESH_IO_SYS
        write(rx(y));
#endif //SPESH_IO_SYS
        return y;
      }
#ifdef SPESH_IO_VERBS
      return writefile(cs(x),y);
#else //!SPESH_IO_VERBS
      return trap(E_Io);
#endif //SPESH_IO_VERBS
    }
    return nc(323,8,x,y);
}

static I lti(I x, I y){ return (I)(x<y); }
static I ltf(F x, F y){ return (I)(x<y || x!=x); }
static void ltcC(I v, I yp, I rp, I e){ do{ SetI(rp,(I)(v<GetC(yp))); }while(yp++, rp+=4, rp<e); }
static void ltiI(I x, I yp, I rp, I e){ do{ SetI(rp,(I)(x<GetI(yp))); }while(yp+=4, rp+=4, rp<e); }
static void ltfF(F x, I yp, I rp, I e){ do{ SetI(rp,ltf(x,GetF(yp))); }while(yp+=8, rp+=4, rp<e); }
static void ltCc(I xp, I v, I rp, I e){ do{ SetI(rp,(I)(GetC(xp)<v)); }while(xp++, rp+=4, rp<e); }
static void ltIi(I xp, I y, I rp, I e){ do{ SetI(rp,(I)(GetI(xp)<y)); }while(xp+=4, rp+=4, rp<e); }
static void ltFf(I xp, F y, I rp, I e){ do{ SetI(rp,ltf(GetF(xp),y)); }while(xp+=8, rp+=4, rp<e); }
static void ltC(I xp, I yp, I rp, I e){ do{ SetI(rp,(I)(GetC(xp)<GetC(yp))); }while(xp++, yp++, rp+=4, rp<e); }
static void ltI(I xp, I yp, I rp, I e){ do{ SetI(rp,(I)(GetI(xp)<GetI(yp))); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void ltF(I xp, I yp, I rp, I e){ do{ SetI(rp,ltf(GetF(xp),GetF(yp))); }while(xp+=8, yp+=8, rp+=4, rp<e); }

static I gti(I x, I y){ return (I)(x>y); }
static I gtf(F x, F y){ return (I)(x>y || y!=y); }
static void gtcC(I v, I yp, I rp, I e){ do{ SetI(rp,(I)(v>GetC(yp))); }while(yp++, rp+=4, rp<e); }
static void gtiI(I x, I yp, I rp, I e){ do{ SetI(rp,(I)(x>GetI(yp))); }while(yp+=4, rp+=4, rp<e); }
static void gtfF(F x, I yp, I rp, I e){ do{ SetI(rp,gtf(x,GetF(yp))); }while(yp+=8, rp+=4, rp<e); }
static void gtCc(I xp, I v, I rp, I e){ do{ SetI(rp,(I)(GetC(xp)>v)); }while(xp++, rp+=4, rp<e); }
static void gtIi(I xp, I y, I rp, I e){ do{ SetI(rp,(I)(GetI(xp)>y)); }while(xp+=4, rp+=4, rp<e); }
static void gtFf(I xp, F y, I rp, I e){ do{ SetI(rp,gtf(GetF(xp),y)); }while(xp+=8, rp+=4, rp<e); }
static void gtC(I xp, I yp, I rp, I e){ do{ SetI(rp,(I)(GetC(xp)>GetC(yp))); }while(xp++, yp++, rp+=4, rp<e); }
static void gtI(I xp, I yp, I rp, I e){ do{ SetI(rp,(I)(GetI(xp)>GetI(yp))); }while(xp+=4, yp+=4, rp+=4, rp<e); }
static void gtF(I xp, I yp, I rp, I e){ do{ SetI(rp,gtf(GetF(xp),GetF(yp))); }while(xp+=8, yp+=8, rp+=4, rp<e); }

static K Sin(K x){ return nf(44,x,0ull); }
static K Cos(K x){ return nf(39,x,0ull); }
static K Exp(K x){ return nf(42,x,0ull); }
static K Log(K x){ return nf(43,x,0ull); }

static K ipow(K x, I y){
    K r;
    I n,rp,xp,e;
    if(tp(x)==T_It){
      n=nn(x);
      r=mk(T_It,n);
      rp=(I)r; xp=(I)x;
      e=rp+4*n;
      for(;rp<e; xp+=4, rp+=4){ SetI(rp, iipow(GetI(xp),y)); }
      dx(x); return r;
    } else {
      return Ki(iipow((I)x,y));
    }
}

static K Pow(K y, K x){
    if((tp(x)&15)==T_it && tp(y)==T_it && (I)(y)>=0){ return ipow(x,(I)y); }
    return nf(106,x,y);
}

static F fk(K x){
    T t=tp(x);
    if(t==T_it){ return (F)((I)x); }
    if(t!=T_ft){ trap(E_Type); }
    dx(x);
    return GetF((I)x);
}

static K Lgn(K x, K y){
    F xf=fk(x);
    if(F64eq(xf,10.)){ xf=0.4342944819032518; }
    else { xf=(F64eq(xf,2.)) ? 1.4426950408889634 : 1./log_(xf); }
    return Mul(Kf(xf),Log(y));
}

static I maxcount(I xp, I n){
    K x;
    I r=0;
    for(I i=0; i<n; i++, xp+=8){
      x=(K)GetJ(xp);
      r=tp(x)<16 ? maxi(1,r) : maxi(nn(x),r);
    }
    return r;
}

static T dtypes(K x, K y){ return (T)maxi((I)tp(x),(I)tp(y)); }
static K dkeys(K x, K y){ return (tp(x)>T_Lt) ? x0(x) : x0(y); }
static K dvals(K x){ return (tp(x)>T_Lt) ? r1(x) : x; }

static K seq(I n){
    n=maxi(n,0);
    K r=mk(T_It,n);
    if(!n){ return r; }
    I p=(I)r,e=ep(r),i=0;
    do{ SetI(p,i++); }while(p+=4, p<e);
    return r;
}

static K Til(K x);
static K key(K x, K y, T t);
static K Flp(K x);
static K Ech(K f, K x);
static K ufd(K x){
    K r=Til(x0(x));
    if(tp(r)!=T_St){
      dx(r); return x;
    }
    I n=nn(x),xp=(I)x;
    for(I i=0; i<n; i++, xp+=8){
      if(!match(r,(K)GetJ((I)GetJ(xp)))){
        dx(r); return x;
      }
    }
    return key(r,Flp(Ech(20ull,l1(x))),T_Tt); // monad 20 = Val
}

static K uf(K x){
    K r;
    T rt=(T)0,t;
    I xn=nn(x),xp=(I)x,rp;
    for(I i=0; i<xn; i++, xp+=8){
      t=tp((K)GetJ(xp));
      if(!i){ rt=t; }
      else if(t!=rt){ return x; }
    }
    if(rt==T_Dt){ return ufd(x); }
    if((rt==0)||(rt>T_ft)){ return x; }
    rt+=16;
    r=mk(rt,xn);
    rp=(I)r; xp=(I)x;
    switch(sz(rt)>>2){
      case 0: for(I i=0; i<xn; i++, xp+=8, rp++){ SetC(rp,GetC(xp)); }
        break;
      case 1: for(I i=0; i<xn; i++, xp+=8, rp+=4){ SetI(rp,GetI(xp)); }
        break;
      case 2: for(I i=0; i<xn; i++, xp+=8, rp+=8){ SetJ(rp,GetJ(GetI(xp))); }
        break;
    }
    dx(x); return r;
}

static K stv(K x, K i, K y){
    I n,xn,s,xp,yp,ip;
    T xt;
    UI xi;
    if(T_It!=tp(i)){ trap(E_Type); }
    n=nn(i);
    if(!n){
      dx(y); dx(i);
      return x;
    }
    if(n!=nn(y)){ trap(E_Length); }
    x=use(x); xt=tp(x); xn=nn(x);
    s=sz(xt);
    xp=(I)x; yp=(I)y; ip=(I)i;
    for(I j=0;j<n;j++){
      xi=(UI)GetI(ip+4*j);
      if(xi>=(UI)xn){ trap(E_Index); }
    }
    switch(s>>2){
      case 0: for(I j=0; j<n; j++, ip+=4, yp++){ SetC(xp+GetI(ip), GetC(yp)); }
        break;
      case 1: for(I j=0; j<n; j++, ip+=4, yp+=4){ SetI(xp+4*GetI(ip), GetI(yp)); }
        break;
      case 2:
        if(xt==T_Lt){
          rl(y);
          for(I j=0;j<n;j++, ip+=4){ dx((K)GetJ(xp+8*GetI(ip))); }
          ip=(I)(i);
        }
        for(I j=0;j<n;j++, ip+=4, yp+=8){ SetJ(xp+8*GetI(ip),GetJ(yp)); }
        if(xt==T_Lt){ x=uf(x); }
        break;
    }
    dx(i); dx(y);
    return x;
}

static K sti(K x, I i, K y){
    I xn,s,xp,yp;
    x=use(x);
    T xt=tp(x);
    xn=nn(x);
    if(i<0 || i>=xn){ trap(E_Index); }
    s=sz(xt);
    xp=(I)x; yp=(I)y;
    switch(s>>2){
      case 0: SetC(xp+i, (C)yp); break;
      case 1: SetI(xp+4*i, yp); break;
      case 2:
        xp+=8*i;
        if(xt==T_Lt){
          dx((K)GetJ(xp));
          SetJ(xp,(J)rx(y));
          x=uf(x);
        } else {
          SetJ(xp,GetJ(yp));
        }
        break;
    }
    dx(y); return x;
}

static K Val(K x);
static K ati(K x, I i);
static K Fst(K x){
    T t=tp(x);
    if(t<16){ return x; }
    return (t==T_Dt) ? Fst(Val(x)) : ati(x,0);
}

static K Las(K x){
    T t=tp(x);
    if(t<16){ return x; }
    if(t==T_Dt){ x=Val(x); }
    I n=nn(x);
    return (!n) ? Fst(x) : ati(x,(n-1));
}

static K Cnt(K x){
    T t=tp(x);
    dx(x);
    return (t<16) ? Ki(1) : Ki(nn(x));
}

static K Not(K x){ return ((tp(x)&15)==T_st) ? Eql(Ks(0),x) : Eql(Ki(0),x); }

static void ff(I f, I rp, I xp, I n, F yf){
    I e=xp+8*n;
    switch(f-42){
      case 0: do{ SetF(rp,exp_(GetF(xp))); }while(rp+=8, xp+=8, xp<e);
        break;
      case 1: do{ SetF(rp,log_(GetF(xp))); }while(rp+=8, xp+=8, xp<e);
        break;
      default:
        if(f==106){
          do{ SetF(rp,pow_(GetF(xp),yf)); }while(rp+=8, xp+=8, xp<e);
        } else {
          do{ SetF(rp, cosin_(GetF(xp),(1+(I)(f==39)))); }while(rp+=8, xp+=8, xp<e); //39=Cos
        }
        break;
    }
}

static K nf(I f, K x, K y){
    I xp,xn;
    F yf=0.;
    K r=(K)0ull;
    T xt=tp(x);
    if(xt>=T_Lt){ return (y==0ull) ? (Ech((K)f,l1(x))) : (Ech((K)(f-64),l2(y,x))); }
    if(y!=0ull){ yf=fk(y); }
    if((xt&15)<T_ft){
      x=uptype(x,T_ft); xt=tp(x);
    }
    xp=(I)x;
    if(xt==T_ft){
      r=Kf(0.);
      ff(f,(I)r,xp,1,yf);
    } else {
      xn=nn(x);
      r=mk(T_Ft,xn);
      if(xn>0){ ff(f,(I)r,xp,xn,yf); }
    }
    dx(x); return r;
}

static K nm(I f, K x){
    I xp,n,rp,e;
    K r=(K)0ull;
    T xt=tp(x);
    if(xt>T_Lt){
      r=x0(x);
      return key(r,nm(f,r1(x)),xt);
    }
    xp=(I)x;
    if(xt==T_Lt){
      n=nn(x);
      r=mk(T_Lt,n); rp=(I)r;
      for(I i=0;i<n;i++, xp+=8, rp+=8){ SetJ(rp,(J)nm(f,x0((K)xp))); }
      dx(x); return uf(r);
    }
    if(xt<16){
      switch (xt) {
        case T_ct: return Kc(((I(*)(I))Fn_[f])(xp));
        case T_it: return Ki(((I(*)(I))Fn_[f])(xp));
        case T_ft:
          r=Kf(((F(*)(F))Fn_[1+f])(GetF(xp)));
          dx(x);
          return r;
        default: return trap(E_Type);
      }
    }
    r=use1(x); rp=(I)r;
    e=ep(r);
    if(e==rp){
      dx(x); return r;
    }
    switch(xt){
      case T_Ct: ((void(*)(I,I,I))Fn_[3+f])(xp,rp,e); break;
      case T_It: ((void(*)(I,I,I))Fn_[4+f])(xp,rp,e); break;
      case T_St: trap(E_Type); break;
      case T_Ft: ((void(*)(I,I,I))Fn_[5+f])(xp,rp,e); break;
    }
    dx(x); return r;
}

static K nd(I f, I ff, K x, K y){
    I av,xp,yp,e,rp;
    K r=(K)0ull;
    T t=dtypes(x,y);
    if(t>T_Lt){
      r=dkeys(x,y);
      return key(r,((K(*)(K,K))Fn_[64+ff])(dvals(x),dvals(y)),t);
    }
    if(t==T_Lt){ return Ech((K)(ff),l2(x,y)); }
    t=maxtype(x,y);
    x=uptype(x,t); y=uptype(y,t);
    av=conform(x,y);
    xp=(I)x; yp=(I)y;
    if(!av){
      switch(t){
        case T_ct: return Kc(((I(*)(I ,I))Fn_[f])(xp,yp));
        case T_it: return Ki(((I(*)(I ,I))Fn_[f])(xp,yp));
        case T_st: return trap(E_Type);
        case T_ft:
          dx(x); dx(y);
          return Kf(((F(*)(F,F))Fn_[1+f])(GetF(xp),GetF(yp)));
      }
    }
    if(av==1){
      r=use1(y);
      if(!nn(r)){
        dx(x); dx(y);
        return r;
      }
      e=ep(r);
      yp=(I)y; rp=(I)r;
      switch(t){
        case T_ct: ((void(*)(I,I,I,I))Fn_[3+f])(xp,yp,rp,e); break;
        case T_it: ((void(*)(I,I,I,I))Fn_[4+f])(xp,yp,rp,e); break;
        case T_st: trap(E_Type); break;
        case T_ft: ((void(*)(F,I,I,I))Fn_[5+f])(GetF(xp),yp,rp,e); break;
      }
      dx(x); dx(y);
      return r;
    } else {
      r=use2(x,y);
      if(!nn(r)){
        dx(x); dx(y);
        return r;
      }
      rp=(I)r; xp=(I)x; yp=(I)y;
      e=ep(r);
      switch(t){
        case T_ct: ((void(*)(I,I,I,I))Fn_[7+f])(xp,yp,rp,e); break;
        case T_it: ((void(*)(I,I,I,I))Fn_[8+f])(xp,yp,rp,e); break;
        case T_st: trap(E_Type); break;
        case T_ft: ((void(*)(I,I,I,I))Fn_[9+f])(xp,yp,rp,e); break;
      }
      dx(x); dx(y);
      return r;
    }
}

static K nc(I f, I ff, K x, K y){
    I av,xp,yp,yn,rp,e,xn,n;
    K r=(K)0ull;
    T t=dtypes(x,y);
    if(t>T_Lt){
      r=dkeys(x,y);
      return key(r,nc(f,ff,dvals(x),dvals(y)),t);
    }
    if(t==T_Lt){ return Ech((K)ff,l2(x,y)); }
    t=maxtype(x,y);
    x=uptype(x,t); y=uptype(y,t);
    av=conform(x,y);
    xp=(I)x; yp=(I)y;
    if(!av){
      switch (t) {
        case T_ct: return Ki(((I(*)(I,I))Fn_[f])(xp,yp));
        case T_it: return Ki(((I(*)(I,I))Fn_[f])(xp,yp));
        case T_st: return Ki(((I(*)(I,I))Fn_[f])(xp,yp));
        case T_ft:
          dx(x); dx(y);
          return Ki(((I(*)(F,F))Fn_[1+f])(GetF(xp),GetF(yp)));
      }
      return trap(E_Type);
    } else if(av==1){
      yn=nn(y);
      r=mk(T_It,yn);
      if(!yn){
        dx(x); dx(y);
        return r;
      }
      rp=(I)(r);
      e=ep(r);
      switch(t){
        case T_ct: ((void(*)(I,I,I,I))Fn_[3+f])(xp,yp,rp,e); break;
        case T_it: ((void(*)(I,I,I,I))Fn_[4+f])(xp,yp,rp,e); break;
        case T_st: ((void(*)(I,I,I,I))Fn_[4+f])(xp,yp,rp,e); break;
        case T_ft:
          dx(x);
          ((void(*)(F,I,I,I))Fn_[5+f])(GetF(xp),yp,rp,e);
          break;
      }
      dx(y); return r;
    } else if(av==2){
      xn=nn(x);
      r=mk(T_It,xn);
      if(!xn){
        dx(x); dx(y);
        return r;
      }
      rp=(int32_t)r;
      e=ep(r);
      switch(t){
        case T_ct: ((void(*)(I,I,I,I))Fn_[7+f])(xp,yp,rp,e); break;
        case T_it: ((void(*)(I,I,I,I))Fn_[8+f])(xp,yp,rp,e); break;
        case T_st: ((void(*)(I,I,I,I))Fn_[8+f])(xp,yp,rp,e);break;
        case T_ft:
          dx(y);
          ((void(*)(I,F,I,I))Fn_[9+f])(xp,GetF(yp),rp,e);
          break;
      }
      dx(x); return r;
    } else {
      n=nn(x);
      r=(t==T_it) ? use2(x,y) : mk(T_It,nn(x));
      if(n){
        ((void(*)(I,I,I,I))Fn_[f+11+(I)(0)+((I)(t-1)/2)])(xp,yp,(I)r,ep(r));
      }
      dx(x); dx(y);
      return r;
    }
}

static K td(K x){
    I m;
    K r=x0(x);
    x=r1(x);
    if(tp(r)!=T_St || tp(x)!=T_Lt){ trap(E_Type); }
    m=maxcount((I)x,nn(x));
    x=Ech(15ull,l2(Ki(m),x));
    r=l2(r,x);
    SetI((I)(r)-12,m);
    return (K)((I)r) | ((K)(T_Tt)<<59ull);
}

static K Key(K x, K y);
static K explode(K x){
    I xn,xp,rp,e;
    T xt=tp(x);
    K r=(K)0ull,k;
    if(xt<16){
      r=l1(x);
    } else if(xt==T_Dt){
      r=mk(T_Lt,1);
      SetJ((I)r,(J)x);
    } else if(xt<T_Lt){
      xn=nn(x);
      r=mk(T_Lt,xn);
      if(!xn){
        dx(x);
        return r;
      }
      xp=(I)x; rp=(I)r;
      e=ep(x);
      switch(xt){
        case T_Ct: do{ SetJ(rp,(J)Kc(GetC(xp))); }while(rp+=8, xp++, xp<e);
          break;
        case T_It: do{ SetJ(rp,(J)Ki(GetI(xp))); }while(rp+=8, xp+=4, xp<e);
          break;
        case T_St: do{ SetJ(rp,(J)Ks(GetI(xp))); }while(rp+=8, xp+=4, xp<e);
          break;
        case T_Ft: do{ SetJ(rp,(J)Kf(GetF(xp))); }while(rp+=8, xp+=8, xp<e);
          break;
      }
      dx(x);
    } else if(xt==T_Lt){
      r=x;
    } else if(xt==T_Tt){
      xn=nn(x);
      k=x0(x); x=r1(x);
      r=mk(T_Lt,xn); rp=(I)r;
      x=Flp(x); xp=(I)x;
      for(I i=0;i<xn;i++, xp+=8, rp+=8){ SetJ(rp,(J)Key(rx(k),x0((K)xp))); }
      dx(x); dx(k);
    }
    return r;
}

static K Tak(K x, K y);
static K Drp(K x, K y);
static K keyt(K x, K y){
    x=rx(x);
    y=rx(y);
    return Key(Tak(x,y),Drp(x,y));
}

static K Enl(K x);
static K key(K x, K y, T t){
    I xn;
    T xt=tp(x);
    T yt=tp(y);
    if(xt<16){
      if(xt==T_it){ return Mod(y,x); }
      if(xt==T_st && yt==T_Tt){ return keyt(x,y); }
      x=Enl(x);
    }
    xn=nn(x);
    if(t==T_Tt){
      if(xn>0){
        xn=nn((K)GetJ((I)y));
      }
    } else if(xn!=nn(y)){
      trap(E_Length);
    } else if(yt<16){
      trap(E_Type);
    }
    x=l2(x,y);
    SetI((I)(x)-12, xn);
    return (K)((I)(x)) | ((K)(t)<<59ull);
}

static K Atx(K x, K y);
static K fix(K f, K x, K l){
    K r=(K)0ull;
    K y=rx(x);
    for(;;){
      r=Atx(rx(f),rx(x));
      if(match(r,x)){ break; }
      if(match(r,y)){ break; }
      dx(x);
      x=r;
      if(l!=0ull){ l=cat1(l,rx(x)); }
    }
    dx(f); dx(r); dx(y);
    if(l!=0ull){
      dx(x); return l;
    }
    return x;
}

static K cal(K f, K x);
static K Ecr(K f, K x){
    K r,y;
    I yn,rp;
    T yt, t;
    r=(K)0ull;
    y=x1(x); x=r0(x);
    yt=tp(y);
    if(yt<16){ return cal(f,l2(x,y)); }
    if(yt>T_Lt){
      t=dtypes(x,y);
      r=dkeys(x,y);
      return key(r,Ecr(f,l2(dvals(x),dvals(y))),t);
    }
    yn=nn(y);
    r=mk(T_Lt,yn); rp=(I)r;
    for(I i=0; i<yn; i++, rp+=8){ SetJ(rp,(J)cal(rx(f),l2(rx(x),ati(rx(y),i)))); }
    dx(f); dx(x); dx(y);
    return uf(r);
}

static K ech(K x){ return l2t(x,0ull,T_df); }
static K rdc(K x){ return l2t(x,2ull,T_df); }
static K scn(K x){ return l2t(x,4ull,T_df); }

static K Cal(K x, K y);
static K ec2(K f, K x, K y){
    I n,rp;
    K r=(K)0ull;
    T t=dtypes(x,y);
    if(t>T_Lt){
      r=dkeys(x,y);
      return key(r,ec2(f,dvals(x),dvals(y)),t);
    }
    n=conform(x,y);
    switch(n){
      case 0: return Cal(f,l2(x,y));
      case 1: n=nn(y); break;
      default: n=nn(x); break;
    }
    r=mk(T_Lt,n);
    rp=(I)r;
    for(I i=0; i<n; i++, rp+=8){ SetJ(rp,(J)Cal(rx(f),l2(ati(rx(x),i),ati(rx(y),i)))); }
    dx(f); dx(x); dx(y);
    return uf(r);
}

static K Cat(K x, K y);
static K ecn(K f, K x){
    K r;
    if(nn(x)==2){
      r=x0(x);
      x=r1(x);
      if(r==0ull){ return Ech(f,l1(x)); }
      if(tp(f)==0 && (I)(f)==13 && tp(r)==T_Tt && tp(x)==T_Tt){ // dyad 13 = Cat
        if(nn(r)!=nn(x)){ trap(E_Length); }
        f=Cat(x0(r),x0(x));
        return key(f,Cat(r1(r),r1(x)),T_Tt);
      }
      return ec2(f,r,x);
    }
    return Ech(20ull,l2(f,Flp(x))); // dyad 20 = Cal
}

static K rdn(K f, K x, K l){
    K r=Fst(rx(x));
    x=Flp(ndrop(1,x));
    I n=nn(x);
    for(I i=0;(i<n);i++){
      r=Cal(rx(f),Cat(l1(r),ati(rx(x),i)));
      if (l!=0ull) { l=cat1(l,rx(r)); }
    }
    dx(f); dx(x);
    if(l!=0ull){
      dx(r);
      return uf(l);
    }
    return r;
}

static K join(K x, K y);
static K Dec(K x, K y);
static K Rdc(K f, K x){
    K r,x0;
    I a,xn,fp;
    T t,xt;
    r=(K)0ull;
    t=tp(f);
    if(!isfunc(t)){
      if(nn(x)==2){ trap(E_Nyi); } // TODO: implement
      x=Fst(x);
      return ((t&15)==T_ct)?join(f,x):Dec(f,x);
    }
    a=arity(f);
    if(a!=2){ return (a>2)?rdn(f,x,0ull):fix(f,Fst(x),0ull); }
    if(nn(x)==2){ return Ecr(f,x); }
    x=Fst(x);
    xt=tp(x);
    if(xt==T_Dt){
      x=Val(x);
      xt=tp(x);
    }
    if(xt<16){
      dx(f);
      return x;
    }
    xn=nn(x);
    if(!t){
      fp=(I)f;
      if(fp>1 && fp<8){ // Fn_ @ [367 - 372]
        if(xt==T_Tt){ return Ech(rdc(f),l1(Flp(x))); }
        r=((K(*)(I,I,I))Fn_[365+fp])((I)x,xt,xn); // sum rd0 prd rd0 min max
        if(r!=0ull){
          dx(x);
          return r;
        }
      }
      if(fp==13){
        if(xt<T_Lt){ return x; }
        r=ucats(x);
        if(r!=0ull){ return r; }
      }
    }
    if(!xn){ return ov0(f,x); }
    x0=ati(rx(x),0);
    for(I i=1;i<xn;i++){ x0=cal(rx(f),l2(x0,ati(rx(x),i))); }
    dx(x); dx(f);
    return x0;
}

static I sumi(I xp, I xn){
    I r=0,e=xp+4*xn;
    for(;xp<e; xp+=4){ r+=GetI(xp); }
    return r;
}

static K Rev(K x);
static K Enc(K x, K y){
    K r,xi;
    T xt=tp(x);
    I n=0,yn;
    if(xt==T_It){ n=nn(x); }
    r=mk(T_It,0);
    yn=(I)Cnt(rx(y));
    for(;;){
      xi=ati(rx(x),--n);
      r=Cat(r,Enl(idiv(rx(y),xi,1)));
      y=idiv(y,xi,0);
      if(n==0 || (n<0 && (I)(y)==0)){ break; }
      if(tp(y)>16 && n<0 && !sumi((I)y, yn)){ break; }
    }
    dx(x); dx(y);
    return Rev(r);
}

static K Dec(K x, K y){
    if(tp(y)<16){ trap(E_Type); }
    K r=Fst(rx(y));
    I n=nn(y);
    for(I i=1;i<n;i++) r=Add(ati(rx(y),i),Mul(ati(rx(x),i),r));
    dx(x); dx(y);
    return r;
}

static K Ecl(K f, K x){
    K y,r;
    I xn,rp;
    y=x1(x); x=r0(x);
    if(tp(x)<16){ return cal(f,l2(x,y)); }
    xn=nn(x);
    r=mk(T_Lt,xn); rp=(I)r;
    for(I i=0; i<xn; i++, rp+=8){ SetJ(rp,(J)cal(rx(f),l2(ati(rx(x),i),rx(y)))); }
    dx(f); dx(x); dx(y);
    return uf(r);
}

static K split(K x, K y);
static K Scn(K f, K x){
    K r,z;
    I a,xn,fp,rp;
    T t, xt;
    r=(K)(0ull);
    t=tp(f);
    if(!isfunc(t)){
      if(nn(x)!=1){ trap(E_Rank); }
      x=Fst(x);
      return ((t&15)==T_ct) ? split(f,x) : Enc(f,x);
    }
    a=arity(f);
    if(a!=2){
      if(a>2){ return rdn(f,x,mk(T_Lt,0)); }
      x=rx(Fst(x));
      return fix(f,x,Enl(x));
    }
    if(nn(x)==2){ return Ecl(f,x); }
    x=Fst(x);
    xt=tp(x);
    if(xt<16){
      dx(f);
      return x;
    }
    xn=nn(x);
    if(!xn){
      dx(f);
      return x;
    }
    if(xt==T_Dt){
      r=x0(x);
      return Key(r,Scn(f,l1(r1(x))));
    }
    if(!tp(f)){
      fp=(I)(f);
      if(fp==2 || fp==4){
        if(xt==T_Tt){ return Flp(Ech(scn(f),l1(Flp(x)))); }
        r=((K(*)(I,I,I))Fn_[372+fp])((I)(x),xt,xn); // sums prds
        if(r!=0ull){
          dx(x);
          return r;
        }
      }
    }
    r=mk(T_Lt,xn);
    rp=(I)r;
    z=ati(rx(x),0);
    SetJ(rp,(J)rx(z));
    rp+=8;
    for(I i=1;i<xn;i++, rp+=8){
      z=cal(rx(f),l2(z,ati(rx(x),i)));
      SetJ(rp,(J)rx(z));
    }
    dx(z); dx(x); dx(f);
    return uf(r);
}

static K atdepth(K x, K y){
    K f;
    T xt=tp(x);
    if(xt<16){ trap(E_Type); }
    f=Fst(rx(y));
    if(f==0ull){ f=seq(nn(x)); }
    x=Atx(x,f);
    if(nn(y)==1){
      dx(y);
      return x;
    }
    y=ndrop(1,y);
    if(tp(f)>16){
      if(nn(y)==1 && xt==T_Tt){ return Atx(x,Fst(y)); }
      return Ecl(20ull,l2(x,y)); // dyad 20 = Cal
    }
    return atdepth(x,y);
}

static K prj(K f, K x){
    K r,a,y;
    I xn,xp,ar,an;
    r=(K)0ull;
    if(!isfunc(tp(f))){ return atdepth(f,x); }
    xn=nn(x);
    xp=(I)x;
    a=mk(T_It,0);
    for(I i=0; i<xn; i++, xp+=8){ if(GetJ(xp)==0ll){ a=cat1(a,Ki(i)); } }
    ar=arity(f);
    for(I i=xn; i<ar; i++){
      a=cat1(a,Ki(i));
      x=cat1(x,0ull);
    }
    an=nn(a);
    if(tp(f)==T_pf){
      r=x1(f); y=x2(f); f=r0(f);
      x=stv(r,rx(y),x);
      a=Drp(a,y);
    }
    r=l3(f,x,a);
    SetI((I)(r)-12,an);
    return (K)((I)r) | ((K)(T_pf)<<59ull);
}

static K calltrain(K f, K x, K y){
    I n=nn(f);
    K r=(y==0ull) ? cal(x0(f),l1(x)) : cal(x0(f),l2(x,y));
    for(I i=1; i<n; i++) r=cal(x0(f+8ull),l1(r));
    return r;
}

static K callprj(K f, K x){
    I n=nn(x), fn=nn(f);
    if(fn!=n){
      if(n<fn){
        rx(f);
        return prj(f,x);
      }
      trap(E_Rank);
    }
    return Cal(x0(f),stv(x1(f),x2(f),x));
}

static K exec(K x);
static K lambda(K f, K x){
    K c,lo,sa,r;
    I fn,xn,fp,nl,sap,vp,lp,xp,p,spp,spe;
    fn=nn(f); xn=nn(x);
    if(xn<fn){
      rx(f);
      return prj(f,x);
    }
    if(xn!=fn){ trap(E_Rank); }
    fp=(I)f;
    c=(K)GetJ(fp);
    lo=(K)GetJ(fp+8);
    nl=nn(lo);
    sa=mk(T_It,2*nl); sap=(I)sa;
    vp=GetI(8);
    lp=(I)lo; xp=(I)x;
    rl(x); dx(x);
    for(I i=0; i<nl; i++, sap+=8, lp+=4){
      p=vp+GetI(lp);
      SetJ(sap,GetJ(p));
      if(i<fn){
        SetJ(p,GetJ(xp));
        xp+=8;
      } else { SetJ(p,0ll); }
    }
    spp=PP; spe=PE;
    r=exec(rx(c));
    vp=GetI(8);
    sap=(I)sa;
    lp=(I)lo;
    for(I i=0; i<nl; i++, lp+=4, sap+=8){
      p=vp+GetI(lp);
      dx((K)GetJ(p));
      SetJ(p,GetJ(sap));
      SetJ(sap,0ll);
    }
    dx(sa);
    PP=spp; PE=spe;
    return r;
}

K Native(K x, K y);
static K native(K f, K x){
    I fn=nn(f),xn=nn(x);
    if(xn<fn){
      rx(f);
      return prj(f,x);
    }
    if(xn!=fn){ trap(E_Rank); }
    return Native(x0(f),x);
}

static K cal(K f, K x){
    I fp,xn,a;
    K r=(K)0ull,z=(K)0ull,y,d;
    T t=tp(f);
    fp=(I)f;
    xn=nn(x);
    if(t<T_df){ // 11
      switch(xn-1){
        case 0: x=Fst(x); break;
        case 1:
          r=x1(x); x=r0(x);
          break;
        case 2:
          r=x1(x); z=x2(x); x=r0(x);
          break;
      }
    }
    switch(t){
      case 0:
        switch(xn-1){
          case 0: r=((K(*)(K))Fn_[(I)f])(x); break;
          case 1: r=((K(*)(K,K))Fn_[fp+64])(x,r); break;
          case 2: r=((K(*)(K,K,K,K))Fn_[fp+192])(x,r,1ull,z); break;
          case 3:
            r=x0(x);
            y=x1(x);
            z=x2(x);
            r=((K(*)(K,K,K,K))Fn_[fp+192])(r,y,z,r3(x));
            break;
          default: r=trap(E_Rank); break;
        }
        break;
      case T_cf:
        switch(xn-1){
          case 0: r=calltrain(f,x,0ull); break;
          case 1: r=calltrain(f,x,r); break;
          default: r=trap(E_Rank); break;
        }
        break;
      case T_df:
        d=x0(f);
        a=85+(int32_t)GetJ(fp+8);
        r=((K(*)(K,K))Fn_[a])(d,x);
        break;
      case T_pf: r=callprj(f,x); break;
      case T_lf: r=lambda(f,x); break;
      case T_xf: r=native(f,x); break;
      default: r=trap(E_Type); break;
    }
    dx(f);
    return r;
}

K Cal(K x, K y){
    T xt=tp(x);
    y=explode(y);
    if(isfunc(xt)){ return cal(x,y); }
    return atdepth(x,y);
}

static K com(K x, K y){
    return (K)((I)l2(y,x)) | ((K)(T_cf)<<59ull);
}

static K Enl(K x){
    K r;
    I rp,xp,s;
    T t=tp(x);
    if(t>0 && t<7){
      t+=16;
      r=mk(t,1);
      rp=(I)r;
      xp=(I)x;
      s=sz(t);
      switch(s>>2){
        case 0: SetC(rp,(C)xp); break;
        case 1: SetI(rp,xp); break;
        case 2: SetJ(rp,GetJ(xp)); break;
        case 3: break;
        case 4:
          SetJ(rp,GetJ(xp));
          SetJ(rp+8,GetJ(xp+8));
          break;
      }
      dx(x);
      return r;
    }
    if(t==T_Dt && tp((K)GetJ((I)x))==T_St){ return Flp(Ech(13ull,l1(x))); }
    return l1(x);
}

static K dcat(K x, K y);
static K ucat(K x, K y){
    K r;
    I xn,yn,s;
    T xt=tp(x);
    if(xt>T_Lt){ return dcat(x,y); }
    xn=nn(x); yn=nn(y);
    r=uspc(x,xt,yn);
    s=sz(xt);
    if(xt==T_Lt){ rl(y); }
    Memorycopy((I)(r)+s*xn, (I)y, s*yn);
    dx(y); return r;
}

static K dcat(K x, K y){
    K r,q;
    T t=tp(x);
    if(t==T_Tt && !match((K)GetJ((I)x),(K)GetJ((I)y))){
      return ucat(explode(x),explode(y));
    }
    r=x0(x); x=r1(x);
    q=x0(y); y=r1(y);
    if(t==T_Dt){
      r=Cat(r,q);
      return Key(r,Cat(x,y));
    } else {
      dx(q);
      x=Ech(13ull,l2(x,y));
      return key(r,x,t);
    }
}

static K Cat(K x, K y){
    T xt=tp(x), yt=tp(y);
    if((xt==T_Tt)&&(yt==T_Dt)){
      y=Enl(y); yt=T_Tt;
    }
    if((xt&15)==(yt&15)){
      if(xt<16){ x=Enl(x); }
      return (yt<16)?cat1(x,y):ucat(x,y);
    } else if(xt==T_Lt && yt<16 && nn(x)>0){
      return cat1(x,y);
    }
    x=uf(Cat(explode(x),explode(y)));
    if(!nn(x)){
      dx(x); return mk(xt|16,0);
    }
    return x;
}

static K flat(K x){
    K r=mk(T_Lt,0);
    I xn=nn(x), xp=(I)x;
    for(I i=0; i<xn; i++, xp+=8){ r=Cat(r,x0((K)xp)); }
    dx(x);
    return r;
}

static K cat1(K x, K y){
    T xt=tp(x);
    I s,rp,yp,xn=nn(x);
    K r=uspc(x,xt,1);
    s=sz(xt);
    rp=(I)(r)+s*xn;
    yp=(I)y;
    switch(sz(xt)){
      case 1: SetC(rp,(C)yp); break;
      case 4: SetI(rp,yp); break;
      case 8:
        if(xt==T_Ft){
          SetJ(rp,GetJ(yp));
          dx(y);
        } else { SetJ(rp,(J)y); }
        break;
    }
    return r;
}

static K ncat(K x, K y){
    T xt=tp(x);
    if(xt<16){ x=Enl(x); }
    xt=maxtype(x,y);
    x=uptype(x,xt);
    y=uptype(y,xt);
    return cat1(x,y);
}

K trap(I x){
    exec_d=0;
    if(U_==NULL){ panic(x); } // no memory
#ifdef SPESH_IO_SYS
    K s;
    I a,b;
    if      (x == E_Type)   write(Ku(0x000a6570797427ull));
    else if (x == E_Value)  write(Ku(0x000a65756c617627ull));
    else if (x == E_Index)  write(Ku(0x000a7865646e6927ull));
    else if (x == E_Length) write(Ku(0x000a6874676e656c27ull));
    else if (x == E_Rank)   write(Ku(0x000a6b6e617227ull));
    else if (x == E_Parse)  write(Ku(0x000a657372617027ull));
    else if (x == E_Stack)  write(Ku(0x000a6b6361747327ull));
    else if (x == E_Grow)   write(Ku(0x000a776f726727ull));
    else if (x == E_Unref)  write(Ku(0x000a6665726e7527ull));
    else if (x == E_Io)     write(Ku(0x000a6f6927ull));
    else if (x == E_Limit)  write(Ku(0x000a74696d694c27ull));
    else if (x == E_Nyi)    write(Ku(0x000a69796e27ull));
    else                    write(Ku(0x000a72726527ull)); // "'err\n"
    if(!SRCP){
      write(Ku(0x000a30ull)); // "0\n"
    } else {
      s=src();
      a=maxi(SRCP-30, 0);
      for(I i=a;i<SRCP;i++){
        if(GetC((I)(s)+i)=='\n'){ a=1+i; }
      }
      b=mini(nn(s), SRCP+30);
      for(I i=SRCP;i<b;i++) {
        if(GetC((I)(s)+i)=='\n'){
          b=i;
          break;
        }
      }
      Write(0, 0, (I)(s)+a, b-a);
      if(SRCP>a){
        write(Cat(Kc('\n'), ntake((SRCP-a)-1,Kc(' '))));
      }
    }
    write(Ku(0x000a5eull)); // "^\n"
#endif //SPESH_IO_SYS
    panic(x);
    return 0ull;
}

static I quoted(K x){ return (I)((I)(x)>=QUOTE && tp(x)==0); }
static K quote(K x){ return (x + QUOTE); }
static K unquote(K x){ return (x - QUOTE); }

static I marksrc(K x){
    I p=16777215&(I)(x>>32ull);
    if(p){ SRCP=p; }
    return (I)x;
}

static void push(K x){
    SetJ(SP,(J)x);
    SP+=8;
    if(SP==512){ trap(E_Stack); }
}

static K pop(void){
    SP-=8;
    if(SP<POS_STACK){ trap(E_Stack); }
    K r=(K)GetJ(SP);
    return r;
}

static I run_op(void){
    if(SPESH_MAX_OPS>0 && ++ops_>SPESH_MAX_OPS){ return(I)trap(E_Limit); }
    exec_state *s = &exec_s[exec_d-1];
    K u=(K)GetJ(s->p);
    if(tp(u)){ // literal
      push(s->a);
      s->a=rx(u);
    } else { // run instruction
      switch((I)(u)>>6){
      case 0: s->a=((K(*)(K))Fn_[marksrc(u)])(s->a); // 0..63 monadic
        break;
      case 1: s->a=((K(*)(K,K))Fn_[marksrc(u)])(s->a,pop()); // 64..127 dyadic
        break;
      case 2: // 128 dyadic indirect
        marksrc(s->a);
        s->b=pop();
        s->a=Cal(s->a,l2(s->b,pop()));
        break;
      case 3: // 192..255 tetradic
        s->b=pop();
        s->c=pop();
        s->a=((K(*)(K,K,K,K))Fn_[marksrc(u)])(s->a,s->b,s->c,pop());
        break;
      case 4: // 256 drop
        dx(s->a);
        s->a=pop();
        break;
      case 5: // 320 jmp
        s->p+=(I)s->a;
        s->a=pop();
        break;
      case 6: // 384 jif
        u=pop();
        s->j=0;
        if((I)(u)==0){ s->p+=(I)(s->a); s->j=1; }
        dx(u);
        s->a=pop();
        break;
      case 7: // 448 jnj
        if(s->j==0){ s->p+=(I)(s->a); }
        dx(s->a);
        s->a=pop();
        break;
      case 8: s->j=0; break; // 512 snj
      default: // 576+ quoted verb
        push(s->a);
        s->a=rx(u-QUOTE);
        break;
      }
    }
    s->p+=8;
    return(s->p < s->e);
}

static I issue(K x){
    SRCP=0;
    I xn=nn(x);
    if(!xn){
      dx(x); return 0;
    }
    if(exec_d>=SPESH_MAX_RECURSION+1){ return (I)trap(E_Limit); }
    exec_state *s = &exec_s[exec_d++];
    s->j=0;
    s->a=(K)0ull; // accu
    s->b=(K)0ull;
    s->c=(K)0ull;
    s->p=(I)x;
    s->e=s->p+8*xn;
    return 1;
}

static K exec(K x){
    // TODO: rewrite to avoid recursive calls to exec/run_op
    if(issue(x)!=1){ return 0ull; }
    do {} while(run_op());
    dx(pop()); dx(x);
    return exec_s[--exec_d].a;
}

static K lst(K n){
    I rp, rn=(I)n;
    K r=mk(T_Lt,rn);
    rp=(I)r;
    for(I i=0;i<rn;i++, rp+=8){ SetJ(rp, (J)pop()); }
    return uf(r);
}

static K nul(K x){
    push(x); return 0ull;
}

static K lup(K x){ return x0((K)(GetI(8)+(I)x)); }

static K Dmd(K x, K i, K v, K y);
static K Unq(K x);
static K Fnd(K x, K y);
static K Amd(K x, K i, K v, K y){
    K r;
    I n;
    T xt=tp(x),it,yt;
    if(xt==T_st){ return Asn(x,Amd(Val(x),i,v,y)); }
    if(xt<16){ trap(E_Type); }
    it=tp(i);
    if(it==T_Lt){
      n=nn(i);
      for(I j=0;j<n;j++) x=Amd(x,ati(rx(i),j),rx(v),ati(rx(y),j));
      dx(i); dx(v); dx(y);
      return x;
    }
    if(xt>T_Lt){
      r=x0(x); x=r1(x);
      if((xt==T_Tt)&&((it&15)==T_it)){
        if(tp(y)>T_Lt){ y=Val(y); }
        return key(r,Dmd(x,l2(0ull,i),v,y),xt);
      }
      r=Unq(Cat(r,rx(i)));
      return key(r,Amd(ntake(nn(r),x),Fnd(rx(r),i),v,y),xt);
    }
    if(i==0ull){
      if(v==1ull){
        if(tp(y)<16){ y=ntake(nn(x),y); }
        dx(x); return y;
      }
      return Cal(v,l2(x,y));
    }
    if(tp(v)!=0 || v!=1ull){
      y=cal(v,l2(Atx(rx(x),rx(i)),y));
    }
    yt=tp(y);
    if((xt&15)!=(yt&15)){
      x=explode(x);
      xt=T_Lt;
    }
    if(it==T_it){
      if(xt!=yt+16){ x=explode(x); }
      return sti(x,(I)i,y);
    }
    if(yt<16){
      y=ntake(nn(i),y);
      yt=tp(y);
    }
    if(xt==T_Lt){ y=explode(y); }
    return stv(x,i,y);
}

static K Dmd(K x, K i, K v, K y){
    K f,t;
    I n,rj;
    if(tp(x)==T_st){ return Asn(x,Dmd(Val(x),i,v,y)); }
    i=explode(i);
    f=Fst(rx(i));
    if(nn(i)==1){
      dx(i); return Amd(x,f,v,y);
    }
    if(f==0ull){ f=seq(nn(x)); }
    i=ndrop(1,i);
    if(tp(f)>16){
      n=nn(f);
      if(nn(i)!=1){ trap(E_Rank); }
      i=Fst(i);
      if((tp(f)==T_It)&&(tp(x)==T_Tt)){
        t=rx(x0(x));
        return key(t,Dmd(r1(x),l2(Fnd(t,i),f),v,y),T_Tt);
      }
      if(tp(f)!=T_It || tp(x)!=T_Lt){ trap(E_Nyi); } // TODO: implement
      x=use(x);
      for(I j=0;j<n;j++){
        rj=(I)(x)+8*GetI((I)(f)+4*j);
        SetJ(rj, (J)Amd((K)GetJ(rj),rx(i),rx(v),ati(rx(y),j)));
      }
      dx(f); dx(i); dx(v); dx(y);
      return x;
    }
    x=rx(x);
    return Amd(x,f,1ull,Dmd(Atx(x,f),i,v,y));
}

static I fndl(K x, K y){
    dx(y);
    for(I r=0, xp=(I)x, xn=nn(x); r<xn; r++, xp+=8){
      if(match((K)GetJ(xp), y)){ return r; }
    }
    return nai;
}

static K uqf(K x){ // uniq elements in T_Lt (deep compare)
    I xn=nn(x);
    K r=mk(T_Lt,0),xi;
    if(xn>0){ r=cat1(r, ati(rx(x), 0)); }
    for(I i=1; i<xn; i++) {
      xi=ati(rx(x), i);
      if(fndl(r, rx(xi)) == nai){
        r=cat1(r, xi);
      } else {
        dx(xi);
      }
    }
    dx(x);
    return r;
}

static K Grp(K x){
    K k,v,ki,xi,l;
    I kn,xn;
    k=uqf(rx(x));
    kn=nn(k); xn=nn(x);
    v=mk(T_Lt, 0);
    for(I i=0; i<kn; i++){
      ki=Atx(rx(k), (K)i);
      l=mk(T_It, 0);
      for(I j=0; j<xn; j++){
        xi=Atx(rx(x), (K)j);
        if(match(xi, ki)){ l=cat1(l, Ki(j)); }
        else { dx(xi); }
      }
      v=cat1(v, l);
    }
    dx(x);
    return Key(k, v);
}

static K grp(K x, K y){
    x=rx(x); y=rx(y);
    return Atx(Drp(x,y),Grp(Atx(y,x)));
}

static K Mtc(K x, K y){
    K r=Ki(match(x,y));
    dx(x); dx(y);
    return r;
}

static I inC(I x, I yp, I e){
    for(;yp<e; yp++){
    if(x==GetC(yp)){ return yp; }
    } return 0;
}

static I inI(I x, I yp, I e){
    for(;yp<e; yp+=4){
      if(x==GetI(yp)){ return yp; }
    } return 0;
}

static I inF(F x, I yp, I e){
    for(;yp<e; yp+=8){
      if(eqf(x,GetF(yp))){ return yp; }
    } return 0;
}

static K in(K x, K y, T xt){
    I xp=(I)x,yp=(I)y,e=ep(y);
    switch(xt){
      case T_ct: e=inC(xp,yp,e); break;
      case T_it: e=inI(xp,yp,e); break;
      case T_st: e=inI(xp,yp,e); break;
      case T_ft:
        dx(x);
        e=inF(GetF(xp),yp,e);
        break;
    }
    return Ki((I)(e!=0));
}

static K In(K x, K y){
    T xt=tp(x),yt=tp(y);
    if(xt==yt && xt>16){ return Ecl(30ull,l2(x,y)); }
    if((xt+16)!=yt){ trap(E_Type); }
    dx(y);
    return in(x,y,xt);
}

static I rnd(void){
    I r=rand_;
    r=(r^(r<<13));
    r=(r^(r>>17));
    r=(r^(r<<5));
    rand_=r;
    return r;
}

static I randi(I n){
    UI low,thresh2,v=(UI)rnd();
    UJ prod=(UJ)(v) * (UJ)n;
    low=(UI)prod;
    if(low<(UI)n){
      thresh2=(UI)(-n) % (UI)n;
      for(;low<thresh2;){
        v=(UI)rnd();
        prod=(UJ)(v) * (UJ)n;
        low=(UI)prod;
      }
    }
    return (I)(prod>>32ull);
}

static K randI(I i, I n){
    K r=mk(T_It,n);
    I rp=(I)r,e=rp+(4*n);
    if(!i){
      for(;rp<e; rp+=4){ SetI(rp,rnd()); }
    } else {
      for(;rp<e; rp+=4){ SetI(rp,randi(i)); }
    }
    return r;
}

static K shuffle(K r, I m){
    I rp,n,ii,j,t;
    rp=(I)r;
    n=nn(r);
    m=mini(n-1, m);
    for(I i=0; (i<m); i++, rp+=4){
      ii=i+randi(n-i);
      j=rp + 4*(ii-i);
      t=GetI(rp);
      SetI(rp,GetI(j)); SetI(j,t);
    }
    return r;
}

static K Cst(K x, K y);
static K deal(K x, K y){
    I xp,yp;
    T yt=tp(y);
    if(yt>16){ return In(x,y); }
    if(tp(x)!=T_it){ trap(E_Type); }
    xp=(I)x;
    if(yt==T_ct){
      return Add(Kc(97), Cst(sc(Ku(99ull)), deal(x,Ki((I)(y)-96))));
    }
    if(yt==T_st){ return Ech(17ull, l2(Ks(0), deal(x,Fst(cs(y))))); }
    if(yt!=T_it){ trap(E_Type); }
    yp=(I)y;
    if(xp>0){ return randI(yp,xp); }
    return ntake(-xp,shuffle(seq(yp),-xp));
}

static K fndXs(K x, K y, T t, I yn){
    K r;
    I xn,a,b,rp,x0,xp;
    xn=nn(x);
    a=(I)min((I)x, t, xn);
    b=1+(((I)max((I)x, t, xn)-a) >> (3*(I)(t==T_St)));
    if(b>256 && b>yn){ return 0ull; }
    if(t==T_St){
      x=use(x);
      x=(K)((I)(x)) | ((K)(T_It)<<59ull);
      x=Div(x, Ki(8));
      y=use(y);
      y=(K)((int32_t)(y)) | ((K)(T_It)<<59ull);
      y=Div(y, Ki(8));
      a=(a>>3);
    }
    r=ntake(b,Ki(nai));
    rp=(I)(r)-4*a;
    x0=(I)x;
    xp=ep(x);
    if(t==T_Ct){
      for(;xp>x0;){
        --xp; SetI(rp+4*GetC(xp), xp-x0);
      }
    } else {
      for(;xp>x0;){
        xp-=4; SetI(rp+4*GetI(xp), (xp-x0)>>2);
      }
    }
    dx(x);
    return Atx(r,Add(Ki(-a),y));
}

static I fnd(K x, K y, T t){
    I r=0,xn,xp,yp,xe,s=0;
    xn=nn(x);
    if(!xn){ return nai; }
    xp=(I)x; yp=(I)y;
    xe=ep(x);
    switch(t){
      case T_ct: r=inC(yp,xp,xe); break;
      case T_it:
        s=2;
        r=inI(yp,xp,xe);
        break;
      case T_st:
        s=2;
        r=inI(yp,xp,xe);
        break;
      case T_ft:
        s=3;
        r=inF(GetF(yp),xp,xe);
        break;
    }
    if(!r){ return nai; }
    return (r-xp)>>s;
}

static K Fnd(K x, K y){
    I yn,rp;
    K r=(K)0ull, yi;
    T xt=tp(x); T yt=tp(y);
    if(xt<16){ return (yt==T_Tt)?grp(x,y):deal(x,y); }
    if(xt>T_Lt){
      if(xt==T_Tt){ trap(E_Nyi); } // TODO: implement
      r=x0(x);
      return Atx(r,Fnd(r1(x),y));
    } else if(xt==yt){
      yn=nn(y);
      if(xt<T_Ft && ((yn>4 && xt==T_Ct) || yn>8)){
        r=fndXs(x,y,xt,yn);
        if(r!=0ull){ return r; }
      }
      r=mk(T_It,yn); rp=(I)r;
      if(xt==T_Lt){
        for(I i=0, yp=(I)y; i<yn; i++, rp+=4, yp+=8){
          SetI(rp,fndl(x,x0((K)yp)));
        }
      } else {
        for(I i=0; i<yn; i++, rp+=4){
          yi=ati(rx(y),i);
          SetI(rp,fnd(x, yi, xt-16));
          dx(yi);
        }
      }
    } else if(xt==yt+16){
      r=Ki(fnd(x,y,yt));
    } else if(xt==T_Lt){
      r=Ki(fndl(x,rx(y)));
    } else if(yt==T_Lt){
      return Ecr(18ull,l2(x,y)); // dyad 18 = Fnd
    } else { trap(E_Type); }
    dx(x); dx(y);
    return r;
}

static I findat(I xp, I yp, I n){
    I i=0;
    do{ if(GetC(xp+i)!=GetC(yp+i)){ return 0; }
    }while(++i<n);
    return 1;
}

static K Find(K x, K y){
    K r;
    I xn,yn,xp,yp,y0,e;
    T xt=tp(x); T yt=tp(y);
    if(xt!=yt || xt!=T_Ct){ trap(E_Type); }
    xn=nn(x); yn=nn(y);
    if(xn==0 || yn==0){
      dx(x); dx(y);
      return mk(T_It,0);
    }
    r=mk(T_It,0);
    xp=(I)x; yp=(I)y;
    y0=yp;
    e=(yp+yn+1)-xn;
    do{
      if(findat(xp,yp,xn)){
        r=cat1(r, Ki(yp-y0));
        yp+=xn;
      } else {
        yp++;
      }
    }while(yp<e);
    dx(x); dx(y);
    return r;
}

static I mtC(I xp, I yp, I e){
    I ve=(e&~7);
    for(;yp<ve; xp+=8, yp+=8){
      if(GetJ(xp)!=GetJ(yp)){ return 0; }
    }
    for(;yp<e; xp++, yp++){
      if(GetC(xp)!=GetC(yp)){ return 0; }
    }
    return 1;
}

static I mtF(I xp, I yp, I e){
    do{ if(!eqf(GetF(xp),GetF(yp))){ return 0; }
    }while(xp+=8, yp+=8, yp<e);
    return 1;
}

static I match(K x, K y){
    I yn=0,xn,xp,yp,e;
    T xt, yt;
    if(x==y){ return 1; }
    xt=tp(x); yt=tp(y);
    if(xt!=yt){ return 0; }
    xp=(I)x; yp=(I)y;
    if(xt<T_ft){ return (I)(xp==yp); }
    if(xt>16){
      xn=nn(x); yn=nn(y);
      if(xn!=yn){ return 0; }
      if(!xn){ return 1; }
      e=ep(y);
      switch(xt){
        case T_Ct: return mtC(xp,yp,e);
        case T_It: return mtC(xp,yp,e);
        case T_St: return mtC(xp,yp,e);
        case T_Ft: return mtF(xp,yp,e);
        case T_Lt:
          for(I i=0;i<xn;i++, xp+=8, yp+=8){
            if(!match((K)GetJ(xp), (K)GetJ(yp))){ return 0; }
          }
          return 1;
        default:
          if(match((K)GetJ(xp), (K)GetJ(yp))){
            return match((K)GetJ(xp+8),(K)GetJ(yp+8));
          }
          return 0;
      }
    }
    switch((I)(xt-T_ft)-3*(I)(xt>9)){
      case 0: return eqf(GetF(xp),GetF(yp));
      case 1: trap(E_Nyi); break;
      case 2: yn=8*nn(y); break;
      case 3: yn=16; break;
      case 4: yn=24; break;
      case 5: return match((K)GetJ(xp+16), (K)GetJ(yp+16));
      default: return (I)(GetJ(xp)==GetJ(yp));
    }
    for(;yn>0;){
      yn=yn-8;
      if(!match((K)GetJ(xp+yn), (K)GetJ(yp+yn))){ return 0; }
    }
    return 1;
}

static K atv(K x, K y){
    K r,miss;
    I yn,xn,rp,xp,yp,xi;
    T t=tp(x);
    if(t==T_Tt){ return Atx(x,y); }
    yn=nn(y);
    if(t<16){
      dx(y); return ntake(yn,x);
    }
    xn=nn(x);
    r=mk(t,yn); rp=(I)r; 
    xp=(I)x; yp=(I)y;
    miss=missing(t-16);
    switch(sz(t)>>2){
      case 0:
        for(I i=0;i<yn;i++, rp++, yp+=4){
          xi=GetI(yp);
          if((UI)(xi)>=(UI)(xn)){ SetC(rp,(C)miss); }
          else { SetC(rp,GetC(xp+xi)); }
        }
        break;
      case 1:
        for(I i=0;i<yn;i++, rp+=4, yp+=4){
          xi=GetI(yp);
          if((UI)(xi)>=(UI)(xn)){ SetI(rp,(I)miss); }
          else { SetI(rp,GetI(xp+4*xi)); }
        }
        break;
      case 2:
        for(I i=0;i<yn;i++, rp+=8, yp+=4){
          xi=GetI(yp);
          if((UI)(xi)>=(UI)(xn)){
            if(t==T_Lt){ SetJ(rp,(J)miss); }
            else { SetJ(rp,GetJ((I)miss)); }
          } else { SetJ(rp,GetJ(xp+8*xi)); }
        }
        break;
    }
    if(t==T_Lt){
      rl(r); r=uf(r);
    }
    dx(miss); dx(x); dx(y);
    return r;
}

static K Atx(K x, K y){
    I xp;
    K r=(K)(0ull);
    T xt=tp(x);
    T yt=tp(y);
    xp=(I)(x);
    if(xt<16){
      if(xt==0 || xt>T_tt){ return cal(x,l1(y)); }
      if(xt==T_st){
        if(!xp && yt==T_it){ return (K)((I)(y)); }
        return cal(Val(sc(cat1(cs(x),Kc('.')))),l1(y));
      }
    }
    if(xt>T_Lt && yt<T_Lt){
      r=x0(x);
      x=r1(x);
      if(xt==T_Tt && (yt&15)==T_it){
        return key(r,Ecl(19ull,l2(x,y)),T_Dt+(I)(I)(yt==T_It));
      }
      return Atx(x,Fnd(r,y));
    }
    if(yt<T_It){
      y=uptype(y,T_it);
      yt=tp(y);
    }
    if(yt==T_It){ return atv(x,y); }
    if(yt==T_it){ return ati(x,(I)y); }
    if(yt==T_Lt){ return Ecr(19ull,l2(x,y)); } // dyad 19 = Atx
    if(yt==T_Dt){
      r=x0(y);
      return Key(r,Atx(x,r1(y)));
    }
    return trap(E_Type);
}

static K ati(K x, I i){
    I s,p;
    K r=(K)0ull;
    T t=tp(x);
    if(t<16){ return x; }
    if(t>T_Lt){ return Atx(x,Ki(i)); }
    if(i<0 || i>=nn(x)){
      dx(x);
      return missing(t-16);
    }
    s=sz(t);
    p=(I)(x)+i*s;
    switch(s>>2){
      case 0: r=(K)((UI)GetC(p)); break;
      case 1: r=(K)((UI)GetI(p)); break;
      case 2: r=(K)((UJ)GetJ(p)); break;
    }
    if(t==T_Ft){
      r=Kf(F64reinterpret_i64((K)r));
    } else if(t==T_Lt){
      r=rx(r); dx(x);
      return r;
    }
    dx(x);
    return r | ((K)(t-16)<<59ull);
}

static K next(void){
    if(PP==PE){ return 0ull; }
    K r=(K)GetJ(PP);
    PS=(16777215&(I)(r>>32ull));
    PP+=8;
    return r&~((K)(16777215ull)<<32ull);
}

static I is(I x, I m){
    // 0x02 =       10 -> ABCDFGHIJLKMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz
    // 0x06 =      110 -> 0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz
    // 0x08 =     1000 -> \/'  
    // 0x40 =  1000000 -> ")0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ]abcdefghijklmnopqrstuvwxyz}
    // 0x80 = 10000000  -> 0123456789abcdef
    // 0x10 =    10000  -> ([{
    // 0x20 =   100000  -> )]};
    // 0x30 =   110000  -> ([{}]);
    // 0x04 =      100  -> 0123456789
    static const I CharClass[95] = {
      //            ' '    !    "      #     $     %     &     '     (     )     *     +     ,     -     .     /     0     1
                  0x00, 0x01, 0x40, 0x01, 0x01, 0x01, 0x01, 0x09, 0x10, 0x60, 0x01, 0x01, 0x01, 0x01, 0x01, 0x09, 0xc4, 0xc4,
      // 2     3     4     5     6     7     8     9     :     ;     <     =     >     ?     @     A     B     C     D     E
      0xc4, 0xc4, 0xc4, 0xc4, 0xc4, 0xc4, 0xc4, 0xc4, 0x01, 0x20, 0x01, 0x01, 0x01, 0x01, 0x01, 0x42, 0x42, 0x42, 0x42, 0x42,
      // F     G     H     I     J     K     L     M     N     O     P     Q     R     S     T     U     V     W     X     Y
      0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42,
      // Z     [     \     ]     ^     _     `     a     b     c     d     e     f     g     h     i     j     k     l     m
      0x42, 0x10, 0x09, 0x60, 0x01, 0x01, 0x00, 0xc2, 0xc2, 0xc2, 0xc2, 0xc2, 0xc2, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42,
      // n     o     p     q     r     s     t     u     v     w     x     y     z     {     |     }    ~
      0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x10, 0x01, 0x60, 0x01
    };
    I y=x-32;
    if(y<0 || y>94){ return 0; }
    return m & CharClass[y];
}

static K clist(K x, I n){
    K xi; T t;
    I p=(I)x;
    for(I i=0; i<n; i++, p+=8){
      xi=(K)GetJ(p);
      t=tp(xi);
      if(t!=T_Lt){ return 0ull; }
      if(nn(xi)!=1){ return 0ull; }
      if(!tp((K)GetJ((I)xi))){ return 0ull; }
    }
    return uf(flat(x));
}

static K rlist(K x, K p){
    I n=nn(x);
    if(!n){ return l1(x); }
    if(n==1){ return Fst(x); }
    if(p!=2ull){
      p=clist(x,n);
      if(p!=0ull){ return l1(p); }
    }
    return cat1(cat1(flat(Rev(x)),Ki(n)),27ull);
}

static K whl(K x, I xn){
    K r,y;
    I p,sum=2;
    r=cat1(Fst(rx(x)),0ull);
    p=nn(r)-1;
    r=cat1(r,384ull); // jif
    r=cat1(r,256ull); // drop
    for(I i=0, xp=(I)x+8; i<xn; i++, xp+=8){
      y=x0((K)xp);
      if(!y){ continue; }
      if(i){ r=cat1(r,256ull); }
      sum+=1+nn(y);
      r=ucat(r,y);
    }
    r=cat1(cat1(r,Ki(-8*(2+nn(r)))), 320ull); // jmp back
    SetJ((I)(r)+8*p, (J)(Ki(8*sum)));
    dx(x);
    return ucat(l1(0ull),r);
}

static K iff(K x, I xn){
    K r,y;
    I p,sum=1;
    r=cat1(Fst(rx(x)),0ull);
    p=nn(r)-1;
    r=cat1(r,384ull); // jif
    r=cat1(r,256ull); // drop
    for(I i=0, xp=(I)x+8; i<xn; i++, xp+=8){
      y=x0((K)xp);
      if(!y){ continue; }
      if(i){ r=cat1(r,256ull); }
      sum+=1+nn(y);
      r=ucat(r,y);
    }
    r=cat1(r, 512ull); // snj
    SetJ((I)(r)+8*p, (J)(Ki(8*sum))); // jif
    dx(x);
    return ucat(l1(0ull),r);
}

static K els(K x, I xn){
    K r,y;
    I sum=0;
    r=mk(T_Lt, 0);
    r=cat1(r, 0ull);
    r=cat1(r,448ull); // jnj
    r=cat1(r,256ull); // drop
    for(I i=0, xp=(I)x; i<xn; i++, xp+=8){
      y=x0((K)xp);
      if(y){
        if(i){ r=cat1(r,256ull); }
        sum+=1+nn(y);
        r=ucat(r,y);
      }
    }
    SetJ((I)(r), (J)(Ki(8*sum))); // jnj
    dx(x);
    return ucat(l1(0ull),r);
}

static K elif(K x, I xn){
    K r,y;
    I p,sum=1,add;
    r=mk(T_Lt, 0);
    r=cat1(r, 0ull);
    r=cat1(r,448ull); // jnj
    r=Cat(r, Fst(rx(x)));
    r=cat1(r, 0ull);
    p=nn(r)-1;
    r=cat1(r,384ull); // jif
    add=nn(r);
    r=cat1(r,256ull); // drop
    for(I i=0, xp=(I)x+8; i<xn; i++, xp+=8){
      y=x0((K)xp);
      if(!y){ continue; }
      if(i){ r=cat1(r,256ull); }
      sum+=1+nn(y);
      r=ucat(r,y);
    }
    r=cat1(r, 512ull); // snj
    SetJ((I)(r), (J)(Ki(8*(sum+add)))); // jnj
    SetJ((I)(r)+8*p, (J)(Ki(8*sum))); // jif
    dx(x);
    return ucat(l1(0ull),r);
}

static K cond(K x, I xn){
    K r;
    I nxt=0,sum=0,xp,state=1;
    xp=(I)(x) + 8*xn;
    for(;xp!=(I)x;){
      xp=xp-8;
      r=(K)GetJ(xp);
      if(!r){ continue; }
      if(sum>0){
        state=1-state;
        r=state ? cat1(cat1(r,Ki(nxt)),384ull) : cat1(cat1(r,Ki(sum)),320ull); // 384=jif 320=jmp
        SetJ(xp, (J)r);
      }
      nxt=8*nn(r);
      sum+=nxt;
    }
    return flat(x);
}

static K pspec(K r, K n){ // parse special [ ] syntax
    I ln=nn(n);
    K v=(K)GetJ((I)r);
    if(nn(r)==1 && ln>2 && tp(v)==0 && (I)(v)==17+QUOTE){ // 17 = Str = $
      dx(r);
      return cond(n,ln); // $[..] cond
    }
    if(nn(r)!=2 || tp(v)!=T_st){ return (K)0ull; }
    K c = cs(v);
    if(ln>1 && nn(c)==5){
      const C *cwhl="while";
      I found=1,cp=(I)c;
      for(I i=0; i<5; i++){
        if(GetC(cp+i)!=cwhl[i]){ found=0; break; }
      }
      if(found){
        dx(r);
        return whl(n, ln-1); // while[..]
      }
    }
    if(ln>1 && nn(c)==2){
      const C *cif="if";
      I found=1,cp=(I)c;
      for(I i=0; i<2; i++){
        if(GetC(cp+i)!=cif[i]){ found=0; break; }
      }
      if(found){
        dx(r);
        return iff(n, ln-1); // if[..]
      }
    }
    if(ln>0 && nn(c)==4){
      const C *celse="else";
      I found=1,cp=(I)c;
      for(I i=0; i<4; i++){
        if(GetC(cp+i)!=celse[i]){ found=0; break; }
      }
      if(found){
        dx(r);
        return els(n, ln); // else[..]
      }
    }
    if(ln>1 && nn(c)==4){
      const C *celif="elif";
      I found=1,cp=(I)c;
      for(I i=0; i<4; i++){
        if(GetC(cp+i)!=celif[i]){ found=0; break; }
      }
      if(found){
        dx(r);
        return elif(n, ln-1); // elif[..]
      }
    }
    return (K)0ull;
}

static K lastp(K x){ return (K)GetJ((I)(x) + 8*(nn(x)-1)); }
static K ldrop(I n, K x){ return explode(ndrop(n,x)); }

static K dyadic(K x, K y){
    K l=lastp(y);
    if(quoted(l)){ return cat1(ucat(x,ldrop(-1,y)), 64ull+unquote(l)); } // monad + 64 = dyad
    return cat1(ucat(x,y),128ull);
}

static K monadic(K x){
    K l=lastp(x),r;
    if(quoted(l)){
      r=cat1(ldrop(-1,x),unquote(l));
      return ((I)(l)==1+QUOTE) ? cat1(cat1(r,Ki(0x100000)),320ull) : r; // 320 = jmp
    }
    return cat1(x,83ull);
}

static K pasn(K x, K y, K r){
    K l,s,lp;
    I v,sap,xn;
    l=(K)GetJ((I)y);
    v=(I)l;
    sap=(0xffffff&(I)(l>>32ull));
    if((nn(y)==1 && tp(l)==0 && v==1+QUOTE) || (v>96+QUOTE && v<117+QUOTE)){
      dx(y);
      xn=nn(x);
      if(xn>2){ // indexed amd/dmd
        if(v>96+QUOTE){ // indexed-modified
          l=l-96ull;
        }
        s=ati(rx(x), xn-3);
        lp=(0xff000000ffffffffull&lastp(x));
        // (+;.i.;`x;.;@) -> x:@[x;.i.;+;rhs] which is (+;.i.;`x;.;211 or 212)
        // lp+128 is @[amd..] or .[dmd..]
        if(lp==92ull){
          lp=84ull; // x[i;]:.. no projection
        }
        x=cat1(cat1(ucat(l1(l),ldrop(-2,x)),20ull), ((K)(sap)<<32ull) | (lp+128ull));
        y=l2(s,QUOTE); // s:..
      } else {
        if(v==1+QUOTE || v==97+QUOTE){
          s=Fst(x); // (`x;.)
          if(loc_!=0ull && v==1+QUOTE){
            loc_=Cat(loc_,rx(s));
          }
          x=l1(s);
          y=l1(QUOTE); // asn
        } else { // modified
          y=cat1(l2(unquote(l-32ull),Fst(rx(x))),QUOTE);
        }
      }
      return dyadic(ucat(r,x),y);
    }
    return 0ull;
}

static K plist(K c);
static K plam(I s0);
static K es(void);
static K t(void){
    K r=next(),verb,n,ks,p,s;
    I a;
    T rt, tn;
    if(r==0ull){ return 0ull; }
    if(tp(r)==0 && (I)(r)<127 && is((I)r,0x20)){ // )]};
      PP-=8;
      return 0ull;
    }
    verb=(K)0ull;
    if(r==(K)40ull){ // '('
      r=plist(41ull); // ')'
      r=rlist(r&~1ull, 0ull);
    } else if(r==(K)123ull){ // '{'
      r=plam(PS);
    } else if(r==(K)91ull){ // '['
      r=es();
      if(next()!=(K)93ull){ trap(E_Parse); } // ']'
      return r;
    } else if(tp(r)==T_st){
      r=l2(r, 20ull | ((K)(PS)<<32ull)); // .`x (lookup)
    } else {
      rt=tp(r);
      if(!rt){
        r=quote(r) | ((K)(PS)<<32ull);
        verb=1ull;
      } else if(rt==T_St && nn(r)==1){ r=Fst(r); }
      r=l1(r);
    }
    for(;;){
      n=next();
      if(n==0ull){ break; }
      a=(int32_t)n;
      tn=tp(n);
      ks=(K)(PS)<<32ull;
      if(tn==0 && a>20 && a<27){ // +/
        r=cat1(r,n);
        verb=1ull;
      } else if(n==91ull){ // '['
        verb=0ull;
        n=plist(93ull); // ']'
        p=(K)(84ull)+(8ull*(n&1ull)); // 92(project) or call(84)
        n=(n&~1ull);
        s=pspec(r,n);
        if(s!=0ull){ return s; }
        if(nn(n)==1){ r=cat1(ucat(Fst(n),r), 83ull|ks); }
        else {
          n=rlist(n,2ull);
          r=cat1(Cat(n,r), p|ks);
        }
      } else {
        PP-=8;
        break;
      }
    }
    return r+verb;
}

static I svrb(I p){
    K x=(K)GetJ(p);
    return (I)((I)(x)<64 && tp(x)==0) * (I)x;
}

static K idiom(K x){
    I l=(I)(x) + 8*(nn(x)-2);
    I i=svrb(l),j=svrb(l+8);
    if(j==4 && (i==6 || i==7)){ i=34; } // *& 6 4 -> 40, 6->40(Fwh) 7->41(Las)
    else if(i==14 && j==18){ i=23; } // ?^ 14 18, 14->37(Uqs)
    else { return x; }
    SetJ(l,GetJ(l)+(J)i);
    return ndrop(-1,x);
}

static K e(K x){
    K r,xv,y,yv,ev,a;
    I xs;
    r=(K)0ull;
    xv=(x&1ull); x=(x&~1ull);
    if(x==0ull){ return 0ull; }
    xs=PS;
    y=t();
    yv=(y&1ull); y=(y&~1ull);
    if(y==0ull){ return x+xv; }
    if(yv!=0ull && xv==0ull){
      r=e(t());
      ev=(r&1ull); r=(r&~1ull);
      a=pasn(x,y,r);
      if(a!=0ull){ return a; }
      if(r==0ull || ev==1ull){
        x=cat1(ucat(cat1(cat1(ucat(l1(0ull),x),Ki(2)),27ull),y),92ull);
        if(ev==1ull){ return (cat1(ucat(r,x),91ull)+1ull); }
        return x+1ull;
      }
      return dyadic(ucat(r,x),y);
    }
    r=e(rx(y)+yv);
    ev=(r&1ull); r=(r&~1ull);
    dx(y);
    if(xv==0ull){
      return cat1(ucat(r,x),83ull|((K)(xs)<<32ull));
    } else if((r==y && (xv+yv)==2ull) || ev==1ull){
      return cat1(ucat(r,x),91ull) + 1ull;
    }
    return idiom(monadic(ucat(r,x)));
}

static K es(void){
    K r=mk(T_Lt,0),n,x;
    for(;;){
      n=next();
      if(n==0ull){ break; }
      if(n==59ull){ continue; } // 59 == ';'
      PP-=8;
      x=(e(t()) &~1ull);
      if(x==0ull){ break; }
      if(nn(r)){ r=cat1(r,256ull); } // drop
      r=Cat(r,x);
    }
    return r;
}

static K parse(K x){
    if(tp(x)!=T_Lt){ trap(E_Type); }
    PP=(I)x;
    PE=PP+(8*nn(x));
    K r=es();
    if(PP!=PE){ trap(E_Parse); }
    lfree(x);
    return r;
}

static void ws(void){
    I c=0;
    for(;PP<PE;PP++){
      c=GetC(PP);
      if(c=='\n' || c>32){ break; }
    }
    for(;PP<PE;){
      c=GetC(PP);
      if(c=='/' && GetC(PP-1)<33){
        PP++;
        for(;PP<PE;PP++){
          c=GetC(PP);
          if(c==10){ break; }
        }
      } else { return; }
    }
}

static K tok(K x){
    K s,r,y;
    s=cat1(src(), Kc('\n'));
    PP=nn(s);
    s=Cat(s,x);
    PP+=(I)s;
    PE=PP+nn(x);
    r=mk(T_Lt,0);
    for(;;){
      ws();
      if(PP==PE){ break; }
      for(I i=193;i<199;i++){ // tchr tnms tvrb tpct tvar tsym
        y=((K(*)(void))Fn_[i])();
        if(y != 0ull){
          y=y | (K)((J)(PP-(I)s)<<32ll);
          r=cat1(r,y);
          break;
        }
        if(i==198){ trap(E_Parse); } // unknown token
      }
    }
    SetJ(POS_SRC,(J)s);
    return r;
}

static K Tok(K x){ return (tp(x)==T_Ct) ? tok(x) : x; }
static K Prs(K x){ return parse(Tok(x)); }

static K slam(K r, I ar, I s0){
    I rp=(I)r;
    SetI(rp-12, ar);
    return ((K)(rp) | ((K)(s0)<<32ull)) | ((K)(T_lf)<<59ull);
}

static K plam(I s0){
    K r,slo,n,n2,c,ik,s;
    I ar=-1,ln2,cn,cp,y;
    r=(K)0ull;
    slo=loc_;
    loc_=0ull;
    n=next();
    if(n==91ull){ // '['
      n2=(plist(93ull)&~1ull); // ']'
      ln2=nn(n2);
      loc_=Ech(4ull,l1(n2)); // [a]->,(`a;.)  [a;b]->((`a;.);(`b;.))
      if(ln2>0 && tp(loc_)!=T_St){ trap(E_Parse); }
      ar=nn(loc_);
      if(!ar){
        dx(loc_);
        loc_=mk(T_St,0);
      }
    } else {
      PP-=8;
      loc_=mk(T_St,0);
    }
    c=es();
    n=next();
    if(n!=125ull){ trap(E_Parse); } // '}'
    cn=nn(c);
    cp=(I)c;
    if(ar<0){
      ar=0;
      for(I i=0; i<cn; i++, cp+=8){ // this parses lamda for implicit args
        r=(K)GetJ(cp);
        if(tp(r)==0 && (I)(r)==20){
          r=(K)GetJ(cp-8);
          y=(I)(r)>>3;
          if(tp(r)==T_st && y>0 && y<4){ ar=maxi(ar,y); } // if you use y you also get x and if you use z, you get all 3!
        }
      }
      loc_=Cat(ntake(ar,rx(xyz_)),loc_); // xyz_ are the default implicit args
    }
    ik=Add(seq((1+PS)-s0), Ki(s0-1));
    s=atv(rx(src()),ik);
    r=l3(c,Unq(loc_),s);
    loc_=slo;
    return l1(slam(r,ar,s0));
}

static K plist(K c){
    K p,r,b,x;
    I n=0;
    p=(K)0ull;
    r=mk(T_Lt,0);
    for(;;n++){
      b=next();
      if(b==0ull || b==c){ break; }
      if(!n){ PP-=8; }
      if(n!=0 && b!=59ull){ trap(E_Parse); }
      x=(e(t())&~1ull);
      if(x==0ull){ p=1ull; }
      r=cat1(r,x);
    }
    return r+p;
}

static K rf(K x){
    I rp,n=(I)x;
    K r=mk(T_Ft, n);
    rp=(I)r;
    for(I i=0; i<n; i++, rp+=8){ SetF(rp, 0.5 + rnd() / 4294967295.); }
    dx(x);
    return r;
}

static K roll(K x){
    T xt=tp(x);
    I xp=(I)x;
    return (xt==T_it && xp>0) ? rf(x) : trap(E_Type);
}

static K rd0(I, I, I){ return (K)0ull; }

static F sumf(I xp, I n, I s){
    I m;
    F r=0.;
    if(n<128){
      for(I i=0;i<n;i++, r+=GetF(xp), xp+=s) {}
      return r;
    }
    m=n/2;
    return sumf(xp, m, s) + sumf(xp+s*m, n-m, s);
}

static K sum(I yp, T t, I n){
    F f;
    I xp=0;
    switch(t){
      case T_Ct:
        for(I i=0;i<n;i++) xp+=GetC(yp+i);
        return Kc(xp);
      case T_It: return Ki(xp+sumi(yp,n));
      case T_St: return 0ull;
      case T_Ft:
        f=0.;
        return Kf(f+sumf(yp,n,8));
      default: return 0ull;
    }
}

static K prd(I yp, T t, I n){
    F f;
    I xp=1;
    switch(t){
      case T_Ct:
        for(I i=0;i<n;i++) xp=xp*GetC(yp+i);
        return Kc(xp);
      case T_It:
        for(I i=0;i<n;i++, yp+=4){ xp=xp*GetI(yp); }
        return Ki(xp);
      case T_St: return 0ull;
      case T_Ft:
        f=1.;
        for(I i=0; i<n; i++, yp+=8){ f=f*GetF(yp); }
        return Kf(f);
      default: return 0ull;
    }
}

static K sums(I yp, T t, I n){
    if(t!=T_It){ return 0ull; }
    K r=mk(T_It,n);
    I rp=(I)r,s=0,e=yp+4*n;
    do{ s+=GetI(yp); SetI(rp,s);
    }while(rp+=4, yp+=4, yp<e);
    return r;
}

static K prds(I yp, T t, I n){
    if(t!=T_It){ return 0ull; }
    K r=mk(T_It,n);
    I rp=(I)r,s=1,e=yp+4*n;
    do{ s=s*GetI(yp); SetI(rp,s);
    }while(rp+=4, yp+=4, yp<e);
    return r;
}

static K Abs(K x){ return(tp(x)>=T_Lt) ? Ech(32ull,l1(x)) : nm(227,x); }
static I absi(I x){ return x<0?-x:x; }
static F absf(F x){ return F64abs(x); }
static void absC(I xp, I rp, I e){ do{ SetC(rp,(C)absi(GetC(xp))); }while(xp++, rp++, rp<e); }
static void absI(I xp, I rp, I e){ do{ SetI(rp,absi(GetI(xp))); }while(xp+=4, rp+=4, rp<e); }
static void absF(I xp, I rp, I e){ do{ SetF(rp,F64abs(GetF(xp))); }while(xp+=8, rp+=8, rp<e); }

static K Sqr(K x){
    if((tp(x)&15)!=T_ft){ x=Add(Kf(0.),x); }
    return nm(300,x);
}

static F sqrf(F x){ return F64sqrt(x); }
static void sqrF(I xp, I rp, I e){ do{ SetF(rp,F64sqrt(GetF(xp))); }while(xp+=8, rp+=8, rp<e); }

static K Hyp(K x, K y){
    I xp,yp;
    T xt=tp(x),yt=tp(y);
    if(xt>=T_Lt || yt>=T_Lt){ return Ech(32ull,l2(x,y)); }
    if(xt==T_ft){
      xp=(I)x;
      yp=(I)y;
      dx(x); dx(y);
      if(yt==T_ft){ return Kf(hypot_(GetF(xp),GetF(yp))); }
    }
    return trap(E_Nyi); // TODO: implement
}

static void mrge(I x, I r, I a, I b, I c, I p, I s, I f){
    I q=0,i=a,j=c,k=a;
    for(;k<b;k+=4){
      q=(i<c && j<b) ? ((I(*)(I,I))Fn_[f])(p+s*GetI(x+i),p+s*GetI(x+j)) : 0;
      if(i>=c || q!=0){
        SetI(r+k,GetI(x+j)); j+=4;
      } else {
        SetI(r+k,GetI(x+i)); i+=4;
      }
    }
}

static void msrt(I x, I r, I a, I b, I p, I s, I f){
    if((b-a)<2){ return; }
    I c=((a+b)>>1);
    msrt(r, x, a, c, p, s, f);
    msrt(r, x, c, b, p, s, f);
    mrge(x, r,4*a, 4*b,4*c, p, s, f);
}

static K grade(K x, I f){
    K r,w;
    I n,rp,xp,wp;
    r=(K)0ull;
    T xt=tp(x);
    if(xt<16){ trap(E_Type); }
    if(xt==T_Dt){
      r=x0(x);
      return Atx(r,grade(r1(x),f));
    }
    if(xt==T_Tt){
      w=x0(x1(x));
      r=grade(w, f);
      dx(x);
      return r;
    }
    n=nn(x);
    if(n<2){
      dx(x);
      return seq(n);
    }
    r=seq(n);
    rp=(I)r; xp=(I)x;
    w=mk(T_It,n);
    wp=(I)w;
    Memorycopy(wp, rp, 4*n);
    msrt(wp, rp, 0, n, xp, sz(xt), f+(I)xt);
    dx(w); dx(x);
    return r;
}

static K Asc(K x){ return (tp(x)==T_st) ?
#ifdef SPESH_IO_VERBS
 readfile(cs(x))
#else //!SPESH_IO_VERBS
 trap(E_Io)
#endif //SPESH_IO_VERBS
 : grade(x,343); }

static K Dsc(K x){ return grade(x,336); }

static K Srt(K x){
    K r=(K)0ull,i;
    I xt=tp(x);
    if(xt<16){ trap(E_Type); }
    if(xt==T_Dt){
      r=x0(x); x=r1(x); i=rx(Asc(rx(x)));
      return Key(atv(r,i),atv(x,i));
    }
    if(nn(x)<2){ return x; }
    return atv(x,Asc(rx(x)));
}

static I taoC(I xp, I yp, I n){
    I e=xp+n;
    for(;xp<e; yp++, xp++){
      if(GetC(xp)!=GetC(yp)){ return (I)(GetC(xp)<GetC(yp)); }
    }
    return 2;
}

static I taoI(I xp, I yp, I n){
    I e=(xp+(4*n));
    for(;xp<e; yp+=4, xp+=4){
      if(GetI(xp)!=GetI(yp)){ return (I)(GetI(xp)<GetI(yp)); }
    }
    return 2;
}

static I ltL(K x, K y);
static I taoL(I xp, I yp, I n){
    K x,y;
    I e=xp+8*n;
    for(;xp<e; yp+=8, xp+=8){
      x=(K)GetJ(xp); y=(K)GetJ(yp);
      if(!match(x,y)){ return ltL(x,y); }
    }
    return 2;
}

static I taoF(I xp, I yp, I n){
    F x,y;
    I e=xp+8*n;
    for(;xp<e; yp+=8, xp+=8){
      x=GetF(xp); y=GetF(yp);
      if(!eqf(x,y)){ return ltf(x,y); }
    }
    return 2;
}

static I ltL(K x, K y){
    K a,b;
    I r=0,xp,yp,xn,yn,n;
    T xt=tp(x);
    if(xt!=tp(y)){ return (I)(xt<tp(y)); }
    if(xt<16){ return (I)Les(rx(x),rx(y)); }
    xp=(I)x;
    yp=(I)y;
    if(xt>T_Lt){
      a=(K)GetJ(xp);
      b=(K)GetJ(yp);
      if(!match(a,b)){ return ltL(a,b); }
      return ltL((K)GetJ(xp+8), (K)GetJ(yp+8));
    }
    xn=nn(x);
    yn=nn(y);
    n=mini(xn,yn);
    switch(sz(xt)>>2){
      case 0: r=taoC(xp,yp,n); break;
      case 1: r=taoI(xp,yp,n); break;
      case 2: r=(xt==T_Lt) ? taoL(xp,yp,n) : taoF(xp,yp,n);
        break;
    }
    return (r==2) ? (I)(xn<yn) : r;
}

static I guC(I xp, I yp){ return (I)(GetC(xp)<GetC(yp)); }
static I guI(I xp, I yp){ return (I)(GetI(xp)<GetI(yp)); }
static I guF(I xp, I yp){ return ltf(GetF(xp),GetF(yp)); }
static I guL(I xp, I yp){ return ltL((K)GetJ(xp),(K)GetJ(yp)); }
static I gdC(I xp, I yp){ return (I)(GetC(xp)>GetC(yp)); }
static I gdI(I xp, I yp){ return (I)(GetI(xp)>GetI(yp)); }
static I gdF(I xp, I yp){ return guF(yp,xp); }
static I gdL(I xp, I yp){ return guL(yp,xp); }

static K emb(I a, I b, K x){ return cat1(Cat(Kc(a),x),Kc(b)); }

static K si(I x){
    K r;
    if(!x){ return Ku((K)48ull); } // '0'
    else if(x==nai){ return Ku(20016ull); } // 0N
    else if(x<0){ return ucat(Ku((K)45ull),si(-x)); } // '-'
    r=mk(T_Ct,0);
    for(;x;x/=10){ r=cat1(r,Kc('0'+x%10)); }
    return Rev(r);
}

static K sf(F x);
static K se(F x){
    I ei;
    F f=x;
    J e=(J)0ll;
    if(frexp1(x)){
      f=frexp2(x); e=frexp3(x);
    }
    x=0.3010299956639812*(F)e;
    ei=(I)F64floor(x);
    x=x-(F)ei;
    return ucat(cat1(sf(f*pow_(10.,x)),Kc('e')),si(ei));
}

static K sf(F x){
    K r;
    I c=0,n,rp;
    J i;
    UJ u;
    if(x!=x){ return Ku(28208ull); } // 0N
    u=(UJ)I64reinterpret_f64(x);
    if(u==(UJ)0x7ff0000000000000ull){ return Ku(30512ull); } // 0w
    else if(u==(UJ)0xfff0000000000000ull){ return Ku(7811117ull); } // -0w
    if(x<0.){ return ucat(Ku((K)45ull),sf(-x)); } // '-'
    if(x>0. && (x>=1.e6 || x<=1e-06)){ return se(x); }
    r=mk(T_Ct,0);
    i=(J)x;
    if(i==0ll){ r=cat1(r,Kc('0')); }
    for(;i!=0ll; i/=10ll){ r=cat1(r,Kc((I)(48ll+i%10ll))); } // '0'
    r=Rev(r);
    r=cat1(r,Kc('.'));
    x=x-F64floor(x);
    for(I j=0;j<6;j++){
      x=x*10.; r=cat1(r,Kc('0'+((I)(x)%10)));
    }
    n=nn(r);
    rp=(I)r;
    for(I j=0;j<n;j++, rp++){
      if(GetC(rp)=='0'){ c++; }
      else { c=0; }
    }
    return ndrop(-c,r);
}

static K Str(K x){
    K r,p,f,l,i;
    I xp,ip;
    r=(K)0ull;
    T xt=tp(x);
    T ft;
    if(xt>16){ return Ech(17ull,l1(x)); } // monad 17 = Str
    xp=(I)x;
    if(xt>T_dt){
      switch (xt) {
        case T_cf:
          rx(x);
          r=ucats(Rev(Str((K)(xp) | ((K)(T_Lt)<<59ull))));
          break;
        case T_df:
          r=Str(x0(x));
          p=x1(x);
          p=((I)(p)%2) ? cat1(Str(20ull+p),Kc(':')) : Str(21ull+p);
          r=ucat(r,p);
          break;
        case T_pf:
          f=x0(x); l=x1(x); i=x2(x);
          ft=tp(f); f=Str(f);
          dx(i);
          r=(nn(i)==1 && GetI((I)i)==1 && (ft==0 || ft==T_df)) ? ucat(Kst(Fst(l)),f) : ucat(f,emb(91,93,ndrop(-1,ndrop(1,Kst(l)))));
          break;
        case T_lf: r=x2(x); break;
        default: r=x1(x); break; // native
      }
      dx(x);
      return r;
    } else {
      switch(xt){
        case 0:
          if(xp>QUOTE){ return Str((K)(xp)-QUOTE); }
          ip=xp;
          switch(xp>>6){
            case 0:
              if(!xp){ return mk(T_Ct,0); } // 0..63 monadic
              break;
            case 1: ip=ip-64; break; // 64..127 dyadic
            case 2: ip=ip-128; break; // 128 dyadic indirect
            case 3: ip=ip-192; break; // 192 tetradic
          }
          if(ip>25 || ip==0){ return ucat(Ku(96ull),si(xp)); } // '`'
          r=Ku((UJ)Verbs[ip-1]);
          break;
        case 1: r=0ull; break; // not reached
        case T_ct: r=Ku((K)xp); break;
        case T_it: r=si(xp); break;
        case T_st: r=cs(x); break;
        case T_ft: r=sf(GetF(xp)); break;
      }
    }
    dx(x);
    return r;
}

static K fmtI(I xp, K r, I n){
    for(I i=0; i<n; i++, xp+=4){
      if(i){ r=ucat(r, Ku(32ull)); }
      r=ucat(r, si(GetI(xp)));
    } return r;
}

static K fmtF(I xp, K r, I n){
    for(I i=0; i<n; i++, xp+=8){
      if(i){ r=ucat(r, Ku(32ull)); }
      r=ucat(r, sf(GetF(xp)));
    } return r;
}

static K fmtD(K x, K r){
    K k=x0(x),v=x1(x); I kn=nn(k);
    if(kn<2 || tp(k)>T_Lt){ r=ucat(r, Ku(40ull)); } // (
    r=ucat(r, Kst(k)); // key list
    if(kn<2 || tp(k)>T_Lt){ r=ucat(r, Ku(41ull)); } // )
    r=ucat(r, Ku(33ull)); // !
    return ucat(r, Kst(v)); // value list
}

static K fmtL(I xp, K r, I n){
    if(n!=1){ r=ucat(r, Ku(40ull)); } // (
    for(I i=0; i<n; i++, xp+=8){
      if(i){ r=ucat(r, Ku(59ull)); } // ;
      K v=Kst( (K)GetJ(xp) );
      r=ucat(r, v);
    }
    if(n!=1){ r=ucat(r, Ku(41ull)); } // )
    return r;
}

static K fmtS(I xp, K r, I n){
    for(I i=0; i<n; i++, xp+=4){
      r=ucat(r, Ku(96ull)); // `
      r=ucat(r, cs((K)GetI(xp)));
    } return r;
}

static K fmthx(I c, K r, I s){
    if(s)r=ucat(r, Ku(0x7830ull)); // 0x
    C hx[3]; snprintf(hx, 3, "%02x", c);
    r=cat1(r, Kc((I)hx[0]));
    return cat1(r, Kc((I)hx[1]));
}

static K fmtc(I c, K r, I s){
    if(c>'~' || (c<' ' && c!='\n' && c!='\r' && c!='\t')){
      return fmthx(c, r, s);
    } else {
      I cc=c;
      if(s){ r=ucat(r, Ku(34ull)); } // "
      if     (c=='\n'){ r=ucat(r, Ku(92ull)); cc='n' ; }
      else if(c=='\r'){ r=ucat(r, Ku(92ull)); cc='r' ; }
      else if(c=='\t'){ r=ucat(r, Ku(92ull)); cc='t' ; }
      else if(c=='"' ){ r=ucat(r, Ku(92ull)); cc='"' ; }
      else if(c=='\\'){ r=ucat(r, Ku(92ull)); cc='\\'; }
      r=cat1(r, (K)cc);
      return (s) ? ucat(r, Ku(34ull)) : r; // "
    }
}

static K fmtC(I xp, K r, I n){
    I c,hx=0;
    for(I i=0;i<n;i++){
      c=GetC(xp+i);
      if(c>'~'||(c<' ' && c!='\n' && c!='\r' && c!='\t')){
       hx=1; break;
      }
    }
    if(hx){
      r=ucat(r, Ku(0x7830ull)); // 0x
      for(I i=0;i<n;i++){
        c=GetC(xp+i); r=fmthx(c, r, 0);
      } return r;
    } else {
      r=ucat(r, Ku(34ull)); // "
      for(I i=0;i<n;i++){
        c=GetC(xp+i); r=fmtc(c, r, 0);
      }
      return ucat(r, Ku(34ull)); // "
    }
}

static K Kst(K x){
    T xt=tp(x);
    if(xt==T_it || xt==T_ft) { return Str(rx(x)); }
    K r=mk(T_Ct, 0);
    I xn=(xt>6) ? nn(x) : 0;
    if(xn==0){
      switch(xt){
        case T_Ft: return Ku(0x2E302330ull); // 0#0.
        case T_It: return Ku(0x3021ull); // !0
        case T_St: return Ku(0x602330ull); // 0#`
      }
    }
    if(xn==1 && xt>16 && xt<=T_Lt){ r=ucat(r, Ku(44ull)); } // ,
    if(xt==T_It) { return fmtI((I)x, r, xn); }
    if(xt==T_Ft) { return fmtF((I)x, r, xn); }
    if(xt==T_Tt) {
      xt=T_Dt; r=ucat(r, Ku(43ull)); // +
    }
    if(xt==T_Dt) { return fmtD(x, r); }
    if(xt==T_Lt) { return fmtL((I)x, r, xn); }
    if(xt==T_st) {
      r=ucat(r, Ku(96ull)); // `
      r=ucat(r, cs(x));
      return r;
    }
    if(xt==T_St) { return fmtS((I)x, r, xn); }
    if(xt==T_ct) { return fmtc((I)x, r, 1); }
    if(xt==T_Ct) { return fmtC((I)x, r, xn); }
    dx(r);
    return Str(rx(x));
}

static K tvar(void){
    K r;
    I c=GetC(PP);
    if(!is(c,0x2)){ return 0ull; }
    PP++;
    r=Ku((K)c);
    for(;PP<PE;PP++){
      c=GetC(PP);
      if(!is(c,0x6)){ break; }
      r=cat1(r,((K)(c) | ((K)(T_ct)<<59ull)));
    }
    return sc(r);
}

static I hx(I c){ return is(c,0x4)?(c-'0'):(c-'W'); }
static K thex(void){
    I c;
    K r=mk(T_Ct,0);
    for(;PP<PE-1;PP+=2){
      c=GetC(PP);
      if(!is(c,0x80)){ break; } // 0123456789abcdef
      r=cat1(r,Kc(((hx(c)<<4)+hx(GetC(1+PP)))));
    }
    if(nn(r)==1){ return Fst(r); }
    return r;
}

static I cq(I c){
    if(c=='t'){ return '\t'; }
    if(c=='n'){ return '\n'; }
    if(c=='r'){ return '\r'; }
    return c;
}

static K tchr(void){
    K r;
    I c, q;
    if(GetC(PP)=='0' && PP<PE && GetC(1+PP)=='x'){
      PP+=2;
      return thex();
    }
    if(GetC(PP)!='"'){ return 0ull; }
    PP++;
    r=mk(T_Ct,0);
    q=0;
    for(;;){
      if(PP==PE){ trap(E_Parse); }
      c=GetC(PP++);
      if(c=='"' && q==0){ break; }
      if(c=='\\' && q==0){ q=1; continue; }
      if(q){ c=cq(c); q=0; }
      r=cat1(r,Kc(c));
    }
    if(nn(r)==1){ return Fst(r); }
    return r;
}

static K tsym(void){
    K r,s;
    r=(K)0ull;
    for(;GetC(PP)=='`';){
      ++PP;
      if(r==0ull){ r=mk(T_St,0); }
      s=(K)0ull;
      if(PP<PE){
        s=tchr();
        if(s==0ull) { s=tvar(); }
        else if(tp(s)==T_ct){ s=sc(Enl(s)); }
        else { s=sc(s); }
      }
      if(s==0ull){ s=(K)(T_st)<<59ull; }
      r=cat1(r,s);
      if(PP==PE){ break; }
    }
    return r;
}

static J pu(void){
    I c;
    J r=0;
    for(;PP<PE;PP++){
      c=GetC(PP);
      if(!is(c,0x4)){ break; }
      r=10ll*r+(J)(c-48);
    }
    return r;
}

static F pexp(F f){
    I c;
    J e=1;
    if(++PP<PE){
      c=GetC(PP);
      if(c=='-' || c=='+'){
      ++PP; if(c=='-'){ e=(J)(-1ll); }
      }
    }
    e=e*pu();
    return f * pow_(10.,(F)e);
}

static K ppi(F f){
    ++PP; return Kf(pi*f);
}

static K pflt(J i){
    I c=0;
    F d=1., f=(F)i;
    PP++;
    for(;PP<PE;PP++){
      c=GetC(PP);
      if(!is(c,0x4)){ break; }
      d=d/10.;
      f+=d*(F)(c-48);
    }
    if(PP<PE){
      c=GetC(PP);
      if(c=='e' || c=='E'){ f=pexp(f); }
    }
    if(PP<PE){
      c=GetC(PP);
      if(c=='p'){ return ppi(f); }
    }
    return Kf(f);
}

static K tunm(void){
    K q;
    I p=PP,c;
    J r=pu();
    if(r==0ll && p==PP){
      return (GetC(p)=='.' && is(GetC(1+p),0x4)) ? pflt(r) : 0ull;
    }
    if(PP<PE){
      c=GetC(PP);
      if(c=='.'){ return pflt(r); }
      if(c=='p'){ return ppi((F)r); }
      if(c=='e' || c=='E'){ return Kf(pexp((F)r)); }
      if(r==0ll){
        if(c=='N'){
          ++PP; return missing(T_it);
        }
        if(c=='n' || c=='w'){
          q=Kf(0.); SetJ((I)q,(J)0x7ff8000000000001ll);
          if(c=='w'){ SetF((I)q, F64inf); }
          ++PP; return q;
        }
      }
    }
    return Ki((I)r);
}
static K tnum(void){
    K r;
    I c=GetC(PP);
    if((c=='-' || c=='.') && is(GetC(PP-1),0x40)){ return (K)0ull; }
    if(c=='-' && PP++<(1+PE)){
      r=tunm();
      if(r==0ull){
        --PP; return (K)0ull;
      }
      return Neg(r);
    }
    return tunm();
}
static K tnms(void){
    K x, r;
    r=tnum();
    for(;PP<PE-1 && GetC(PP)==' ';){
      ++PP; x=tnum();
      if(x==0ull){ break; }
      r=ncat(r,x);
    }
    return r;
}
static K prs(T t, K y){
    I yp,yn,p,e;
    K r=(K)0ull;
    yp=(I)y; yn=nn(y);
    p=PP; e=PE;
    PP=yp; PE=yp+yn;
    if((t&15)==2){ return (t==T_Ct)?y:Fst(y); }
    if(t==4){
      r=Fst(tsym());
    } else if(t>2 && t<=6){
      r=tnum();
      if(tp(r)<t && r!=0ull){ r=uptype(r,t); }
    }
    if(t>T_Ct && t<T_Lt){
      if(PP==PE){
        r=mk(t,0);
      } else if(t==T_St){
        r=tsym();
      } else {
        r=tnms();
        if((tp(r)&15)<(t&15) && r!=0ull){
          r=uptype(r, t&15);
        }
      }
      if(tp(r)==t-16){ r=Enl(r); }
    }
    if(tp(r)!=t || PP<PE){
      dx(r); r=0ull;
    }
    PP=p; PE=e;
    dx(y);
    return r;
}
static T ts(K x){ // char -> T
    I c=(I)Fst(cs(x));
    for(I i=0; i<26; i++){
      if(c==Types[i]){ return (T)i; }
    }
    trap(E_Value);
    return (T)0;
}
static K pad(K x, K y){
    // TODO: implement
    // 5$"abc" -> "abc  "
    // -3$"a" -> "  a"
    dx(x);
    return y;
}
static K Cst(K x, K y){
    T yt=tp(y);
    if(yt>=T_Lt){ return Ecr(17ull,l2(x,y)); } // dyad 17 = Cst
    if(tp(x)==T_it){ return pad(x, y); }
    if(tp(x)!=T_st){ trap(E_Type); }
    if(!(I)x){ // `$"abc" -> `abc
      if(yt==T_ct){ return sc(Enl(y)); }
      if(yt!=T_Ct){ trap(E_Type); }
      return sc(y);
    }
    T dst=ts(x);
    if(dst==T_it || dst==T_ft || dst==T_ct) {
      if(dst==yt){ return y; }
      I yp=(I)y;
      if(yt<16){
        if(yt==T_ft){ yp=(I)F64floor(GetF(yp)); }
        switch(dst){
          case T_it: return Ki(yp);
          case T_ft: return Kf(yp);
          case T_ct: return Kc(yp);
        }
      } else if(yt==T_It || yt==T_Ft || yt==T_Ct){
        if(yt-16==dst){ return y; }
        I yn=nn(y);
        K r=mk(dst+16,yn); I rp=(I)r;
        if(yt==T_Ct){
          if(dst==T_it){
            for(I i=0;i<yn;i++, yp++, rp+=4){ SetI(rp,GetC(yp)); }
          } else {
            for(I i=0;i<yn;i++, yp++, rp+=8){ SetF(rp,GetC(yp)); }
          }
        } else if(yt==T_It){
          if(dst==T_ct){
            for(I i=0;i<yn;i++, yp+=4, rp++){ SetC(rp,(C)GetI(yp)); }
          } else {
            for(I i=0;i<yn;i++, yp+=4, rp+=8){ SetF(rp,GetI(yp)); }
          }
        } else if(yt==T_Ft){
          if(dst==T_it){
            for(I i=0;i<yn;i++, yp+=8, rp+=4){ SetI(rp,(I)F64floor(GetF(yp))); }
          } else {
            for(I i=0;i<yn;i++, yp+=8, rp++){ SetC(rp,(C)F64floor(GetF(yp))); }
          }
        }
        return r;
      }
    }
    if(yt==T_ct){
      y=Enl(y); yt=T_Ct;
    }
    if(yt!=T_Ct){ trap(E_Type); }
    return prs(dst,y);
}

static K Rtp(K y, K x){
    I t=ts(y),n,s;
    T xt=tp(x);
    t+=16*(I)(t<16);
    if(xt<16 || t<17 || t>=T_Lt){ trap(E_Type); }
    n=(nn(x)*sz(xt));
    s=sz(t);
    if(n%s){ trap(E_Length); }
    x=use(x);
    SetI((I)(x)-12,n/s);
    x=((K)(t)<<59ull) | (K)((I)x);
    return x;
}

static K tvrb(void){
    I o,c=GetC(PP);
    if(!is(c, 0x1)){ return (K)0ull; }
    PP++;
    if(c=='\\' && GetC(PP-2)==' '){ return (K)29ull; } // 29 = Out/Otu
    o=1;
    if(PP<PE && GetC(PP)==':'){
      PP++;
      if(is(c, 0x8)){ trap(E_Parse); }
      o=97; // 'a'
    }
    for(I i=0; i<26; i++){ if(Verbs[i]==c){ return (K)(o+i); } }
    trap(E_Parse);
    return (K)(o-1);
}

static K tpct(void){
    I c=GetC(PP);
    if(is(c,0x30)){ // ([{}]);
      ++PP; return (K)c;
    }
    if(c==10){
      ++PP; return (K)59ull;
    }
    return (K)0ull;
}

static K nyi(K){ return trap(E_Nyi); }

static K Idy(K x){ return x; }

static K Dex(K x, K y){
    dx(x); return y;
}

static K Flp(K x){
    K m,t;
    T xt=tp(x);
    I n,xp;
    switch(xt){
      case T_Lt:
        n=nn(x); xp=(I)x;
        m=Ki(maxcount(xp,n));
        return x=Atx(Rdc(13ull,l1(Ecr(15ull,l2(m,x)))),Ecl(2ull,l2(Til(m),Mul(m,Til(Ki(n)))))); // m13=Enl d15=Tak d2=Add
      case T_Dt: return td(x);
      case T_Tt:
        t=x0(x);
        return Key(t,r1(x));
      default: return x;
    }
}

static K odo(K x){
    K y, r;
    I n,xp,yp,w=1,s=0,c,rps;
    n=maxi(nn(x),0);
    r=mk(T_Lt,0);
    if(!n){ return r; }
    xp=(I)x;
    for(I i=0; i<n; i++, xp+=4){
      c=GetI((I)xp);
      s+=c; w*=c;
    }
    xp=(I)x;
    rps=s;
    for(I i=0; i<n; i++, xp+=4){
      c=GetI((I)xp);
      y=mk(T_It, w); yp=(I)y;
      rps=rps-c;
      for(I j=0, k=0, l=0; k<w; k++, yp+=4){
        ++l; SetI(yp, j);
        if(rps==0 || l==rps){
          l=0; if(++j==c){ j=0; }
        }
      }
      r=cat1(r, y);
    }
    return r;
}

static K Til(K x){
    K y;
    T xt=tp(x);
    if(xt>T_Lt){
      y=x0(x); dx(x); return y;
    }
    if(xt==T_it){ return seq((I)x); }
    if(xt==T_It){ return odo(x); }
    return trap(E_Type);
}

static K Unq(K x){
    I xn;
    K r,xi;
    T xt=tp(x);
    if(xt<16){ return roll(x); }
    if(xt>=T_Lt){
      if(xt==T_Dt){ trap(E_Type); }
      if(xt==T_Tt){
        r=x0(x); x=r1(x);
        return key(r,Flp(Unq(Flp(x))),xt);
      }
      return uqf(x);
    }
    xn=nn(x);
    r=mk(xt,0);
    for(I i=0;i<xn;i++){
      xi=ati(rx(x),i);
      if(!(I)In(rx(xi),rx(r))){ r=cat1(r,xi); }
      else { dx(xi); }
    }
    dx(x);
    return r;
}

static K Uqs(K x){
    T xt=tp(x);
    if(xt<16){ trap(E_Type); }
    return Srt(uqf(x));
}

static K Key(K x, K y){ return key(x,y,T_Dt); }

static K ntake(I n, K y){
    I yp,s,rp,yn;
    F f;
    K r=(K)0ull;
    T t=tp(y);
    if(n==nai){ n=t<16 ? 1 : nn(y); }
    if(n<0){
      if(tp(y)<16){ return ntake(-n,y); }
      n+=nn(y);
      return (n<0) ? ucat(ntake(-n,missing(t-16)),y) : ndrop(n,y);
    }
    yp=(I)y;
    if(t<5){
      t+=16; s=sz(t);
      r=mk(t,n); rp=(I)r;
      if(s==1){
        Memoryfill(rp,yp,n);
      } else {
        for(I i=0; i<n; i++, rp+=4){ SetI(rp,yp); }
      }
      return r;
    } else if(t==T_ft){
      r=mk(T_Ft,n); rp=(I)r;
      f=GetF(yp);
      for(I i=0; i<n; i++, rp+=8){ SetF(rp,f); }
      dx(y);
      return r;
    } else if(t<16){
      r=mk(T_Lt,n); rp=(I)r;
      for(I i=0; i<n; i++, rp+=8){ SetJ(rp,(J)rx(y)); }
      dx(y);
      return r;
    }
    r=seq(n);
    yn=nn(y);
    if(n>yn && yn>0){ r=idiv(r,Ki(yn),1); }
    return atv(y,r);
}

static K Wer(K x){
    I xn,xp,n,rp,j;
    K r=(K)0ull;
    T t=tp(x);
    if(t<16){
      x=Enl(x); t=tp(x);
    }
    if(t==T_Dt){
      r=x0(x); return Atx(r,Wer(r1(x)));
    }
    xn=nn(x); xp=(I)x;
    if(t==T_It){
      n=sumi(xp,xn);
      r=mk(T_It,n); rp=(I)r;
      for(I i=0;i<xn;i++, xp+=4){
        j=GetI(xp);
        for(I k=0; k<j; k++, rp+=4){ SetI(rp,i); }
      }
    } else {
      r=(!xn) ? mk(T_It,0) : trap(E_Type);
    }
    dx(x);
    return r;
}

static K Tak(K x, K y){
    K r;
    T xt=tp(x),yt=tp(y);
    if(yt==T_Dt){
      x=rx(x);
      if(xt==T_it){
        r=x0(y); y=r1(y);
        r=Tak(x,r); y=Tak(x,y);
        return Key(r,y);
      } else {
        return Key(x,Atx(y,x));
      }
    } else {
      if(yt==T_Tt){
        if((xt&15)==T_st){
          if(xt==T_st){ x=Enl(x); }
          x=rx(x);
          return key(x,Atx(y,x),yt);
        } else {
          return Ecr(15ull,l2(x,y)); // dyad 15 = Tak
        }
      }
    }
    if(xt==T_it){ return ntake((I)x,y); }
    y=rx(y);
    return (xt>16 && xt==yt) ? atv(y,Wer(In(y,x))) : Atx(y,Wer(Cal(x,l1(y))));
}

static K ndrop(I n, K y){
    I yn,rn,s,yp;
    K r=(K)0ull;
    T yt=tp(y);
    if(yt<16 || yt>T_Lt){ trap(E_Type); }
    yn=nn(y);
    if(n<0){ return ntake(maxi(0,yn+n),y); }
    rn=yn-n;
    if(rn<0){
      dx(y); return mk(yt,0);
    }
    s=sz(yt);
    yp=(I)y;
    if(GetI(yp-4)==1 && bucket(s*yn)==bucket(s*rn) && yt<T_Lt){
      r=rx(y);
      SetI((yp-12), rn);
      memmove(M_+(I)r, M_+(yp+s*n), (size_t)(s*rn));
    } else {
      r=mk(yt, rn);
      Memorycopy((I)r, yp+s*n, s*rn);
    }
    if(yt==T_Lt){
      rl(r); r=uf(r);
    }
    dx(y);
    return r;
}

static K Drp(K x, K y){
    K r;
    T xt=tp(x),yt=tp(y);
    if(yt>T_Lt){
      if(yt==T_Dt || (yt==T_Tt && (xt&15)==T_st)){
        r=x0(y); y=r1(y);
        if(xt<16){ x=Enl(x); }
        x=rx(Wer(Not(In(rx(r),x))));
        return key(Atx(r,x),Atx(y,x),yt);
      } else {
        return Ecr(16ull,l2(x,y)); // dyad 16 = Drp
      }
    }
    if(xt==T_it){ return ndrop((I)x,y); }
    if(xt>16 && xt==yt){ return atv(y,Wer(Not(In(rx(y),x)))); }
    if(yt==T_it){ return atv(x,Wer(Not(Eql(y,seq(nn(x)))))); }
    return Atx(y,Wer(Not(Cal(x,l1(rx(y))))));
}

static K rcut(K x, K a, K b){
    K r;
    I n,ap,bp,rp,o,on;
    n=nn(a);
    ap=(I)a; bp=(I)b;
    r=mk(T_Lt,n); rp=(I)r;
    for(I i=0; i<n; i++, rp+=8, ap+=4, bp+=4){
      o=GetI(ap); on=GetI(bp)-o;
      if(on<0){ trap(E_Value); }
      SetJ(rp,(J)atv(rx(x),Add(Ki(o),seq(on))));
    }
    dx(a); dx(b); dx(x);
    return r;
}

static K cuts(K x, K y){
    return rcut(y,x,cat1(ndrop(1,rx(x)),Ki(nn(y))));
}

static K Cut(K x, K y){
    K r;
    I xp,rp,e,n;
    T yt=tp(y),xt;
    if(yt==T_it || yt==T_ft){ return Pow(y,x); }
    xt=tp(x);
    if(xt==T_It){ return cuts(x,y); }
    if(xt==T_Ct && yt==T_Ct){
      x=rx(Wer(In(rx(y),x)));
      return rcut(y,Cat(Ki(0),Add(Ki(1),x)),Cat(x,Ki(nn(y))));
    }
    if(xt!=T_it || yt<16){ trap(E_Type); }
    xp=(I)x;
    if(xp<=0){ xp=nn(y)/-xp; }
    r=mk(T_Lt,xp); rp=(I)r;
    e=ep(r);
    n=nn(y)/xp;
    x=seq(n);
    do{
      SetJ(rp,(J)atv(rx(y),rx(x)));
      x=Add(Ki(n),x);
    }while(rp+=8, rp<e);
    dx(x); dx(y);
    return r;
}

static K split(K x, K y){
    I xn=1;
    T xt=tp(x),yt=tp(y);
    if(yt==(xt+16)){
      x=Wer(Eql(x,rx(y)));
    } else {
      if(xt==yt && xt==T_Ct){
        xn=nn(x);
        x=Find(x,rx(y));
      } else {
        trap(E_Type);
      }
    }
    x=rx(x);
    return rcut(y,Cat(Ki(0),Add(Ki(xn),x)),cat1(x,Ki(nn(y))));
}

static K join(K x, K y){
    K r,v;
    I yp,yn;
    T xt=tp(x),yt;
    if(xt<16){
      x=Enl(x); xt=tp(x);
    }
    yt=tp(y);
    if(yt!=T_Lt){ trap(E_Type); }
    yp=(I)y; yn=nn(y);
    r=mk(xt,0);
    for(I i=0; i<yn; i++, yp+=8){
      v=x0((K)yp);
      if(tp(v)!=xt){ trap(E_Type); }
      if(i>0){ r=ucat(r,rx(x)); }
      r=ucat(r,v);
    }
    dx(x); dx(y);
    return r;
}

static I ibin(K x, K y, T t){
    I h=0,n,xp,yp,j;
    F f;
    n=nn(x); j=n-1;
    xp=(I)x; yp=(I)y;
    switch(sz(t)>>2){
      case 0:
        for(I k=0;;){ if(k>j){ return k-1; }
          h=(k+j)>>1;
          if(GetC(xp+h)>yp){ j=h-1; }
          else { k=h+1; }
        }
        break;
      case 1:
        for(I k=0;;){ if(k>j){ return k-1; }
          h=(k+j)>>1;
          if(GetI(xp+4*h)>yp){ j=h-1; }
          else { k=h+1; }
        }
        break;
      default:
        f=GetF(yp);
        for(I k=0;;){ if(k>j){ return (k-1); }
          h=(k+j)>>1;
          if(GetF(xp+8*h)>f){ j=h-1; }
          else { k=h+1; }
        }
        break;
    }
    return 0;
}

static K win(I n, K x){
    K y=seq(n),r=mk(T_Lt,0);
    I m=(1+nn(x))-n;
    for(I i=0; i<m; i++){
      r=ucat(r,l1(atv(rx(x),rx(y))));
      y=Add(Ki(1),y);
    }
    dx(x); dx(y);
    return r;
}

static K Bin(K x, K y){
    K r=(K)0ull;
    T xt=tp(x),yt=tp(y);
    if(xt<16 || xt>T_Ft){
      return (xt==T_it && yt>16) ? win((I)x,y) : trap(E_Type);
    }
    if(xt==yt || yt==T_Lt){
      return Ecr(40ull,l2(x,y)); // dyad 40 = Bin
    } else if(xt==yt+16){
      r=Ki(ibin(x,y,xt));
    } else {
      trap(E_Type);
    }
    dx(x); dx(y);
    return r;
}

static C lc(C x){ return (x>='A' && x<='Z') ? x+32 : x; }
static K lower(K x){
    I p,e;
    x=use(x); p=(I)x; e=p+nn(x);
    for(;p<e;p++){ SetC(p,lc(GetC(p))); }
    return x;
}

static K Flr(K x){
    I rp,xp=(I)x,xn;
    K r=(K)0ull;
    T xt=tp(x);
    if(xt<16){
      switch(xt){
        case T_ct: return Kc(lc((C)xp));
        case T_it: return x;
        case T_st: return sc(lower(cs(x)));
        case T_ft:
          dx(x);
          return Ki((I)F64floor(GetF(xp)));
        default: return x;
      }
    }
    xn=nn(x);
    switch(xt){
      case T_Ct: return lower(x);
      case T_It: return x;
      case T_Ft:
        r=mk(T_It,xn); rp=(I)r;
        for(I i=0;i<xn;i++, xp+=8, rp+=4){ SetI(rp,(I)F64floor(GetF(xp))); }
        break;
      default: return Ech(16ull,l1(x));
    }
    dx(x);
    return r;
}
static K Rev(K x){
   I xn,rp;
   K r=(K)0ull;
   T t=tp(x);
   if(t<16){ return x; }
   if(t==T_Dt){
      r=x0(x);
      return Key(Rev(r),Rev(r1(x)));
   }
   xn=nn(x);
   if(xn<2){ return x; }
   r=mk(T_It,xn); rp=(I)(r)+4*xn;
   for(I i=0; i<xn; i++){
      rp-=4;
      SetI(rp,i);
   }
   return atv(x,r);
}
static I fwh(I xp, I n){
   I p=xp,e=xp+4*n;
   for(;p<e; p+=4){
      if(GetC(p)){ return ((p-xp)>>2); }
   }
   return nai;
}

static K Fwh(K x){
   if(tp(x)==T_It){
      dx(x);
      return Ki(fwh((I)x, nn(x)));
   }
   return Fst(Wer(x));
}

static K Typ(K x){ // T -> char
   T t=tp(x); dx(x);
   return (t<0 || t>25) ? sc(Enl(Kc(0x0))) : sc(Enl(Kc(Types[(I)t])));
}

static K val(K x){
   I xn,xp,asn=0;
   x=parse(tok(x));
   xn=nn(x);
   xp=(I)(x) + 8*(xn-1);
   if(xn>2 && GetJ(xp)==64ll){ asn=1; }
   x=exec(x);
   if(asn){
      dx(x); return (K)0ull;
   }
   return x;
}

static K Val(K x){
   K r=(K)0ull;
   T xt=tp(x);
   if(xt==T_st){ return lup(x); }
   if(xt==T_Ct){ return val(x); }
   if(xt==T_lf || xt==T_xf){
      r=l2(x0(x),x1(x));
      if(xt==T_lf){ r=cat1(r,x2(x)); }
      r=cat1(r,Ki(nn(x)));
      dx(x);
      return r;
   }
   if(xt==T_Lt){ return exec(x); }
   if(xt>T_Lt){
      r=x1(x); dx(x); return r;
   }
   return trap(E_Type);
}

static K Ech(K f, K x){
   I xn,rp;
   T t=tp(f),xt;
   K r=(K)0ull;
   if(!isfunc(t)){ return Bin(f,Fst(x)); }
   if(nn(x)==1){ x=Fst(x); }
   else { return ecn(f,x); }
   if(tp(x)<16){ trap(E_Type); }
   xt=tp(x);
   if(xt==T_Dt){
      r=x0(x);
      return Key(r,Ech(f,l1(r1(x))));
   }
   if(xt==T_Tt){ x=explode(x); }
   xn=nn(x);
   r=mk(T_Lt,xn); rp=(I)r;
   for(I i=0; i<xn; i++, rp+=8){ SetJ(rp,(J)Atx(rx(f),ati(rx(x),i))); }
   dx(f); dx(x);
   return uf(r);
}

static void zfuncs(void){
   C *z = "abs:`32;sin:`44;cos:`39;find:`31;exp:`42;log:`43\n";
   size_t zn = strlen(z);
   K x=mk(T_Ct, (I)zn);
   memcpy(M_+((I)x), z, zn);
   dx(Val(x));
}

static I dfi_ = 0;
static void df_(void* f){ Fn_[dfi_++]= f; }
void kinit(void){
   K x,y,z;
   Memory(1);
   minit(9,14); // 512..16k
   Fn_=malloc(379*sizeof(void*));

   //            0        :        +        -        *        %        &        |        <        >        =10      ~        !        ,        ^        #        _        $        ?        @        .20      '        ':       /        /:       \        \:                                  30                                           35                                           40                                           45
   dfi_=0;   df_(nul);df_(Idy);df_(Flp);df_(Neg);df_(Fst);df_(Sqr);df_(Wer);df_(Rev);df_(Asc);df_(Dsc);df_(Grp);df_(Not);df_(Til);df_(Enl);df_(Srt);df_(Cnt);df_(Flr);df_(Str);df_(Unq);df_(Typ);df_(Val);df_(ech);df_(nyi);df_(rdc);df_(nyi);df_(scn);df_(nyi);df_(lst);df_(Kst);df_(Out);df_(nyi);df_(nyi);df_(Abs);df_(nyi);df_(nyi);df_(nyi);df_(nyi);df_(Uqs);df_(nyi);df_(Cos);df_(Fwh);df_(Las);df_(Exp);df_(Log);df_(Sin);df_(Tok);df_(Prs);
   dfi_=64;  df_(Asn);df_(Dex);df_(Add);df_(Sub);df_(Mul);df_(Div);df_(Min);df_(Max);df_(Les);df_(Mor);df_(Eql);df_(Mtc);df_(Key);df_(Cat);df_(Cut);df_(Tak);df_(Drp);df_(Cst);df_(Fnd);df_(Atx);df_(Cal);df_(Ech);df_(nyi);df_(Rdc);df_(nyi);df_(Scn);df_(nyi);df_(com);df_(prj);df_(Otu);df_(In);df_(Find);df_(Hyp);df_(nyi);df_(nyi);df_(nyi);df_(Enc);df_(Dec);df_(nyi);df_(nyi);df_(Bin);df_(Mod);df_(Pow);df_(Lgn);df_(nyi);df_(nyi);df_(Rtp);
   dfi_=193; df_(tchr);df_(tnms);df_(tvrb);df_(tpct);df_(tvar);df_(tsym);
   dfi_=211; df_(Amd);df_(Dmd);

   // monads/dyads for each type
   //           f+0       f+1       f+2      f+3        f+4        f+5        f+6      f+7       f+8       f+9       f+10     f+11     f+12     f+13     f+14
   //           T_it      T_ft      nyi      T_Ct       T_It       T_Ft       nyi      T_ct      T_it      T_ft      nyi                                 nyi
   //           T_ct
   dfi_=220;df_(negi);df_(negf);df_(nyi);df_(negC); df_(negI); df_(negF); df_(nyi);
   dfi_=227;df_(absi);df_(absf);df_(nyi);df_(absC); df_(absI); df_(absF); df_(nyi);
   dfi_=234;df_(addi);df_(addf);df_(nyi);df_(addcC);df_(addiI);df_(addfF);df_(nyi);df_(addC);df_(addI);df_(addF);df_(nyi);
   dfi_=245;df_(subi);df_(subf);df_(nyi);df_(subcC);df_(subiI);df_(subfF);df_(nyi);df_(subC);df_(subI);df_(subF);df_(nyi);
   dfi_=256;df_(muli);df_(mulf);df_(nyi);df_(mulcC);df_(muliI);df_(mulfF);df_(nyi);df_(mulC);df_(mulI);df_(mulF);df_(nyi);
   dfi_=267;df_(divi);df_(divf);df_(nyi);df_(nyi);  df_(nyi);  df_(divfF);df_(nyi);df_(nyi); df_(nyi); df_(divF);df_(nyi);
   dfi_=278;df_(mini);df_(minf);df_(nyi);df_(mincC);df_(miniI);df_(minfF);df_(nyi);df_(minC);df_(minI);df_(minF);df_(nyi);
   dfi_=289;df_(maxi);df_(maxf);df_(nyi);df_(maxcC);df_(maxiI);df_(maxfF);df_(nyi);df_(maxC);df_(maxI);df_(maxF);df_(nyi);
   dfi_=300;df_(nyi); df_(sqrf);df_(nyi);df_(nyi);  df_(nyi);  df_(sqrF); df_(nyi);

   dfi_=308;df_(eqi); df_(eqf); df_(nyi);df_(eqcC); df_(eqiI); df_(eqfF); df_(nyi);df_(eqCc);df_(eqIi);df_(eqFf);df_(nyi);df_(eqC);df_(eqI);df_(eqF);df_(nyi);
   dfi_=323;df_(lti); df_(ltf); df_(nyi);df_(ltcC); df_(ltiI); df_(ltfF); df_(nyi);df_(ltCc);df_(ltIi);df_(ltFf);df_(nyi);df_(ltC);df_(ltI);df_(ltF);df_(nyi);
   dfi_=338;df_(gti); df_(gtf); df_(nyi);df_(gtcC); df_(gtiI); df_(gtfF); df_(nyi);df_(gtCc);df_(gtIi);df_(gtFf);df_(nyi);df_(gtC);df_(gtI);df_(gtF);df_(nyi);

   // grade up/down
   dfi_=353;df_(guC);df_(guC);df_(guI);df_(guI);df_(guF);df_(nyi);df_(guL);df_(gdC);df_(gdC);df_(gdI);df_(gdI);df_(gdF);df_(nyi);df_(gdL);

   // special reductions
   dfi_=367;df_(sum); df_(rd0);df_(prd); df_(rd0);df_(min);df_(max);
   dfi_=374;df_(sums);df_(rd0);df_(prds);df_(rd0);df_(rd0);

   // k init
   SP=POS_STACK;
   SetJ(POS_SRC,(J)mk(T_Ct,0));
   loc_=0ull;
   math_init();
   rand_=1592653589;
   SetJ(0,(J)mk(T_Lt,0)); // key
   SetJ(8,(J)mk(T_Lt,0)); // val
   sc(Ku(0ull));
   x=sc(Ku(0x78ull)); // 'x'
   y=sc(Ku(0x79ull)); // 'y'
   z=sc(Ku(0x7aull)); // 'z'
   xyz_=cat1(Cat(x,y),z);
   zfuncs();
}

#ifdef SPESH_NATIVE
// extend (register external function)
void KR(const C *name, void *fp, int arity) {
   size_t n=strlen(name);
   K s=mk(T_Ct, (I)n);
   memcpy(M_+(I)s, name, n);
   K r=l2(KCn((C *)&fp, 8), rx(s));
   I *m=(I*)(M_+(I)r);
   m[-3]=(I)arity;
   dx(Asn(sc(s),((K)(I)r) | (((K)T_xf)<<59ull)));
}

K Native(K x, K y){
   I n=nn(y);
   void **p=(void **)(M_+(int32_t)x);
   void *f=*p;
   rl(y); dx(y);
   K *m=(K*)(M_+(I)y);
   switch(n){
      case 0: return ((K(*)())f)();
      case 1: return ((K(*)(K))f)(m[0]);
      case 2: return ((K(*)(K,K))f)(m[0],m[1]);
      case 3: return ((K(*)(K,K,K))f)(m[0],m[1],m[2]);
      case 4: return ((K(*)(K,K,K,K))f)(m[0],m[1],m[2],m[3]);
      case 5: return ((K(*)(K,K,K,K,K))f)(m[0],m[1],m[2],m[3],m[4]);
      case 6: return ((K(*)(K,K,K,K,K,K))f)(m[0],m[1],m[2],m[3],m[4],m[5]);
      case 7: return ((K(*)(K,K,K,K,K,K,K))f)(m[0],m[1],m[2],m[3],m[4],m[5],m[6]);
      case 8: return ((K(*)(K,K,K,K,K,K,K,K))f)(m[0],m[1],m[2],m[3],m[4],m[5],m[6],m[7]);
      case 9: return ((K(*)(K,K,K,K,K,K,K,K,K))f)(m[0],m[1],m[2],m[3],m[4],m[5],m[6],m[7],m[8]);
   }
   return trap(E_Nyi);
}
#else //!SPESH_NATIVE
K Native(K x, K y){ return 0*(x+y); }
#endif //SPESH_NATIVE
