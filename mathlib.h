// License: CC0 (Public Domain)

#ifndef MATHLIB_H
#define MATHLIB_H

#define F64abs       fabs
#define F64sqrt      sqrt
#define F64floor     floor
#define F64min       fmin
#define F64max       fmax
#define F64copysign  copysign

static double   F64reinterpret_i64(uint64_t x){union{uint64_t i;double f;}u;u.i=x;return u.f;}
static uint64_t I64reinterpret_f64(double   x){union{uint64_t i;double f;}u;u.f=x;return u.i;}

static const double pi=3.141592653589793;
static const double maxfloat=1.7976931348623157e+308;

static double F64na = 0.;
static double F64inf = 0.;

static int32_t F64eq(double x, double y) {
    return F64abs(x-y)<2.2250738585072014e-308;
}

void math_init(void) {
    F64na=F64reinterpret_i64((uint64_t)0x7ff8000000000001ull);
    F64inf=F64reinterpret_i64((uint64_t)0x7ff0000000000000ull);
}

static double normalize(double x){
    if(F64abs(x)<2.2250738585072014e-308){
      return x*4.503599627370496e+15;
    }
    return x;
}

static double hypot_(double p, double q){
    double t;
    p=F64abs(p);
    q=F64abs(q);
    if(p<q){
      t=p; p=q; q=t;
    }
    if(F64eq(p,0.)){ return 0.; }
    q=q/p;
    return p*F64sqrt(1. + q*q);
}

static double ldexp_(double frac, int64_t exp){
    uint64_t x;
    double nf,m;
    if(F64eq(frac,0.) || frac>maxfloat || frac<-maxfloat || frac!=frac){
      return frac;
    }
    nf=normalize(frac);
    if(nf!=frac){
      exp=(exp-52ll);
      frac=nf;
    }
    x=(uint64_t)I64reinterpret_f64(frac);
    exp+=(((int64_t)(x>>52ull)&2047ll)-1023ll);
    if(exp<(int64_t)(-1075ll)){
      return F64copysign(0.,frac);
    }
    if(exp>(int64_t)1023ll){
      return frac<0.?-F64inf:F64inf;
    }
    m=1.;
    if(exp<(int64_t)(-1022ll)){
      exp+=53ll;
      m=1.1102230246251565e-16;
    }
    x=(x&~0x7ff0000000000000ull);
    x=(x|((uint64_t)(exp+1023ll)<<52ull));
    return m*F64reinterpret_i64((uint64_t)x);
}

static double expmulti(double hi, double lo, int64_t k){
    double r,t,c,y;
    r=hi-lo;
    t=r*r;
    c=r - t * (0.16666666666666666 + t * (-0.0027777777777015593 + t * (6.613756321437934e-05 + t * (-1.6533902205465252e-06 + t * 4.1381367970572385e-08))));
    y=1. - (lo-((r*c)/(2.-c)) - hi);
    return ldexp_(y,k);
}

static double exp_(double x){
    double hi,lo;
    int64_t k=0ll;
    if(x!=x){ return x; }
    if(x>709.782712893384){ return F64inf; }
    if(x<-745.1332191019411){ return 0.; }
    if(-3.725290298461914e-09<x && x<3.725290298461914e-09){
      return 1.+x;
    }
    k=(x<0.) ? (int64_t)(1.4426950408889634*x-0.5) : (int64_t)(1.4426950408889634*x+0.5);
    hi=x-((double)(k)*0.6931471803691238);
    lo=(double)(k)*1.9082149292705877e-10;
    return expmulti(hi,lo,k);
}

static int32_t frexp1(double f){
    if(F64eq(f,0.)){ return 0; }
    if(f<-maxfloat || f>maxfloat || f!=f){
      return 0;
    }
    return 1;
}

static double frexp2(double f){
    uint64_t x;
    f=normalize(f);
    x=I64reinterpret_f64(f);
    x=(x&~0x7ff0000000000000ull);
    x=(x|0x3fe0000000000000ull);
    return F64reinterpret_i64(x);
}

static int64_t frexp3(double f){
    uint64_t x;
    double nf;
    int64_t exp;
    exp=(int64_t)0ll;
    nf=normalize(f);
    if(nf!=f){
      exp=(int64_t)-52ll;
      f=nf;
    }
    x=I64reinterpret_f64(f);
    return (exp+(int64_t)((x>>52ull)&2047ull))-1022ll;
}

static double log_(double x){
    double f,k,s,s2,s4,t1,t2,R,hfsq;
    int64_t ki;
    if(x!=x || x>maxfloat){ return x; }
    if(x<0.){ return F64na; }
    if(F64eq(x,0.)){ return -F64inf; }
    f=x;
    ki=(int64_t)0ll;
    if(frexp1(x)){
      f=frexp2(x);
      ki=frexp3(x);
    }
    if(f<0.7071067811865476){
      f=f*2.;
      ki=ki-1ll;
    }
    f=f-1.;
    k=(double)ki;
    s=f/(2.+f);
    s2=s*s;
    s4=s2*s2;
    t1=s2 * (0.6666666666666735 + s4 * (0.2857142874366239 + s4 * (0.1818357216161805 + s4 * 0.14798198605116586)));
    t2=s4 * (0.3999999999940942 + s4 * (0.22222198432149784 + s4 * 0.15313837699209373));
    R=t1+t2;
    hfsq=0.5*f*f;
    return k * 0.6931471803691238 - ((hfsq - (s * (hfsq+R) + k * 1.9082149292705877e-10)) - f);
}

static double modabsfi(double f){
    uint64_t x,e;
    if(f<1.){ return 0.; }
    x=I64reinterpret_f64(f);
    e=((x>>52ull)&2047ull)-1023ull;
    if(e<52ull){
      x=(x&~(((uint64_t)(1ull)<<(52ull-e)) - (uint64_t)1ull));
    }
    return F64reinterpret_i64(x);
}

static double pow_(double x, double y){
    double yf,yi,a,x1;
    int64_t ae,xe;
    if(F64eq(y,0.) || F64eq(x,1.)){ return 1.; }
    if(F64eq(y,1.)){ return x; }
    if(x!=x || y!=y || y>maxfloat || y<-maxfloat){ return F64na; }
    if(F64eq(x,0.)){ return (y<0.) ? F64inf : 0.; }
    if(F64eq(y,0.5)){ return F64sqrt(x); }
    if(F64eq(y,-0.5)){ return 1./F64sqrt(x); }
    yf=F64abs(y);
    yi=modabsfi(yf);
    yf=(yf-yi);
    if(!F64eq(yf,0.) && x<0.){return F64na;}
    if(yi>=9.223372036854776e+18){
      if(F64eq(x,-1.)){
        return 1.;
      } else {
        return ((F64abs(x)<1.)==(y>0.)) ? 0. : F64inf;
      }
    }
    a=1.;
    ae=(int64_t)(0ll);
    if(!F64eq(yf,0.)){
      if(yf>0.5){
        yf=yf-1.;
        yi+=1.;
      }
      a=exp_(yf*log_(x));
    }
    x1=x;
    xe=(int64_t)0ll;
    if(frexp1(x)){
      x1=frexp2(x);
      xe=frexp3(x);
    }
    for(int64_t i=(int64_t)yi; i!=0ll; i=(i>>(int64_t)1ll)){
      if(xe<-4096ll || 4096ll<xe){
        ae+=xe;
        break;
      }
      if((i&1ll)==1ll){
         a=(a*x1);
         ae+=xe;
      }
      x1=x1*x1;
      xe=(xe<<(int64_t)1ll);
      if(x1<0.5){
        x1+=x1;
        xe=(xe-1ll);
      }
    }
    if(y<0.){
      a=(1./a);
      ae=-ae;
    }
    return ldexp_(a,ae);
}

static int32_t iipow(int32_t x, int32_t y){
    int32_t r = 1;
    for(;;){
      if((y&1)==1){ r=(r*x); }
      y=(y>>1);
      if(!y){ break; }
      x=x*x;
    } return r;
}

static double cosin_(double x, int32_t csonly){
    int32_t ss,cs;
    double c,s,y,z,zz;
    int64_t j;
    c=0.; s=0.;
    ss=0; cs=0;
    if(x<0.){
      x=-x; ss=1;
    }
    j=(int64_t)(x*1.2732395447351628);
    y=(double)j;
    if((j&1ll)==1ll){
      j+=1ll; y+=1.;
    }
    j=(j&7ll);
    z=((x - y*0.7853981256484985) - y*3.774894707930798e-08) - y*2.6951514290790595e-15;
    if(j>3ll){
      j=j-4ll; ss=1-ss; cs=1-cs;
    }
    if(j>1ll){ cs=1-cs; }
    zz=z*z;
    c= (1. - 0.5*zz) + (zz*zz) * (((((-1.1358536521387682e-11 * zz + 2.087570084197473e-09) * zz + -2.755731417929674e-07) * zz + 2.4801587288851704e-05) * zz + -0.0013888888888873056) * zz + 0.041666666666666595);
    s= z + (z*zz) * (((((1.5896230157654656e-10 * zz + -2.5050747762857807e-08) * zz + 2.7557313621385722e-06) * zz + -0.0001984126982958954)*zz+0.008333333333322118) * zz + -0.1666666666666663);
    if(j==1ll || j==2ll){
      x=c; c=s; s=x;
    }
    if(cs){ c=-c; }
    if(ss){ s=-s; }
    if(csonly==1){ return s; }
    return c;
}

#endif // MATHLIB_H
