// Minimal Spesh Terminal
// License: CC0 (Public Domain)
#define SPESH_NATIVE
#define SPESH_IO_VERBS
#define SPESH_IO_SYS
#include "../spesh.h"
#define Exit exit
#include<setjmp.h>

static int    args_;
static char **argv_;
static jmp_buf jb_;
int err=0;

void panic(I) { err=1; longjmp(jb_,1); }

static I Arg(I i, I r){
    if(i>=args_) return 0;
    if(r ==   0) return (I)strlen(argv_[i]);
    memcpy(M_+r,argv_[i],strlen(argv_[i]));
    return 0;
}

static K getargv(void){
    K r,s;
    I n=args_;
    r=mk(T_Lt,n);
    for(I i=0, rp=(I)r; i<n; i++, rp+=8){
      s=mk(T_Ct,Arg(i,0));
      Arg(i,(I)s);
      SetJ(rp,(J)s);
    } return r;
}

static void test(K x);
static void dofile(K x, K c){
    K kk=KC(".k"); K tt=KC(".t");
    K xe=ntake(-2,rx(x)); // file extension (hopefully)
    if(match(xe,kk)){ ops_=0; dx(val(c)); } // file .k (execute)
    else if(match(xe,tt)){ test(c); } // file .t (test)
    else { dx(Asn(sc(rx(x)),c)); } // file (assign file:bytes..)
    dx(xe); dx(x); dx(tt); dx(kk);
}

static K Lst(K x){
    /*
    `"pad.":{x@\\!|/#'x}
    `"lxy.":{ /k
    kt:{[x;y;k;T]x:$[`T~@x;T[x;k];`pad("";"-"),$x];(x,'"|"),'T[y;k]}
    d:{[x;k;kt;T]r:!x;x:.x;$[`T~@x;kt[r;x;k;T];,'[,'[`pad(k'r);"|"];k'x]]}
    T:{[x;k]$[`L?@'.x;,k x;(,*x),(,(#*x)#"-"),1_x:" "/'+`pad@'$(!x),'.x]}
    t:@y;
    k:`kxy@*x;h:*|x
    dd:("";,"..")h<#y:$[(@y)?`L`D`T;y;y~*y;y;[t:`L;,y]]
    y:$[y~*y;y;(h&#y)#y]
    $[`D~t;d[y;k;kt;T];`T~t;T[y;k];y~*y;,k y;k'y],dd}
    `"l.":`lxy 70 20
    */
    // Should return T_Lt of T_Ct (list of strings)
    return Enl(Kst(x));
}

void dw(K x){
    write(rx(x)); dx(x);
}

void repl(K x){
    I n=nn(x),xp=(I)x,s=0,c;
    if(n>0){
      s=GetC(xp);
      if(s=='\\' && n>1){
        c=GetC(1+xp);
        if(c=='\\'){
          Exit(0);
        } else if(c=='m'){ // mem usage
          dx(x); dx(Out(Ki((1<<memorycount_)/1024)));
        } else if(c=='h'){ // refcard help
          dx(x);
          dw(KC("+ flp add       '  ech  bin                c char     \"x\"   \"ab\"\n"));
          dw(KC("- neg sub       /  rdc  mod   f n/ ndo     i int      2     1 2\n"));
          dw(KC("* fst mul       \\  scn  div   x//y dec     s symbol   `a    ``c`d\n"));
          dw(KC("% sqr div       ': ecp  in    y\\\\x enc     f float    2.    1. 2.\n"));
          dw(KC("! til key       /: ecr  split   f/:fix\n"));
          dw(KC("& wer min       \\: ecl  join    f\\:fix     L list     (1;2 3)\n"));
          dw(KC("| rev max       while[c;a;b;..]            D dict     `a`b!1 2\n"));
          dw(KC("< asc les       $[a;b;...]      cond       T table    +`a`b!..\n"));
          dw(KC("> dsc mor       @[x;i;+;y]      amend      v verb     +\n"));
          dw(KC("= grp eql       .[x;i;+;y]      dmend      c comp     1+/*%\n"));
          dw(KC("~ not mtc       {a+b}.d         env        d derived  +/\n"));
          dw(KC(", enl cat       k?t             group      l lambda   {x+y}\n"));
          dw(KC("^ srt cut       k!t             key        x native   c-extension\n"));
          dw(KC("# cnt tak       t,d t,t t,'t(h) join\n"));
          dw(KC("_ flr drp       t{a>5}          where     exec: t~`v: push\n"));
          dw(KC("$ str cst       c:<`file(read)             v:  0..63   monadic\n"));
          dw(KC("? unq fnd       `file<c(write)                64..127  dyadic\n"));
          dw(KC("@ typ atx       `@i(verb) (+)~`2             128       pop + dyadic\n"));
          dw(KC(". val cal       .(1;2;`64+(+))  exec         129..255  tetradic\n"));
          dw(KC("                                             256       drop\n"));
          dw(KC("abs sin cos exp log any find             320/384   jmp, jmp-ifz\n"));
          dw(KC("                                             448..     quoted verb\n"));
          dw(KC("rand: ?n(uniform) n?n(with) -n?n(w/o) n?L\n"));
        }
        return;
      }
    }
    ops_=0; x=val(x);
    if(x==0ull){ return; }
    if(s==' '){ // skip formatting with Lst
      dx(Out(x));
    } else {
      write(cat1(join(Kc('\n'),Lst(x)),Kc('\n')));
    }
}

static void doargs(void){
    K a=ndrop(1,getargv()),x;
    I an=nn(a);
    K ee=KC("-e");
    for(I i=0; i<an; i++, a+=8ull){
      x=x0(a);
      if(match(x,ee)){ // -e (exit)
        if(i<an-1){
          dx(x); dx(ee);
          if(!setjmp(jb_)){ repl(x1(a)); }
        }
        Exit(err);
      }
      if(!setjmp(jb_)){ dofile(x,readfile(rx(x))); }
    }
    dx(ee);
}

static void testi(K l, I i){
    K x,y;
    x=split(Ku(0x2f20ull),ati(split(Kc('\n'),l),i)); // " /"
    if(nn(x)!=2){ trap(E_Length); }
    y=x1(x); x=r0(x);
    dx(Out(ucat(ucat(rx(x),Ku(0x2f20ull)),rx(y))));
    ops_=0; x=Kst(val(x));
    if(!match(x,y)){
      x=Out(x); trap(E_Err);
    }
    dx(x); dx(y);
}

static void test(K x){
    if(tp(x)!=T_Ct){ trap(E_Type); }
    K l=ndrop(-1,split(Kc('\n'),rx(x)));
    I n=nn(l);
    dx(l);
    for(I i=0;i<n;i++) testi(rx(x),i);
    dx(x);
}

K hello(K x){
    printf("Hello %i\n", (I)x);
    return x;
}
K nadd(K x, K y){
    return Neg(Add(x, y));
}

int main(int args, char **argv){
    K x;
    args_=(I)args; argv_=argv;
    kinit();
    KR("hello", (void*)hello, 1);
    KR("nadd", (void*)nadd, 2);
    doargs();
    write(KC("spesh/k\n"));
    for(;;){ // The repl loop
      write(Ku(32ull)); // " "
      x=read(); // stdin -> string
      if(!nn(x)){ write(Ku(0x000a)); break; } //"\n"
      if(!setjmp(jb_)){ repl(x); }
    }
    return 0;
}
