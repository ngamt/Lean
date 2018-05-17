-- Live javascript version of Lean

#check (λ x:ℕ , x+1) 5

variables  α β: Type
variables p:α ×  β
variables p1 p2 p3 :α

-- variables (a1 a2: α) (b:β)(n: N)

#eval 2^64 
#eval 3-2*4+9

variable f: α-> β

def add23(x y: ℕ ): ℕ :=x+y+3
#check add23

--inductive nat: Type:=
--zero: nat 
--succ: nat → nat 

def fib:ℕ → ℕ
|0:=1
|1:=1
|(n+2):=fib(n+1) +fib(n)
#eval fib 5


def hm(x: ℕ):ℕ  → ℕ 
|0:=1
|1:=x
|(n+1):=(hm n) * x
#eval hm 2 10 

open nat
def hm2 : ℕ → ℕ  → ℕ 
|x 0 :=1
|x 1 := x
|x (succ n):= (hm2 x  n)*x
#eval hm2 2 10 

def sum1: (ℕ →  ℕ)→ ℕ  → ℕ 
|f 0 := f 0
|f (n+1):=sum1 f(n) + f(n+1) 
#eval sum1(λ x, x) 10

def sum2: (ℕ → ℕ)  →  ℕ → ℕ  → ℕ 
|f n m :=sum1 (λ x, f(x+ m)) (n-m)
#eval sum2(λ x, x) 1 10

def sum3 (f: ℕ → ℕ) (m n: ℕ ) 
:=sum1 (λ x, f(x+ m)) (n-m)
#eval sum2(λ x, x) 1 10

def s:=[1,2,3,4]
def t:=[5,7,8,9]
#eval s.length 

def Suml:list ℕ  →  ℕ 
|[]:=0
|(a::l):= if a > 6 then a + Suml l else Suml l  
#eval Suml t

def Sumlc (p:ℕ → bool): list ℕ  →  ℕ 
|[]:=0
|(a::l):= if p a then a + Sumlc l else Sumlc l  
#eval s

def is_even: ℕ → bool
|0:=tt
|1:=ff
|(n+2):=is_even n
#eval Sumlc is_even s

def divisor(n:ℕ): ℕ → bool 
|0:=ff
|1:=tt
|(succ m) :=if (n % succ m = 0) then tt else divisor m 
#eval divisor 13 12

