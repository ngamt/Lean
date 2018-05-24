
universe u
inductive BT(α : Type u)
|nil{}: BT
|leaf: α  → BT
|node: α → BT→ BT → BT 
def bt1:BT ℕ  := BT.node 1 (BT.leaf 2)(BT.leaf 3)
def bt2:BT ℕ  := BT.node 1 (BT.node 2 (BT.leaf 3)(BT.nil)) (BT.leaf 4) 

#eval bt1 
#eval bt2

open BT
def nVers {α: Type} : BT α → ℕ 
|nil:=0
|(leaf a) :=1
|(node a T1 T2):=1 + (nVers T1) + (nVers T2)

#eval nVers bt1
#eval nVers bt2

def isNil {α: Type} : BT α → bool
|nil:=tt
|(leaf a) :=ff
|(node a T1 T2):=ff
#eval isNil bt1

def nEdges {α: Type} : BT α → ℕ 
|nil:=0
|(leaf a) :=0
|(node a T1 T2):=if isNil T1 ∧ isNil T2 then 0 else if isNil T1 then (nEdges T2)+1 
else if isNil T2 then (nEdges T1) +1 else (nEdges T1)+(nEdges T2)+2
#eval nEdges bt1
#eval nEdges bt2

def inTree(v:ℕ): BT ℕ → bool
|nil:=ff
|(leaf a):=if v=a then tt else ff
|(node a T1 T2):=if a=v then tt else if inTree T1 then tt else inTree T2
#eval inTree 1 bt1

def maxTree: BT ℕ → ℕ 
|nil:=0
|(leaf a):=a
|(node a T1 T2):=let m1:= maxTree T1 in let m2:=maxTree T2 in if m1<=a ∧ m2<=a then 
a else if m1<=m2 then m2 else m1
#eval maxTree bt2
