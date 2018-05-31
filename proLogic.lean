example (m n : ℕ) : m + n = n + m :=
by simp

theorem t1(p q: Prop):p → q → p:=
 assume hp:p,
 assume hq:q,
 show p, from hp 


--theorem t2(p q r: Prop)(H1:q → r)(H1:q → r):=

theorem and_swap(p q : Prop):p ∧ q ↔  q ∧ p:= 
begin
apply iff.intro,
intro H1,
exact and.intro(and.right H1)(and.left H1),
intro H2,
exact and.intro(and.right H2)(and.left H2),  
end
#check and_swap

theorem or_swap(p q : Prop):p ∨ q ↔  q ∨ p:= 
begin
apply iff.intro,
intro H1,
apply or.elim H1,

intro H2,
exact or.inr H2,

intro H3,
exact or.inl H3,

intro H4,
apply or.elim H4,

intro H2,
exact or.inr H2,

intro H3,
exact or.inl H3,

end
#check or_swap
