import data.fintype data.nat.basic
 
namespace Elgamal

/- define a group on finite type -/
universe u
variables (A : Type u) (Hf : fintype A)
(gOp : A -> A -> A) (e : A) (inv : A -> A)

class group  :=
  (associativity : ∀ x y z : A, gOp x (gOp y z) = 
                                gOp (gOp x y) z)
  (left_identity : ∀ x : A, gOp e x = x)
  (right_identity : ∀ x : A, gOp x e = x)
  (left_inverse : ∀ x : A, gOp (inv x) x = e)
  (right_inverse : ∀ x : A, gOp x (inv x) = e)

def group_pow (x : A) : ℕ → A 
| 0 := e
| (n + 1) := gOp x (group_pow n)

lemma group_exp_identity :
 ∀ (n : ℕ), group_pow A gOp e e n = e :=
  begin
  intro n, induction n,
  
  

 
  end 


end Elgamal





