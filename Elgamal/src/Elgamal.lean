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

variable Hg : group A gOp e inv
include Hg 

lemma group_exp_identity :
 ∀ (n : ℕ), group_pow A gOp e e n = e :=
  begin
  intro n, induction n,
  /- simplification would do the job -/
  /- simplify it and rewrite in Ih, follwed right_identity -/
  {simp [group_pow]},
  {dsimp [group_pow], 
   rewrite n_ih, apply (group.left_identity gOp e inv e)}
  end

lemma group_exp_plus : ∀ (n m : ℕ) (x : A), 
  group_pow A gOp e x (n + m) = 
  gOp (group_pow A gOp e x n) (group_pow A gOp e x m) := 
  begin 
  intros n, 
  induction n, 
  {intros m x, simp [group_pow],
   rewrite
   group.left_identity gOp e inv (group_pow A gOp e x m)},
  {intros m x,
   simp [group_pow],
   rewrite nat.add_succ,
   simp [group_pow], rewrite n_ih,
   rewrite <- (group.associativity gOp e inv x)}
  end

  
              


end Elgamal





