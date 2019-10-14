import data.fintype data.nat.basic
       data.zmod.basic algebra.group_power


namespace Zeroknowledgeproof
variables (p : ℕ) (q : ℕ) (r : ℕ+)
  (Hp : nat.prime p)
  (Hq : nat.prime q)
  (Hdiv : p = q * r + 1)
  (g : zmodp p Hp) /- g is a generator -/
  (Hg : g^q = 1)   /- of order q -/
  (w : zmodp q Hq) /- private key-/
  (h : zmodp p Hp)
  (Hh : h = g^w.val)

/- 
A Schnorr group is a large prime-order subgroup of ℤ∗𝑝, 
the multiplicative group of integers modulo 𝑝. 
To generate such a group, we find 𝑝=𝑞𝑟+1 such that 𝑝 and 𝑞
are prime.Then, we choose any ℎ
in the range 1<ℎ<𝑝 such that ℎ^r ≠ 1 (mod𝑝)
The value 𝑔=ℎ^𝑟(mod𝑝) is a generator of a subgroup ℤ∗𝑝 of order 𝑞.
By Fermat's little theorem
g^q = h^(rq) = h^(p-1) = 1 (mod p)

-/

def elgamal_enc (m : zmodp p Hp) (r : zmodp q Hq) :=
  (g^r.val, g^m.val * h^r.val)

def elgamal_dec (c : zmodp p Hp × zmodp p Hp) :=
     c.2 * (c.1^w.val)⁻¹ 
    
def multiply_cipher (c₁ c₂ : zmodp p Hp × zmodp p Hp) :=
  (c₁.1 * c₂.1, c₁.2 * c₂.2)


#check elgamal_enc p q Hp Hq g h 
#check elgamal_dec p q Hp Hq w 
#check multiply_cipher p Hp

lemma prime5: nat.prime 5 := 
begin 
 unfold nat.prime,
 split, sorry, 
 intros m Hm, sorry 
end 
/- It's pretty fase -/
#eval (13^1990 : zmodp 5 prime5)

include Hh
lemma elgama_enc_dec_identity :  
 ∀ m r, elgamal_dec p q Hp Hq w (elgamal_enc p q Hp Hq g h m r) 
        = g^m.val :=
begin
 intros m r, 
 unfold elgamal_enc elgamal_dec,
 simp, rw Hh, sorry 
end 
         
end Zeroknowledgeproof

namespace Interactive 

variables (p : ℕ) (Hp : nat.prime p)
          (g : zmodp p Hp)

/- 
universes u v
inductive communication : zmodp p Hp -> Type u
| commitment : ∀ k, communication k
| challenge : ∀ k, communication k
| response : ∀ k, communication k

open communication
/- Both parties are honest. zero knowledge proof -/
inductive zeroknowledge : ∀ (t : zmodp p Hp), communication p Hp t → Type u
| first_step : ∀ (r k : zmodp p Hp), k = g^r.val → zeroknowledge k (commitment k)
| second_step : ∀ (k c : zmodp p Hp), zeroknowledge k (commitment k) → 
    zeroknowledge c (challenge c)
| final_step : ∀ (s k c a : zmodp p Hp), s = k + c * a → 
          zeroknowledge c (challenge c) → zeroknowledge s (response s)
    
-/
/- I claim that this always checks out -/

universes u v
inductive communication : Type u
| commitment (k : zmodp p Hp) : communication
| challenge (k c : zmodp p Hp) : communication
| response (k c s : zmodp p Hp) : communication

/- /- zero knowledge proof of zkp {x | g^x = h} -/  -/
open communication
inductive zeroknowledge (x h : zmodp p Hp) (Hf : h = g^x.val) : 
    communication p Hp → Type u
| first_step (r k : zmodp p Hp) : k = g^r.val → zeroknowledge (commitment k)
| second_step (k c : zmodp p Hp) : zeroknowledge (commitment k) → 
    zeroknowledge (challenge k c)
| final_step (r k c s : zmodp p Hp) : s = r + c * x →
      /- How to connect r and k ? k = g^r.val or this can be 
      inferred from zeroknowledge (challenge k c). What if 
      prover try to cheat -/
          zeroknowledge (challenge k c) → zeroknowledge (response k c s)

axiom unique_element_in_zmodp : ∀ (k : zmodp p Hp), ∃ r : zmodp p Hp, k = g^r.val

axiom discrete_log : ∀ (k r₁ r₂ : zmodp p Hp), k = g^r₁.val -> k = g^r₂.val -> 
           r₁ = r₂  

open zeroknowledge
#check zeroknowledge
lemma first_constructor :  ∀ (k x h : zmodp p Hp) (Hf : h = g^x.val), 
  zeroknowledge p Hp g x h Hf (commitment k) :=
  begin 
    intros, have h := unique_element_in_zmodp p Hp g k, 
    sorry,
  end

 
lemma proof_of_correctness : ∀ (x h : zmodp p Hp) (Hf : h = g^x.val) 
    (k c s : zmodp p Hp), 
    zeroknowledge p Hp g x h Hf (response k c s) → 
    g^s.val = k * h^c.val :=
    begin 
    intros x h Hf k c s Hzkp, 
    destruct Hzkp, 
    {intros r k Ha Hr, injection Hr},
    {intros k c a Hr, injection Hr},
    intros r k c s Hs Ha Hr Hzero, clear Hr, 
    destruct Ha, 
    intros _ _ _ Hr₁, injection Hr₁, 
    intros k₁ c₁ Hc Hr₁ Ha₁, injection Hr₁, 
    destruct Hc, intros, 
    
    end 

lemma proof_of_knowlege : 

namespace Elgamal

/- define a group on finite type -/
universe u
variables (A : Type u) (Hf : fintype A)
(gop : A -> A -> A) (e : A) (inv : A -> A)

class group  :=
  (associativity : ∀ x y z : A, gop x (gop y z) = 
                                gop (gop x y) z)
  (left_identity : ∀ x : A, gop e x = x)
  (right_identity : ∀ x : A, gop x e = x)
  (left_inverse : ∀ x : A, gop (inv x) x = e)
  (right_inverse : ∀ x : A, gop x (inv x) = e)
 

def group_pow (x : A) : ℕ → A 
| 0 := e
| (n + 1) := gop x (group_pow n)

variable (G : group A gop e inv)
include G 

lemma group_exp_identity :
 ∀ (n : ℕ), group_pow A gop e e n = e :=
  begin
  intro n, induction n,
  /- simplification would do the job -/
  /- simplify it and rewrite in Ih, follwed right_identity -/
  {simp [group_pow]},
  {dsimp [group_pow], 
   rewrite n_ih, apply (group.left_identity gop e inv e)}
  end

lemma group_exp_plus : ∀ (n m : ℕ) (x : A), 
  group_pow A gop e x (n + m) = 
  gop (group_pow A gop e x n) (group_pow A gop e x m) := 
  begin 
  intros n, 
  induction n, 
  {intros m x, simp [group_pow],
   rewrite
   group.left_identity gop e inv (group_pow A gOp e x m)},
  {intros m x,
   simp [group_pow],
   rewrite nat.add_succ,
   simp [group_pow], rewrite n_ih,
   rewrite <- (group.associativity gOp e inv x)}
  end

  lemma group_exp_mult : ∀ (n m : ℕ) (x : A), 
  group_pow A gop e x (n * m) = 
  group_pow A gop e (group_pow A gop e x n) m := 
  begin 
   intros n, induction n,
   sorry,
   sorry
  end

class abelian_group := 
  (commutative : ∀ x y, gop x y = gop y x)

  #check (abelian_group A gop e inv G)

class cyclic_group (g : A) (order : ℕ+) 

end Elgamal





