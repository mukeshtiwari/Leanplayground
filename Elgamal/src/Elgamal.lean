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

namespace Interactivezkp

variables (p : ℕ) (Hp : nat.prime p)
          (g : zmodp p Hp)


universes u
inductive communication : Type u
| commitment (k : zmodp p Hp) : communication
| challenge (k : zmodp p Hp) : communication
| response (k s : zmodp p Hp) : communication

/- zero knowledge proof of zkp {x | g^x = h} 
   r is prover's randomness, c is challenger's randomness 
   Can this be abstracted for some R : A → B → bool -/
open communication
inductive zkp_transcript (x h : zmodp p Hp) (Hf : h = g^x.val)  
    (r c : zmodp p Hp) :  communication p Hp → Type u
| commitment_step (k : zmodp p Hp) : k = g^r.val → zkp_transcript (commitment k)
| challenge_step (k : zmodp p Hp) : zkp_transcript (commitment k) → 
    zkp_transcript (challenge k)
| response_step (k s : zmodp p Hp) : s = r + c * x →
          zkp_transcript (challenge k) → zkp_transcript (response k s)
/- end of zero knowledge proof transcript -/

open zkp_transcript
/- I don't care how the transcript is constructed. If it checks out according 
   to defined rule then I will accept it. -/
def accept_transcript  (k r c s x h : zmodp p Hp) (Hf : h = g^x.val)
      (Hzkp : zkp_transcript p Hp g x h Hf r c (response k s)) :=
      g^s.val =  k * h^c.val 

/- A transcript is not valid if it does not check out -/
def reject_transcript (k r c s x h : zmodp p Hp) (Hf : h = g^x.val)
      (Hzkp : zkp_transcript p Hp g x h Hf r c (response k s)) :=
      g^s.val ≠  k * h^c.val 

 /- for any given x h and proof Hf, randomness r c, I can always construct 
    a valid certificate. I will prove this formally that this 
    function always constructs a valid certificate which checks out  -/
 def construct_a_certificate (r c x h : zmodp p Hp) (Hf : h = g^x.val) :
        zkp_transcript p Hp g x h Hf r c (response (g^r.val) (r + c * x)) := 
    response_step (g^r.val) (r + c * x) rfl (challenge_step (g^r.val) 
      (commitment_step _ _ (g^r.val) rfl))

/- certificate checking is decidable-/

 /- Proof that the construct_a_certificate function always constructs 
    a valid certificate. Each valid certificate always checks out : Completeness -/
lemma proof_of_correctness :
    ∀ (r c x h : zmodp p Hp) (Hf : h = g^x.val) 
    (cert = construct_a_certificate p Hp g r c x h Hf), 
    accept_transcript p Hp g _ _ _ _ _ _ _ cert := 
    begin 
      intros, 
      unfold accept_transcript, 
      /- some basic math would solve it, but I don't know 
         the tactics yet.-/
         sorry 
    end 

 /- If you give me two valid ceritificate then I can extract a witness x : Soundenss  -/
lemma extract_witness : 
  ∀ (r₁ c₁ r₂ c₂ x h : zmodp p Hp) (Hf : h = g^x.val)
  (cert₁ = construct_a_certificate p Hp g r₁ c₁ x h Hf)
  (cert₂ = construct_a_certificate p Hp g r₂ c₂ x h Hf), 
  accept_transcript p Hp g _ _ _ _ _ _ _ cert₁ →
  accept_transcript p Hp g _ _ _ _ _ _ _ cert₂ →  true := 
  begin
    intros, sorry
  end 

 /- Zero knowledge Proof -/


end Interactivezkp



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





