
/- https://github.com/coq-community/corn/tree/master/order -/
namespace Ordering

universes u v

class preorder (A : Type u) (R : A -> A -> Prop) :=
(Hreflexive : ∀ x : A, R x x)
(Htransitive : ∀ x y z, R x y → R y z → R x z)

class equivalence_rel (A : Type u) (R : A -> A -> Prop) :=
(Hp : preorder A R)
(Hsymmetric : ∀ x y : A, R x y → R y x)

class partial_order (A : Type u) (R : A -> A -> Prop) :=
(Hp : preorder A R)
(Hantisymmetric : ∀ x y, R x y → R y x -> x = y)

class meet_semilattice (A : Type u) (R : A -> A -> Prop)  
(meet : A -> A -> A) :=
(Hp : partial_order A R) 
(H₁ : ∀ x y : A, R (meet x y) x)
(H₂ : ∀ x y : A, R (meet x y) y)
(H₃ : ∀ x y z : A, R z x -> R z y -> R z (meet x y))

lemma meet_commutative : ∀  (A : Type u) (R : A -> A -> Prop)  
  (x y : A) (meet : A → A → A), 
  meet_semilattice A R meet ->  meet x y = meet y x :=
  begin
  intros A R x y meet Hmeet, 
  apply Hmeet.Hp.Hantisymmetric,
  /- How to combine top and below one in one go ? -/
  apply Hmeet.H₃, apply Hmeet.H₂,
  apply Hmeet.H₁,
  apply Hmeet.H₃, apply Hmeet.H₂,
  apply Hmeet.H₁,  
  end

lemma meet_associative : ∀  (A : Type u) (R : A -> A -> Prop)  
  (x y z : A) (meet : A → A → A), 
  meet_semilattice A R meet ->  meet x (meet y z) = meet (meet x y) z :=
  begin
   sorry
  end 

class join_semilattice (A : Type u) (R : A -> A -> Prop)
(join : A -> A -> A) :=
(Hp : partial_order A R)
(H₁ : ∀ x y : A, R x (join x y))
(H₂ : ∀ x y : A, R y (join x y))
(H₃ : ∀ x y z : A, R x z -> R y z -> R (join x y) z)

#check @join_semilattice

class lattice (A : Type u) (R : A -> A -> Prop)  
(meet : A -> A -> A) (join : A -> A -> A) :=
(Hmeet : meet_semilattice A R meet)
(Hjoin : join_semilattice A R join) 


class bounded_lattic (A : Type u) (R : A -> A -> Prop)  (top : A) (bot : A) 
(meet : A -> A -> A) (join : A -> A -> A) := 
(Hla : lattice A R meet join)
(Hb : ∀ x, R bot x)
(Ht : ∀ x, R top x)


def monotone_fun (A : Type u) (B : Type v) (f : A -> B) 
  (Ra : A -> A -> Prop) (Rb : B -> B -> Prop) :=
  partial_order A Ra -> partial_order B Rb -> 
  ∀ (x y : A), Ra x y -> Rb (f x) (f y)


def fixed_point (A : Type u) (f : A -> A) (x : A) := 
  f x = x


    



end Ordering


