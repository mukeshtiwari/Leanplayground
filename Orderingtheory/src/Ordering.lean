
/- https://github.com/coq-community/corn/tree/master/order -/
namespace Ordering

universes u v

/- Preorder is reflexive and transitive -/
class preorder (A : Type u) (R : A -> A -> Prop) :=
(Hreflexive : ∀ x : A, R x x)
(Htransitive : ∀ x y z, R x y → R y z → R x z)

/- Equivalence is a preorder set with symmetry -/
class equivalence (A : Type u) (R : A -> A -> Prop) :=
(Hp : preorder A R)
(Hsymmetric : ∀ x y : A, R x y → R y x)

/- Partial order is -/
class partial_order (A : Type u) (R : A -> A -> Prop) :=
(Hp : preorder A R)
(Hantisymmetric : ∀ x y, R x y → R y x -> x = y)

/- Meet semilattic is poset with meet -/
class meet_semilattice (A : Type u) (R : A -> A -> Prop)  
(meet : A -> A -> A) :=
(Hp : partial_order A R) 
(H₁ : ∀ x y : A, R (meet x y) x)
(H₂ : ∀ x y : A, R (meet x y) y)
(H₃ : ∀ x y z : A, R z x -> R z y -> R z (meet x y))

lemma meet_idempotent : forall (A : Type u) (R : A -> A -> Prop)
  (x : A) (meet : A → A → A), 
  meet_semilattice A R meet → meet x x = x  :=
  begin
  intros A R x meet Hmeet, 
  apply Hmeet.Hp.Hantisymmetric,
  apply Hmeet.H₁, 
  apply Hmeet.H₃;
  apply Hmeet.Hp.Hp.Hreflexive
  end 


lemma meet_commutative : ∀  (A : Type u) (R : A -> A -> Prop)  
  (x y : A) (meet : A → A → A), 
  meet_semilattice A R meet →  meet x y = meet y x :=
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


lemma join_idempotent : forall (A : Type u) (R : A -> A -> Prop)
  (x : A) (join : A → A → A), 
  join_semilattice A R join → join x x = x  :=
  begin
  intros A R x join Hjoin, 
  apply Hjoin.Hp.Hantisymmetric,
  apply Hjoin.H₃;
  apply Hjoin.Hp.Hp.Hreflexive,
  apply Hjoin.H₁
  end 

/- Can I pull some category theoretic duality notation 
   about meet and join. This proof is same as meet_commutative -/
lemma join_commutative : ∀  (A : Type u) (R : A -> A -> Prop)  
  (x y : A) (join : A → A → A), 
  join_semilattice A R join →  join x y = join y x :=
  begin
  intros A R x y join Hjoin, 
  apply Hjoin.Hp.Hantisymmetric,
  /- How to combine top and below one in one go ? -/
  apply Hjoin.H₃, apply Hjoin.H₂,
  apply Hjoin.H₁,
  apply Hjoin.H₃, apply Hjoin.H₂,
  apply Hjoin.H₁,  
  end

lemma join_associative : ∀  (A : Type u) (R : A -> A -> Prop)  
  (x y z : A) (join : A → A → A), 
  meet_semilattice A R join ->  join x (join y z) = join (join x y) z :=
  begin
  /- Write a pen and paper proof first -/
   sorry
  end 

class lattice (A : Type u) (R : A -> A -> Prop)  
(meet : A -> A -> A) (join : A -> A -> A) :=
(Hmeet : meet_semilattice A R meet)
(Hjoin : join_semilattice A R join) 


class bounded_lattic (A : Type u) (R : A -> A -> Prop)  (Top : A) (Bot : A) 
(meet : A -> A -> A) (join : A -> A -> A) := 
(Hla : lattice A R meet join)
(Hb : ∀ x, R Bot x)
(Ht : ∀ x, R x Top)



def monotone_fun (A : Type u) (B : Type v) (f : A -> B) 
  (Ra : A -> A -> Prop) (Rb : B -> B -> Prop) :=
  partial_order A Ra -> partial_order B Rb -> 
  ∀ (x y : A), Ra x y -> Rb (f x) (f y)


def fixed_point (A : Type u) (f : A -> A) (x : A) := 
  f x = x


    



end Ordering


