import data.fintype

namespace Fixedpoint

universes u
variables (A : Type u)
variables [finA : fintype A]
include finA

/- Boolean function representing set -/
def predicate := A -> bool 

/- Subset set relation -/
def rel_subset (fSet sSet : predicate A) : Prop :=
  ∀ (x : A), fSet x = tt  -> sSet x = tt

/- Subset equality -/
def eq_set (fSet sSet : predicate A) :=
  and  (rel_subset A fSet sSet) 
       (rel_subset A sSet fSet)

/- Subset relation is reflexive -/
lemma rel_subset_equal : 
  ∀ (p : predicate A), rel_subset A p p :=
begin
 intros _ _ Hp; 
 exact Hp 
end 

/- Subset relation is antisymmteric-/
lemma rel_subset_antisymmetric :
  ∀ (p q : predicate A),  rel_subset A p q ->
  rel_subset A q p -> eq_set A p q :=
  begin
  intros p q Hp Hq; 
  split; intros x Hx,
  apply Hp, exact Hx,
  apply Hq, exact Hx,
  end 

/- Subset relation is transitive-/
lemma subset_transitive :
  ∀ (p q r : predicate A), rel_subset A p q ->
  rel_subset A q r -> rel_subset A p r :=
  begin
  intros p q r Hp Hq x Hx;
  apply Hq; apply Hp; exact Hx,
  end 

/- subset relation is Partial order-/

lemma eq_subset_refl : 
  ∀ (p : predicate A), eq_set A p p :=
  begin
  intro _; split;
  intros _ Hp; exact Hp,
  end


 lemma eq_subset_symmetric :
  ∀ (p q : predicate A), eq_set A p q -> eq_set A q p :=
 begin 
  intros p q Hp,
  have Hpl : rel_subset A p q, from and.left Hp,
  have Hpr : rel_subset A q p, from and.right Hp,
  exact (and.intro Hpr Hpl)
 end 

def complement_set (p : predicate A) : predicate A :=
  λ (x : A), bnot (p x)


def empty_set : predicate A :=
 λ (x : A), ff


lemma empty_set_subset : 
  ∀ (p : predicate A), rel_subset A (empty_set A) p :=
  begin
   intros _ _ Hx, 
   cases Hx
  end 

/- Subset relation is decidable on finite types -/
lemma decidable_equality_rel_set : 
∀ (fSet sSet : predicate A), decidable (rel_subset A fSet sSet) :=
begin
 intros fSet sSet,
 apply fintype.decidable_forall_fintype
end 

/- Equality is decidable on finite set -/
lemma decidable_equality_set : 
∀ (fSet sSet : predicate A), decidable (eq_set A fSet sSet) :=
begin
 intros fSet sSet,
 have H₁ : decidable (rel_subset _ fSet sSet), 
    from (decidable_equality_rel_set _ fSet sSet),
 have H₂ : decidable (rel_subset _ sSet fSet), 
    from (decidable_equality_rel_set _ sSet fSet),
 apply (@and.decidable _ _ H₁ H₂),
end
  
lemma adding_new_element : 
∀ (fSet sSet : predicate A), rel_subset _ fSet sSet -> 
 ¬(∀ x : A, fSet x = sSet x) -> 
 ∃ y : A, fSet y = ff ∧ sSet y = tt :=
begin
 unfold rel_subset, 
 end 

    










         

  


end Fixedpoint