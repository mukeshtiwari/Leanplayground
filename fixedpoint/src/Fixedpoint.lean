import data.fintype data.list

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
  
lemma finite_type_list_ex : 
∀ (fSet sSet : predicate A) (l : list A),
¬(∀ x : A, x ∈ l -> fSet x = sSet x) ->
∃ x : A, x ∈ l /\ fSet x ≠ sSet x :=
begin
  intros fSet sSet l H,  
  induction l, 
  have H₁ : false, 
    apply H, intros, 
    cases a,
  cases H₁, 

  have H₁ : fSet l_hd ≠ sSet l_hd ∨ 
            fSet l_hd = sSet l_hd, 
    destruct (fSet l_hd);
      destruct (sSet l_hd); intros,
    right, rw [a, a_1], 
    left, intro, rw [a, a_1] at a_2, 
    cases a_2, 
    left, intro, rw [a, a_1] at a_2, 
    cases a_2, 
    right, rw [a, a_1],
  destruct H₁; intros, 
  /- give l_hd as witness -/
  have H₂ : l_hd ∈ (list.cons l_hd l_tl),
    simp,  
  exact (exists.intro l_hd (and.intro H₂ h)),
  
  have H₁ : ¬ (∀ x : A, x ∈ l_tl → fSet x = sSet x),
  intro, apply H, intros, cases a_1, 
  rw a_1, assumption, 
  apply a, assumption, 
  let rw := l_ih H₁, 
  destruct rw, intros, 
  destruct h_1, intros, 
  have H₂ : w ∈ (list.cons l_hd l_tl), 
   simp, right, assumption, 
  exact (exists.intro w (and.intro H₂ right)),
end


lemma adding_new_element : 
∀ (fSet sSet : predicate A), rel_subset _ fSet sSet -> 
 ¬(∀ x : A, fSet x = sSet x) -> 
 ∃ y : A, fSet y = ff ∧ sSet y = tt :=
 begin 
 destruct (fintype.exists_univ_list A), 
 unfold rel_subset, 
 intros w Hl fSet sSet Hx Hnx,
 let rw := finite_type_list_ex A fSet sSet w,   
 have H₁ : ¬(∀ x : A, x ∈ w -> fSet x = sSet x),
  intro, apply Hnx, 
  intro, apply a, destruct Hl, intros, 
  apply right, 
 let an := rw H₁,
 destruct an, intros, 
 destruct h, intros, 
 destruct (fSet w_1);
   destruct (sSet w_1); intros, 
 rw [a, a_1] at right, 
 cases (right rfl),
 exact (exists.intro w_1 (and.intro a_1 a)),
 let hwt := Hx w_1 a_1, 
 rw hwt at a, cases a,
 rw [a, a_1] at right, 
 cases (right rfl),
 end 

    










         

  


end Fixedpoint
