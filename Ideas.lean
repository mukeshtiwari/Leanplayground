import Init.WF
import Init.Data.Nat



theorem nat_lt : ∀ n : Nat, 
  Acc (fun (x y : Nat) => x < y) n := by 
  intros n 
  induction n with 
  | zero =>
    focus
      apply Acc.intro
      intros y Hy
      cases Hy
  | succ n ih => 
    focus 
      apply Acc.intro
      intros y Hy 
      apply Acc.intro 
      intros z Hz 
      cases ih with
      | _ _ R => 
        apply R  
        have Ht := Nat.le_of_lt_succ Hy 
        have Hw := Nat.lt_of_lt_of_le Hz Ht 
        exact Hw 

class One (α : Type u) where
  one : α

class Op (α : Type u) where
  op : α → α → α

class Associative (α : Type u) extends (One α), (Op α) where 
  op_associative : ∀ (x y z : α), op x (op y z) = op (op x y) z 

class LeftOne (α : Type u) extends (One α), (Op α) where 
  left_one : ∀ x : α, op one x = x 

class RightOne (α : Type u) extends (One α), (Op α) where 
  right_one : ∀ x : α, op x one = x 

class Monoid (α : Type u) extends 
  (One α), (Op α), (Associative α), 
  (LeftOne α), (RightOne α)
  

class Inv (α : Type u) where 
   inv : α → α 

class LeftInv (α : Type u) extends (Inv α), (Op α) where 
  left_inv : forall x : α, op (inv x) x = one

class RightInv (α : Type u) extends (Inv α), (Op α) where 
    right_inv : forall x : α, op x (inv x) = one

class Group (α : Type u) extends (Monoid α), (Inv α), 
  (LeftInv α), (RightInv α)


theorem monoid_cancel_left
  {α : Type u} 
  [H : Monoid α] 
  (z iz x y : α) : 
  H.op iz z = H.one →
  (H.op z x = H.op z y ↔ x = y) := by 
  intro ha
  apply Iff.intro
  focus
    intro hb 
    have Hcut : (H.op iz  (H.op z x))  = (H.op iz (H.op z  y)) := by 
      rewrite [hb]; exact rfl 
    rewrite [H.op_associative, ha, H.left_one] at Hcut
    rewrite [H.op_associative, ha, H.left_one] at Hcut
    exact Hcut
  focus 
    intro hb 
    rewrite [hb]
    exact rfl 



  

  







  
  
  


