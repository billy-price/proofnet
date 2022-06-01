import tactic

inductive foo : Type
| atom : ℕ → foo
| neg : foo → foo

open foo

lemma not_self_double_dual (A) : neg (neg A) ≠ A := sorry

inductive dual (A : foo) : foo → foo → Prop
| negpos : dual (neg A) A
| posneg : dual A (neg A)

theorem bar (A B) : dual A B (neg B) → A = B :=
begin
  intro d,
  have h := not_self_double_dual A,
  generalize_hyp e : B = B' at d,
end




  -- intro e,
  -- apply_fun foo.sizeof at e,
  -- refine ne_of_gt _ e,
  -- refine lt_trans _ _, exact (neg A).sizeof,
  -- rw [foo.sizeof, nat.add_comm], exact nat.lt_succ_self _ ,
  -- rw [foo.sizeof, foo.sizeof], apply add_lt_add_left,
  -- have : sizeof (neg A) = (neg A).sizeof, refl, rw this,
  -- rw [foo.sizeof, nat.add_comm], exact nat.lt_succ_self _ ,








