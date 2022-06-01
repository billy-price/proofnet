import mll

instance : has_zero Form := ⟨Form.atom 0⟩
instance : has_one Form := ⟨Form.atom 1⟩

def Form.bad_add (A B : Form) : Form :=
begin
  induction A; induction B,
  exact Form.atom (A+B),
  repeat {exact Form.atom 0},
end

instance : has_add Form := ⟨Form.bad_add⟩
instance : inhabited Form := ⟨0⟩


--   inductive cycle_trip (ps : proof_structure) (S : switching) : Form_occ × dir → ℕ → Prop
--   | cycle_trip (Ai d) (n : ℕ) : trip ps S n.succ (Ai,d) (Ai,d) → cycle_trip (Ai,d) n

--   inductive cycle_equiv {ps S X} {n : ℕ} (t : trip ps S n.succ X X) (Y m k) : trip ps S (m + k) Y Y → Prop
--   | cycle (tYX : trip ps S m Y X) (tXY : trip ps S k X Y) : cycle_equiv (trip.concat tYX tXY)

--   def longtrip (ps : proof_structure) (S : switching) := 
--     ∀ Γ₁ Γ₂, cycle_trip ps S Γ₁ → cycle_trip ps S Γ₂ → cycle_equiv Γ₁ Γ₂

--   theorem list_trip_unique_cons (ps : proof_structure) (S : switching) (t : list (Form_occ × dir)) (nnil : t ≠ []) (Ai Bi : Form_occ) (d₁ d₂ : dir) :
--     list_trip ps S ((Ai,d₁)::t) → list_trip ps S ((Bi,d₂)::t) → (Ai,d₁) = (Bi,d₂) :=
--   begin
--     intros tA tB,
--     rcases t with _ | ⟨⟨Ci,d₃⟩,t⟩, contradiction,
--     rcases tA with _ | _ | ⟨_,_,_,_,_,Δ,hΔ,sA,tC⟩,
--     rcases tB with _ | _ | ⟨_,_,_,_,_,Δ',hΔ',sB,tC⟩,
--     have : Δ' = Δ, symmetry, apply link_unique_of_steps_next hΔ hΔ' sA sB, cases this,
--     cases sA,
--     case steps.ax : { cases sB, simp, apply dual_unique_prev; assumption },
--     case steps.cut : { cases sB, simp, apply dual_unique_prev; assumption },
--     case steps.con : { cases sB, refl},
--     case steps.tensor : A B ai bi ci st₁ {
--       rcases (ps.valid _ hΔ) with _ | _ | _ | ⟨_,_,_,_,_,nAB⟩,
--       cases sB, cases S (Link.tensor ai bi ci A B); apply steps_tensor_unique_prev _ _ _ st₁,
--       assumption, cases (ps.valid _ hΔ), assumption,
--         intro e, injection e with e1, apply not_self_sub_right_tensor e1,
--         intro e, injection e with e1, apply not_self_sub_left_tensor e1,
--       assumption,
--       symmetry, exact nAB,
--         intro e, injection e with e1, apply not_self_sub_left_tensor e1,
--         intro e, injection e with e1, apply not_self_sub_right_tensor e1 },
--     case steps.par : A B ai bi ci st₁ {
--       rcases (ps.valid _ hΔ) with _ | _ | _ | _ | ⟨_,_,_,_,_,nAB⟩,
--       cases sB, cases S (Link.par ai bi ci A B); apply steps_par_unique_prev _ _ _ st₁,
--       assumption, cases (ps.valid _ hΔ), assumption,
--         intro e, injection e with e1, apply not_self_sub_right_par e1,
--         intro e, injection e with e1, apply not_self_sub_left_par e1,
--       assumption,
--       symmetry, exact nAB,
--         intro e, injection e with e1, apply not_self_sub_left_par e1,
--         intro e, injection e with e1, apply not_self_sub_right_par e1 }
--   end

-- end