import tactic

inductive Form : Type
| atom : ℕ → Form
| tensor : Form → Form → Form
| par : Form → Form → Form
| neg : Form → Form

infix ` ⊗ `:70 := Form.tensor
infix ` ⅋ `:65 := Form.par
prefix `~` := Form.neg

inductive Link : Type
| ax : ℕ → ℕ → Form → Link
| cut : ℕ → ℕ → Form → Link
| tensor : ℕ → ℕ → ℕ → Form → Form → Link
| par : ℕ → ℕ → ℕ → Form → Form → Link
| con : ℕ → Form → Link

def Form_occ := Form × ℕ

inductive premise : Form_occ → Link → Prop
| cut_pos {A i j}          : premise (A,i) (Link.cut i j A)
| cut_neg {A i j}          : premise (~A,j) (Link.cut i j A)
| tensor_left {A B i j k}  : premise (A,i) (Link.tensor i j k A B)
| tensor_right {A B i j k} : premise (B,j) (Link.tensor i j k A B)
| par_left {A B i j k}     : premise (A,i) (Link.par i j k A B)
| par_right {A B i j k}    : premise (B,j) (Link.par i j k A B)
| con {A i}                : premise (A,i) (Link.con i A)

inductive conclusion : Form_occ → Link → Prop
| ax_pos {A i j}     : conclusion (A,i) (Link.ax i j A)
| ax_neg {A i j}     : conclusion (~A,j) (Link.ax i j A)
| tensor {A B i j k} : conclusion (A ⊗ B,k) (Link.tensor i j k A B)
| par {A B i j k}    : conclusion (A ⅋ B,k) (Link.par i j k A B)

inductive valid_link : Link → Prop
| ax  (i j A) : valid_link (Link.ax i j A)
| cut (i j A) : valid_link (Link.cut i j A)
| con (i A) : valid_link (Link.con i A)
| tensor (i j k A B) : (A,i) ≠ (B,j) → valid_link (Link.tensor i j k A B)
| par (i j k A B) : (A,i) ≠ (B,j) → valid_link (Link.par i j k A B)

structure proof_structure : Type :=
(links : set Link)
(valid : ∀ l ∈ links, valid_link l)
(prem_unique : ∀ Ai : Form_occ, ∀ l₁ l₂ ∈ links, premise Ai l₁ → premise Ai l₂ → l₁ = l₂)
(con_unique : ∀ Ai : Form_occ, ∀ l₁ l₂ ∈ links, conclusion Ai l₁ → conclusion Ai l₂ → l₁ = l₂)

inductive mem_Form_occ_ps (Ai : Form_occ) (ps : proof_structure) : Prop
| prem (l) : l ∈ ps.links → premise Ai l → mem_Form_occ_ps
| con (l) : l ∈ ps.links → conclusion Ai l → mem_Form_occ_ps

instance : has_mem Form_occ proof_structure := ⟨mem_Form_occ_ps⟩

@[reducible]
def dir := bool

@[pattern] def down := ff
@[pattern] def up := tt

@[pattern] def with_down (Ai : Form_occ) := (Ai,down)
@[pattern] def with_up (Ai : Form_occ) := (Ai,up)
postfix `↓`:max_plus := with_down
postfix `↑`:max_plus := with_up

@[reducible]
def switch := bool

@[reducible, pattern] def L := ff
@[reducible, pattern] def R := tt

def switching := Link → switch

@[simp]
def switch.flip {α β} (f : α → α → β) : switch → α → α → β
| L a b := f a b
| R a b := f b a

inductive steps_tensor (Ai Bi Ci : Form_occ) : Form_occ × dir → Form_occ × dir → Prop
| down : steps_tensor Ai↓ Ci↓
| turn : steps_tensor Bi↓ Ai↑
| up : steps_tensor Ci↑ Bi↑

inductive steps_par (Ai Bi Ci : Form_occ) : Form_occ × dir → Form_occ × dir → Prop
| down : steps_par Ai↓ Ci↓
| turn : steps_par Bi↓ Bi↑
| up : steps_par Ci↑ Ai↑

inductive dual (A : Form) (ai ni : ℕ) : Form_occ → Form_occ → Prop
| posneg : dual (A,ai) (~A,ni)
| negpos : dual (~A,ni) (A,ai)

inductive steps (T : switch) : Link → Form_occ × dir → Form_occ × dir → Prop
| ax  {A ai ni Bi Ci} : dual A ai ni Bi Ci → steps (Link.ax ai ni A) Bi↑ Ci↓
| cut {A ai ni Bi Ci} : dual A ai ni Bi Ci → steps (Link.cut ai ni A) Bi↓ Ci↑
| con {A ai}          : steps (Link.con ai A) (A, ai)↓ (A,ai)↑
| tensor {A B ai bi ci X Y} :
  T.flip steps_tensor (A, ai) (B, bi) (A ⊗ B, ci) X Y →
  steps (Link.tensor ai bi ci A B) X Y
| par {A B ai bi ci X Y} :
  T.flip steps_par (A, ai) (B, bi) (A ⅋ B, ci) X Y →
  steps (Link.par ai bi ci A B) X Y

inductive trip (ps : proof_structure) (S : switching) : ℕ → Form_occ × dir → Form_occ × dir → Prop
| single {Ai d}    : Ai ∈ ps → trip 0 (Ai,d) (Ai,d)
| cons {X Y Z Δ n} : Δ ∈ ps.links → steps (S Δ) Δ X Y → trip n Y Z → trip (n.succ) X Z

inductive trip2 (ps : proof_structure) (S : switching) : Form_occ × dir → Form_occ × dir → Prop
| single (Ai : Form_occ) (d : dir) : Ai ∈ ps → trip2 (Ai,d) (Ai,d)
| front (Ai Bi Ci : Form_occ) (d₁ d₂ d₃ : dir) (Δ : Link) :
  Δ ∈ ps.links → steps (S Δ) Δ (Ai,d₁) (Bi,d₂) → trip2 (Bi,d₂) (Ci, d₃) → trip2 (Ai,d₁) (Ci,d₃)
| back (Ai Bi Ci : Form_occ) (d₁ d₂ d₃ : dir) (Δ : Link) :
  Δ ∈ ps.links → steps (S Δ) Δ (Bi,d₂) (Ci,d₃) → trip2 (Ai,d₁) (Bi, d₂) → trip2 (Ai,d₁) (Ci,d₃)

inductive list_trip (ps : proof_structure) (S : switching) : list (Form_occ × dir) → Prop
| emp : list_trip []
| single (Ai : Form_occ) (d : dir) : Ai ∈ ps → list_trip [(Ai,d)]
| cons (Ai Bi : Form_occ) (d₁ d₂ : dir) (Γ : list (Form_occ × dir)) (Δ : Link) :
  Δ ∈ ps.links → steps (S Δ) Δ (Ai,d₁) (Bi,d₂) → list_trip ((Bi,d₂) :: Γ) → list_trip ((Ai,d₁) :: (Bi,d₂) :: Γ)

lemma not_self_dual {A} : (~A) ≠ A :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_gt _ e,
  rw [Form.sizeof, nat.add_comm], exact nat.lt_succ_self _ ,
end

lemma not_self_double_dual {A} : (~~A) ≠ A :=
begin
  suffices : A ≠ (~~A), by symmetry; assumption,
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  refine lt_trans _ _, exact (~A).sizeof,
  rw [Form.sizeof, nat.add_comm], exact nat.lt_succ_self _ ,
  rw [Form.sizeof, Form.sizeof], apply add_lt_add_left,
  have : sizeof (~A) = (~A).sizeof, refl, rw this,
  rw [Form.sizeof, nat.add_comm], exact nat.lt_succ_self _ ,
end

lemma not_self_sub_left_tensor {A B} : A ≠ A ⊗ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw nat.add_comm, rw nat.add_comm 1,
  apply nat.le_add_right,
end

lemma not_self_sub_right_tensor {A B} : B ≠ A ⊗ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw [←nat.add_assoc],
  apply nat.le_add_right,
end

lemma not_self_sub_left_par {A B} : A ≠ A ⅋ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw nat.add_comm, rw nat.add_comm 1,
  apply nat.le_add_right,
end

lemma not_self_sub_right_par {A B} : B ≠ A ⅋ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw [←nat.add_assoc],
  apply nat.le_add_right,
end

section
  variable {Δ : Link}
  variable {T : switch}
  variables {Ai Bi Ci : Form_occ}
  variables {X Y Z : Form_occ × dir}

  lemma dual_unique_prev {A pi ni} :
    dual A pi ni Ai Ci → dual A pi ni Bi Ci → Ai = Bi :=
  begin
    intros d₁ d₂,
    generalize_hyp e : Ci = Ci' at d₂,
    cases d₁; cases d₂; injection e with e1 e2; cases e2;
    try { cases e1 }; [refl, cases not_self_dual e1, cases not_self_dual e1.symm, refl]
  end

  lemma dual_unique_next {A pi ni} :
    dual A pi ni Ai Bi → dual A pi ni Ai Ci → Bi = Ci :=
  begin
    intros d₁ d₂,
    generalize_hyp e : Ai = Ai' at d₂,
    cases d₁; cases d₂; injection e with e1 e2; cases e2;
    try { cases e1 }; [refl, cases not_self_dual e1.symm, cases not_self_dual e1, refl]
  end

  lemma steps_tensor_unique_prev : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_tensor Ai Bi Ci X Z → steps_tensor Ai Bi Ci Y Z → X = Y :=
  by intros _ _ _ s₁ s₂; cases s₁; cases s₂; try {refl}; try {contradiction}

  lemma steps_tensor_unique_next : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_tensor Ai Bi Ci X Y → steps_tensor Ai Bi Ci X Z → Y = Z :=
  by intros _ _ _ s₁ s₂; cases s₁; cases s₂; try {refl}; try {contradiction}

  lemma steps_par_unique_prev : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_par Ai Bi Ci X Z → steps_par Ai Bi Ci Y Z → X = Y :=
  by intros _ _ _ s₁ s₂; cases s₁; cases s₂; try {refl}; try {contradiction}

  lemma steps_par_unique_next : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_par Ai Bi Ci X Y → steps_par Ai Bi Ci X Z → Y = Z :=
  by intros _ _ _ s₁ s₂; cases s₁; cases s₂; try {refl}; try {contradiction}

  theorem steps_unique_prev : valid_link Δ → steps T Δ X Z → steps T Δ Y Z → X = Y :=
  begin
    intros hΔ s₁ s₂,
    cases s₁,
    case steps.ax : A ai ni Bi Ci d₁ {
      cases s₂ with _ _ _ Di _ d₂,
      rw dual_unique_prev d₁ d₂ },
    case steps.cut : A ai ni Bi Ci d₁ {
      rcases s₂ with _ | ⟨_,_,_,Di,_,d₂⟩,
      rw dual_unique_prev d₂ d₁
    },
    case steps.con : A ai { cases s₂, refl },
    case steps.tensor : A B ai bi ci X y t₁ {
      rcases s₂ with _ | _ | _ | ⟨_,_,_,_,_,_,_,t₂⟩,
      cases T; simp at t₁ t₂;
      apply steps_tensor_unique_prev _ _ _ t₁ t₂;
      cases hΔ, finish,
      intro e, injection e with e1,
      exact not_self_sub_right_tensor e1,
      intro e, injection e with e1,
      exact not_self_sub_left_tensor e1,
      finish,
      intro e, injection e with e1,
      exact not_self_sub_left_tensor e1,
      intro e, injection e with e1,
      exact not_self_sub_right_tensor e1,
    },
    case steps.par : A B ai bi ci X y p₁ {
      rcases s₂ with _ | _ | _ | _ | ⟨_,_,_,_,_,_,_,p₂⟩,
      cases T; simp at p₁ p₂;
      apply steps_par_unique_prev _ _ _ p₁ p₂;
      cases hΔ, finish,
      intro e, injection e with e1,
      exact not_self_sub_right_par e1,
      intro e, injection e with e1,
      exact not_self_sub_left_par e1,
      finish,
      intro e, injection e with e1,
      exact not_self_sub_left_par e1,
      intro e, injection e with e1,
      exact not_self_sub_right_par e1,
    },
  end

  theorem steps_unique_next : valid_link Δ → steps T Δ X Y → steps T Δ X Z → Y = Z :=
  begin
    intros hΔ s₁ s₂,
    cases s₁,
    case steps.ax : A ai ni Bi Ci d₁ {
      cases s₂ with _ _ _ Di _ d₂,
      rw dual_unique_next d₁ d₂ },
    case steps.cut : A ai ni Bi Ci d₁ {
      rcases s₂ with _ | ⟨_,_,_,Di,_,d₂⟩,
      rw dual_unique_next d₂ d₁
    },
    case steps.con : A ai { cases s₂, refl },
    case steps.tensor : A B ai bi ci X y t₁ {
      rcases s₂ with _ | _ | _ | ⟨_,_,_,_,_,_,_,t₂⟩,
      cases T; simp at t₁ t₂;
      apply steps_tensor_unique_next _ _ _ t₁ t₂;
      cases hΔ, finish,
      intro e, injection e with e1,
      exact not_self_sub_right_tensor e1,
      intro e, injection e with e1,
      exact not_self_sub_left_tensor e1,
      finish,
      intro e, injection e with e1,
      exact not_self_sub_left_tensor e1,
      intro e, injection e with e1,
      exact not_self_sub_right_tensor e1,
    },
    case steps.par : A B ai bi ci X y p₁ {
      rcases s₂ with _ | _ | _ | _ | ⟨_,_,_,_,_,_,_,p₂⟩,
      cases T; simp at p₁ p₂;
      apply steps_par_unique_next _ _ _ p₁ p₂;
      cases hΔ, finish,
      intro e, injection e with e1,
      exact not_self_sub_right_par e1,
      intro e, injection e with e1,
      exact not_self_sub_left_par e1,
      finish,
      intro e, injection e with e1,
      exact not_self_sub_left_par e1,
      intro e, injection e with e1,
      exact not_self_sub_right_par e1,
    },
  end

  lemma con_of_steps_up :
    steps T Δ Ai↑ X → conclusion Ai Δ :=
  begin
    intros s, cases s,
    case steps.ax : A i j Ai Bi u { cases u; constructor, },
    case steps.tensor : A B i j k Ci u { cases T; cases u; constructor },
    case steps.par : A B i j k Ci u { cases T; cases u; constructor },
  end

  lemma prem_of_steps_down :
    steps T Δ Ai↓ X → premise Ai Δ :=
  begin
    intros s, cases s,
    case steps.cut : A i j Ai Bi u { cases u; constructor, },
    case steps.tensor : A B i j k Ci u { cases T; cases u; constructor },
    case steps.par : A B i j k Ci u { cases T; cases u; constructor },
    case steps.con : { constructor }
  end

  lemma con_of_steps_down :
    steps T Δ X Ai↓ → conclusion Ai Δ :=
  begin
    intros s, cases s,
    case steps.ax : A i j Ai Bi u { cases u; constructor, },
    case steps.tensor : A B i j k Ci u { cases T; cases u; constructor },
    case steps.par : A B i j k Ci u { cases T; cases u; constructor },
  end

  lemma prem_of_steps_up :
    steps T Δ X Ai↑ → premise Ai Δ :=
  begin
    intros s, cases s,
    case steps.cut : A i j Ai Bi u { cases u; constructor, },
    case steps.tensor : A B i j k Ci u { cases T; cases u; constructor },
    case steps.par : A B i j k Ci u { cases T; cases u; constructor },
    case steps.con : { constructor }
  end

  lemma mem_ps_of_steps_prev {ps : proof_structure} {d : dir} :
    Δ ∈ ps.links → steps T Δ (Ai,d) X → Ai ∈ ps :=
  begin
    intros hΔ s,
    cases d,
    -- down
    case bool.ff : { apply mem_Form_occ_ps.prem Δ hΔ, exact prem_of_steps_down s }, 
    -- up
    case bool.tt : { apply mem_Form_occ_ps.con Δ hΔ, exact con_of_steps_up s }, 
  end

  lemma mem_ps_of_steps_next {ps : proof_structure} {d : dir} :
    Δ ∈ ps.links → steps T Δ X (Bi,d) → Bi ∈ ps :=
  begin
    intros hΔ s,
    cases d,
    -- down
    case bool.ff : { apply mem_Form_occ_ps.con Δ hΔ, exact con_of_steps_down s }, 
    -- up
    case bool.tt : { apply mem_Form_occ_ps.prem Δ hΔ, exact prem_of_steps_up s }, 
  end

end

section
  variable {ps : proof_structure}
  variable {S : switching}
  variables {X Y Z : Form_occ × dir}
  variables {n m : ℕ}

  theorem link_unique_of_steps_prev {Δ₁ Δ₂} :
    Δ₁ ∈ ps.links → Δ₂ ∈ ps.links → steps (S Δ₁) Δ₁ X Y → steps (S Δ₂) Δ₂ X Z → Δ₁ = Δ₂ :=
  begin
    intros v₁ v₂ s₁ s₂,
    rcases X with ⟨Ai,⟨_|_⟩⟩,
      apply ps.prem_unique Ai _ _ v₁ v₂ (prem_of_steps_down s₁) (prem_of_steps_down s₂),
    apply ps.con_unique Ai _ _ v₁ v₂ (con_of_steps_up s₁) (con_of_steps_up s₂),
  end

  theorem link_unique_of_steps_next {Δ₁ Δ₂} :
    Δ₁ ∈ ps.links → Δ₂ ∈ ps.links → steps (S Δ₁) Δ₁ X Z → steps (S Δ₂) Δ₂ Y Z → Δ₁ = Δ₂ :=
  begin
    intros v₁ v₂ s₁ s₂,
    rcases Z with ⟨Ci,⟨_|_⟩⟩,
      apply ps.con_unique Ci _ _ v₁ v₂ (con_of_steps_down s₁) (con_of_steps_down s₂),
    apply ps.prem_unique Ci _ _ v₁ v₂ (prem_of_steps_up s₁) (prem_of_steps_up s₂),
  end

  def trip.rcons {Δ} : Δ ∈ ps.links → trip ps S n X Y → steps (S Δ) Δ Y Z → trip ps S n.succ X Z :=
  begin
    revert X Y Z,
    induction n,
    case nat.zero : {
      rintros X Y Z hΔ ⟨Ai,d,hA⟩ s,
      apply trip.cons hΔ s,
      cases Z with Ci d',
      apply trip.single,
      apply mem_ps_of_steps_next hΔ s,
    },
    case nat.succ : n ih {
      rintros X Y Z hΔ tXY sYZ,
      cases tXY with _ _ _ _ W _ Δ' _ hΔ' sXW tWY,
      apply trip.cons hΔ' sXW,
      apply ih hΔ tWY sYZ,
    },
  end

  def trip.concat : trip ps S n X Y → trip ps S m Y Z → trip ps S (n + m) X Z :=
  begin
    revert X Y Z n,
    induction m,
    case nat.zero : {
      intros X Y Z _ tXY tYZ,
      cases tYZ,
      exact tXY,
    },
    case nat.succ : m ih {
      intros X Y Z n tXY tYZ,
      rw [nat.add_succ, nat.add_comm, ←nat.add_succ, nat.add_comm],
      cases tYZ with _ _ _ _ W _ Δ' _ hΔ' sYW tWZ,
      apply ih _ tWZ,
      apply trip.rcons hΔ' tXY sYW }
  end

  theorem trip_unique_start : trip ps S n X Z → trip ps S n Y Z → X = Y :=
  begin
    intros tX tY,
    revert X Y,
    induction n,
    case nat.zero : { intros, cases tX; cases tY, refl},
    case nat.succ : n ih {
      rintros X Y tX tY,
      rcases tX with _ | ⟨_,X',_,Δ,_,hΔ,sX,tX'⟩,
      rcases tY with _ | ⟨_,Y',_,Δ',_,hΔ',sY,tY'⟩,
      have : Y' = X', by exact ih tY' tX',
      rw this at sY,
      have : Δ' = Δ, apply link_unique_of_steps_next hΔ' hΔ sY sX,
      rw this at sY,
      exact steps_unique_prev (ps.valid Δ hΔ) sX sY,
      }
  end

  lemma trip_exists_rcons : trip ps S n.succ X Z → ∃ Y Δ, ∃ hΔ : Δ ∈ ps.links, ∃ tXY : trip ps S n X Y, steps (S Δ) Δ Y Z :=
  begin
    revert X,
    induction n,
    case nat.zero : {
      intros X tXZ, cases tXZ with _ _ _ _ Y _ Δ _ hΔ sXY tYZ,
      use X, use Δ, refine ⟨hΔ,_⟩,
      constructor,
      cases X with Ai d,
      constructor,
      apply mem_ps_of_steps_prev hΔ sXY,
      cases tYZ, assumption,
      },
    case nat.succ : n ih {
      intros X tXZ, cases tXZ with _ _ _ _ Y _ Δ _ hΔ sXY tYZ,
      specialize ih tYZ,
      rcases ih with ⟨Y',Δ',hΔ',tYY',sY'Z⟩,
      exact ⟨Y',Δ',hΔ',trip.cons hΔ sXY tYY',sY'Z⟩,
    }
  end

  theorem trip_unique_stop : trip ps S n X Y → trip ps S n X Z → Y = Z :=
  begin
    revert Y Z,
    induction n,
    case nat.zero : { intros _ _ tXY tXZ, cases tXY, cases tXZ, refl },
    case nat.succ : n ih {
      intros Y Z tXY tXZ,
      rcases (trip_exists_rcons tXY) with ⟨U,Δ₁,hΔ₁,tXU, sUY⟩,
      rcases (trip_exists_rcons tXZ) with ⟨V,Δ₂,hΔ₂,tXV, sVZ⟩,
      have : V = U, apply ih tXV tXU,
      rw this at sVZ,
      have : Δ₂ = Δ₁, apply link_unique_of_steps_prev hΔ₂ hΔ₁ sVZ sUY,
      rw this at sVZ,
      apply steps_unique_next (ps.valid Δ₁ hΔ₁) sUY sVZ,
      }
  end

end

