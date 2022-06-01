import tactic

inductive Form : Type
| atom : ℕ → Form
| tensor : Form → Form → Form
| par : Form → Form → Form
| neg : Form → Form

infix ` ⊗ `:70 := Form.tensor
infix ` ⅋ `:65 := Form.par
prefix `~` := Form.neg

theorem not_self_dual {A} : A ≠ ~A :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm], exact nat.lt_succ_self _ ,
end

theorem not_self_sub_left_tensor {A B} : A ≠ A ⊗ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw nat.add_comm, rw nat.add_comm 1,
  apply nat.le_add_right,
end

theorem not_self_sub_right_tensor {A B} : B ≠ A ⊗ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw [←nat.add_assoc],
  apply nat.le_add_right,
end

theorem not_self_sub_left_par {A B} : A ≠ A ⅋ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw nat.add_comm, rw nat.add_comm 1,
  apply nat.le_add_right,
end

theorem not_self_sub_right_par {A B} : B ≠ A ⅋ B :=
begin
  intro e,
  apply_fun Form.sizeof at e,
  refine ne_of_lt _ e,
  rw [Form.sizeof, nat.add_comm],
  apply nat.lt_of_succ_le,
  rw [←nat.add_assoc],
  apply nat.le_add_right,
end


inductive Link : Type
| ax : ℕ → ℕ → Form → Link
| cut : ℕ → ℕ → Form → Link
| tensor : ℕ → ℕ → ℕ → Form → Form → Link
| par : ℕ → ℕ → ℕ → Form → Form → Link
| con : ℕ → Form → Link

def Form_occ := Form × ℕ

def is_premise (Ai : Form_occ) : Link → Prop
| (Link.ax n m B) := false
| (Link.cut n m B) := (Ai = ⟨B,n⟩) ∨ (Ai = ⟨~B,m⟩)
| (Link.tensor n m k A B) := (Ai = ⟨A,n⟩) ∨ (Ai = ⟨B,m⟩)
| (Link.par n m k A B) := (Ai = ⟨A,n⟩) ∨ (Ai = ⟨B,m⟩)
| (Link.con n A) := Ai = ⟨A,n⟩

def is_conclusion (Ai : Form_occ) : Link → Prop
| (Link.ax n m B) := (Ai = ⟨B,n⟩) ∨ (Ai = ⟨~B,m⟩)
| (Link.cut n m B) := false
| (Link.tensor n m k A B) := Ai = ⟨A ⊗ B,k⟩
| (Link.par n m k A B) := Ai = ⟨A ⅋ B,k⟩
| (Link.con n A) := false

inductive valid_link : Link → Prop
| ax  (i j A) : valid_link (Link.ax i j A)
| cut (i j A) : valid_link (Link.cut i j A)
| tensor (i j k A B) : (A,i) ≠ (B,j) → valid_link (Link.tensor i j k A B)
| par (i j k A B) : (A,i) ≠ (B,j) → valid_link (Link.par i j k A B)
| con (i A) : valid_link (Link.con i A)

structure proof_structure : Type :=
(links : set Link)
(valid : ∀ l ∈ links, valid_link l)
(form_occs : set Form_occ)
(link_prem : ∀ l ∈ links, ∀ Ai : Form_occ, is_premise Ai l → Ai ∈ form_occs)
(link_con : ∀ l ∈ links, ∀ Ai : Form_occ, is_conclusion Ai l → Ai ∈ form_occs)
(premise : Form_occ → Link)
(prem_unique : ∀ Ai ∈ form_occs, ∀ l ∈ links, is_premise Ai l → premise Ai = l)
(prem_range : ∀ Ai ∈ form_occs, premise Ai ∈ links ∧ is_premise Ai (premise Ai))
(conclusion : Form_occ → Link)
(con_unique : ∀ Ai ∈ form_occs, ∀ l ∈ links, is_conclusion Ai l → conclusion Ai = l)
(con_range : ∀ Ai ∈ form_occs, conclusion Ai ∈ links ∧ is_conclusion Ai (conclusion Ai))

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

@[simp] lemma flip_L {α β} {f : α → α → β} {a b} : switch.flip f L a b = f a b := rfl
@[simp] lemma flip_R {α β} {f : α → α → β} {a b} : switch.flip f R a b = f b a := rfl

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
| ax  (A : Form) (ai ni : ℕ) (Bi Ci) : dual A ai ni Bi Ci → steps (Link.ax ai ni A) Bi↑ Ci↓
| cut (A : Form) (ai ni : ℕ) (Bi Ci) : dual A ai ni Bi Ci → steps (Link.cut ai ni A) Bi↓ Ci↑
| con (A : Form) (ai : ℕ)            : steps (Link.con ai A) (A, ai)↓ (A,ai)↑
| tensor (A B : Form) (ai bi ci : ℕ) (x y) :
  T.flip steps_tensor (A, ai) (B, bi) (A ⊗ B, ci) x y →
  steps (Link.tensor ai bi ci A B) x y
| par (A B : Form) (ai bi ci : ℕ) (x y) :
  T.flip steps_par (A, ai) (B, bi) (A ⅋ B, ci) x y →
  steps (Link.par ai bi ci A B) x y

theorem dual_unique_prev {A ai ni Bi Ci Di}
  (d₁ : dual A ai ni Bi Ci) (d₂ : dual A ai ni Di Ci) : Bi = Di :=
begin
  generalize_hyp e : Ci = Ci' at d₂,
  have : A ≠ ~A,
  { intro e,
    apply_fun Form.sizeof at e,
    refine ne_of_lt _ e,
    rw [Form.sizeof, nat.add_comm], exact nat.lt_succ_self _ },
  cases d₁; cases d₂; injection e with e1 e2; cases e2;
  try { cases e1 }; [refl, cases this e1.symm, cases this e1, refl]
end

theorem steps_tensor_unique_prev (Ai Bi Ci : Form_occ) (X Y Z) : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_tensor Ai Bi Ci X Z → steps_tensor Ai Bi Ci Y Z → X = Y :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_tensor_unique_next (Ai Bi Ci : Form_occ) (X Y Z) : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_tensor Ai Bi Ci X Y → steps_tensor Ai Bi Ci X Z → Y = Z :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_par_unique_prev (Ai Bi Ci : Form_occ) (X Y Z) : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_par Ai Bi Ci X Z → steps_par Ai Bi Ci Y Z → X = Y :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_par_unique_next (Ai Bi Ci : Form_occ) (X Y Z) : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_par Ai Bi Ci X Y → steps_par Ai Bi Ci X Z → Y = Z :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_unique_prev {T : switch} {Δ : Link} {X Y Z} : valid_link Δ → steps T Δ X Z → steps T Δ Y Z → X = Y :=
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
    apply steps_tensor_unique_prev _ _ _ _ _ _ _ _ _ t₁ t₂;
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
    apply steps_par_unique_prev _ _ _ _ _ _ _ _ _ p₁ p₂;
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


inductive trip (ps : proof_structure) (S : switching) : list (Form_occ × dir) → Prop
| emp : trip []
| single (Ai : Form_occ) (d : dir) : Ai ∈ ps.form_occs → trip [(Ai,d)]
| consup (Ai Bi : Form_occ) (d : dir) (Γ : list (Form_occ × dir)) : Ai ∈ ps.form_occs → (steps (S (ps.premise Bi)) (ps.premise Bi) (Ai,d) Bi↑) → trip (Bi↑ :: Γ) → trip ((Ai,d) :: Bi↑ :: Γ)
| consdown (Ai Bi : Form_occ) (d : dir) (Γ : list (Form_occ × dir)) : Ai ∈ ps.form_occs → (steps (S (ps.conclusion Bi)) (ps.conclusion Bi) (Ai,d) Bi↓) → trip (Bi↓ :: Γ) → trip ((Ai,d) :: Bi↓ :: Γ)

theorem trip_in_form_occs {ps : proof_structure} (S : switching) (Γ : list (Form_occ × dir)): trip ps S Γ → ∀ Ai d, (Ai,d) ∈ Γ → Ai ∈ ps.form_occs :=
begin
  induction Γ,
  intros _ _ _ h, cases h,
  intros t Ai d h,
  case list.cons : Ai Γ ih { 
    cases t with Bi d₁ hB Ci Di d₂ Γ hC s₁ t₁ Ci Di d₂ Γ hC s₁ t₁,
    { cases h; cases h, assumption, },
    repeat { cases h; cases h, assumption, apply ih t₁, constructor, exact h, apply ih t₁, right, exact h, },
  }
end

theorem premise_valid_link {ps : proof_structure} : ∀ {Ai ∈ ps.form_occs}, valid_link (ps.premise Ai) :=
  λ A hA, ps.valid _ (ps.prem_range _ hA).1

theorem conclusion_valid_link {ps : proof_structure} : ∀ {Ai ∈ ps.form_occs}, valid_link (ps.conclusion Ai) :=
  λ A hA, ps.valid _ (ps.con_range _ hA).1

theorem trip_unique_cons (ps : proof_structure) (S : switching) (t : list (Form_occ × dir)) (nnil : t ≠ []) (Ai Bi : Form_occ) (d₁ d₂ : dir) : trip ps S ((Ai,d₁)::t) → trip ps S ((Bi,d₂)::t) → (Ai,d₁) = (Bi,d₂) :=
begin
  intros tA tB,
  cases t with Cid t, contradiction,
  cases d₁,
  cases d₂,
  repeat {
    rcases tA with _ | _ | ⟨_,Ci,_,_,hA,sAC,t₁⟩ | ⟨_,Ci,_,_,hA,sAC,t₁⟩,
    rcases tB with _ | _ | ⟨_,_,_,_,hB,sBC,t₂⟩,
    apply steps_unique_prev _ sAC sBC,
    apply premise_valid_link,
    apply trip_in_form_occs _ _ t₂, left, refl,
    rcases tB with _ | _ | _ | ⟨_,Ci,_,_,hB,sBC,t₂⟩,
    apply steps_unique_prev _ sAC sBC,
    apply conclusion_valid_link,
    apply trip_in_form_occs _ _ t₂, left, refl },
end

theorem trip_unique (ps : proof_structure) (S : switching) (t : list (Form_occ × dir)) (nnil : t ≠ []) (Ai Bi : Form_occ) (d₁ d₂ : dir) : trip ps S ((Ai,d₁)::t) → trip ps S ((Bi,d₂)::t) → 

def length_non_nil {α} (p : list α) : length p > 1 → p ≠ [] :=
begin
intros ip, intro h,
rw h at ip, have : nil.length = 0, trivial, rw this at ip, cases ip,
end

def cycle_trip (ps : proof_structure) (S : switching) (Ai : Form_occ) (d : dir) (p : list (Form_occ × dir)) (ip : p ≠ []) : Prop := trip ps S (⟨Ai,d⟩::p) ∧ steps (S )(last p ip)

def rotate {α} (l : list α) (n : ℕ) := drop n l ++ take n l

def cycle_equiv {α} (l1 l2 : list α) := ∃ n : ℕ, rotate l1 n = l2

def longtrip (ps : proof_structure) (S1 S2 : switching) (p1 p2 : list (Form_occ × dir)) (ip1 : length p1 > 1) (ip2 : length p2 > 1) : Prop := 
  cycle_trip ps S1 p1 ip1 →
  cycle_trip ps S2 p2 ip2 → cycle_equiv p1 p2

-- theorem tensor_rotate 

def ax_cut (A : Form) : proof_structure :=
{links := {Link.ax 0 1 A, Link.cut 0 1 A},
form_occs := {⟨A,0⟩, ⟨~A,1⟩},
link_prem :=
  begin
    intros l hl Ai hp,
    cases hl,
    rw hl at hp,
    cases hp,
    cases hl,
    cases hp; finish,
  end,
link_con :=
  begin
    intros l hl Ai hc,
    cases hl,
    rw hl at hc,
    cases hc; finish,
    cases hl,
    cases hc; finish,
  end,
premise := (λ Ai, Link.cut 0 1 A),
prem_unique :=
  begin
    intros Ai hA l hl pl,
    cases hl, rw hl at pl, cases pl; finish,
    cases hl, cases pl; finish,
  end,
prem_range :=
  begin
  intros Ai hA,
  split, finish,
  cases hA,
    left, exact hA,
  right, cases hA, refl,
  end,
conclusion := λ Ai, Link.ax 0 1 A, 
con_unique :=
  begin
    intros Ai hA l hl cl,
    cases hA,
    cases hl, finish,
    cases hl, cases cl,
    cases hA,
    cases hl, finish,
    cases hl, cases cl
    end,
con_range := by intros; finish}