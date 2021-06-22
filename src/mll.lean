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

theorem not_self_double_dual {A} : (~~A) ≠ A :=
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
| con (i A) : valid_link (Link.con i A)
| tensor (i j k A B) : (A,i) ≠ (B,j) → valid_link (Link.tensor i j k A B)
| par (i j k A B) : (A,i) ≠ (B,j) → valid_link (Link.par i j k A B)

structure proof_structure : Type :=
(links : set Link)
(valid : ∀ l ∈ links, valid_link l)
(prem_unique : ∀ Ai : Form_occ, ∀ l₁ l₂ ∈ links, is_premise Ai l₁ → is_premise Ai l₂ → l₁ = l₂)
(con_unique : ∀ Ai : Form_occ, ∀ l₁ l₂ ∈ links, is_conclusion Ai l₁ → is_conclusion Ai l₂ → l₁ = l₂)

inductive mem_Form_occ_ps (Ai : Form_occ) (ps : proof_structure) : Prop
| prem (l) : l ∈ ps.links → is_premise Ai l → mem_Form_occ_ps
| con (l) : l ∈ ps.links → is_conclusion Ai l → mem_Form_occ_ps

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

theorem steps_tensor_unique_prev {Ai Bi Ci : Form_occ} {X Y Z} : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_tensor Ai Bi Ci X Z → steps_tensor Ai Bi Ci Y Z → X = Y :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_tensor_unique_next {Ai Bi Ci : Form_occ} {X Y Z} : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_tensor Ai Bi Ci X Y → steps_tensor Ai Bi Ci X Z → Y = Z :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_par_unique_prev {Ai Bi Ci : Form_occ} {X Y Z} : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_par Ai Bi Ci X Z → steps_par Ai Bi Ci Y Z → X = Y :=
begin
  intros _ _ _ s₁ s₂,
  cases s₁; cases s₂; try {refl}; try {contradiction},
end

theorem steps_par_unique_next {Ai Bi Ci : Form_occ} {X Y Z} : Ai ≠ Bi → Bi ≠ Ci → Ai ≠ Ci → steps_par Ai Bi Ci X Y → steps_par Ai Bi Ci X Z → Y = Z :=
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


inductive trip (ps : proof_structure) (S : switching) : list (Form_occ × dir) → Prop
| emp : trip []
| single (Ai : Form_occ) (d : dir) : Ai ∈ ps → trip [(Ai,d)]
| cons (Ai Bi : Form_occ) (d₁ d₂ : dir) (Γ : list (Form_occ × dir)) (Δ : Link) :
  Δ ∈ ps.links → steps (S Δ) Δ (Ai,d₁) (Bi,d₂) → trip ((Bi,d₂) :: Γ) → trip ((Ai,d₁) :: (Bi,d₂) :: Γ)

theorem steps_link_from_con {T : switch} {Δ : Link} {Ai : Form_occ} {X} :
  steps T Δ Ai↑ X → is_conclusion Ai Δ :=
begin
  intros s,
  cases s,
  case steps.ax : A i j Ai Bi u { cases u, left, refl, right, refl },
  case steps.tensor : A B i j k Ci t {
    cases T; simp at t; cases t; constructor },
  case steps.par : A B i j k Ci t {
    cases T; simp at t; cases t; constructor },
end

theorem steps_link_from_prem {T : switch} {Δ : Link} {Ai : Form_occ} {X} :
  steps T Δ Ai↓ X → is_premise Ai Δ :=
begin
  intros s,
  cases s,
  case steps.cut : A i j Ai Bi u { cases u, left, refl, right, refl },
  case steps.tensor : A B i j k Ci t {
    cases T; simp at t; cases t, left, refl, right, refl, right, refl, left, refl,},
  case steps.par : A B i j k Ci t {
    cases T; simp at t; cases t, left, refl, right, refl, right, refl, left, refl,},
  constructor,
end

theorem steps_link_to_con {T : switch} {Δ : Link} {Ai : Form_occ} {X} :
  steps T Δ X Ai↓ → is_conclusion Ai Δ :=
begin
  intros s,
  cases s,
  case steps.ax : A i j Ai Bi u { cases u, right, refl, left, refl },
  case steps.tensor : A B i j k Ci t {
    cases T; simp at t; cases t; constructor },
  case steps.par : A B i j k Ci t {
    cases T; simp at t; cases t; constructor },
end

theorem steps_link_to_prem {T : switch} {Δ : Link} {Ai : Form_occ} {X} :
  steps T Δ X Ai↑ → is_premise Ai Δ :=
begin
  intros s,
  cases s,
  case steps.cut : A i j Ai Bi u { cases u, right, refl, left, refl },
  case steps.tensor : A B i j k Ci t {
    cases T; simp at t; cases t, left, refl, right, refl, right, refl, left, refl,},
  case steps.par : A B i j k Ci t {
    cases T; simp at t; cases t, right, refl, left, refl, left, refl, right, refl,},
  constructor,
end

theorem steps_link_to_unique {ps : proof_structure} {S : switching} {Ai Bi Ci} {d₁ d₂ d₃} {Δ₁ Δ₂} :
  Δ₁ ∈ ps.links → Δ₂ ∈ ps.links → steps (S Δ₁) Δ₁ (Ai,d₁) (Ci,d₃) → steps (S Δ₂) Δ₂ (Bi,d₂) (Ci,d₃) → Δ₁ = Δ₂ :=
begin
  intros v₁ v₂ s₁ s₂,
  cases d₃,
    apply ps.con_unique Ci _ _ v₁ v₂ (steps_link_to_con s₁) (steps_link_to_con s₂),
  apply ps.prem_unique Ci _ _ v₁ v₂ (steps_link_to_prem s₁) (steps_link_to_prem s₂),
end

theorem trip_unique_cons (ps : proof_structure) (S : switching) (t : list (Form_occ × dir)) (nnil : t ≠ []) (Ai Bi : Form_occ) (d₁ d₂ : dir) :
  trip ps S ((Ai,d₁)::t) → trip ps S ((Bi,d₂)::t) → (Ai,d₁) = (Bi,d₂) :=
begin
  intros tA tB,
  rcases t with _ | ⟨⟨Ci,d₃⟩,t⟩, contradiction,
  rcases tA with _ | _ | ⟨_,_,_,_,_,Δ,hΔ,sA,tC⟩,
  rcases tB with _ | _ | ⟨_,_,_,_,_,Δ',hΔ',sB,tC⟩,
  have : Δ' = Δ, symmetry, apply steps_link_to_unique hΔ hΔ' sA sB, cases this,
  cases sA,
  case steps.ax : { cases sB, simp, apply dual_unique_prev; assumption },
  case steps.cut : { cases sB, simp, apply dual_unique_prev; assumption },
  case steps.con : { cases sB, refl},
  case steps.tensor : A B ai bi ci st₁ {
    rcases (ps.valid _ hΔ) with _ | _ | _ | ⟨_,_,_,_,_,nAB⟩,
    cases sB, cases S (Link.tensor ai bi ci A B); apply steps_tensor_unique_prev _ _ _ st₁,
    assumption, cases (ps.valid _ hΔ), assumption,
      intro e, injection e with e1, apply not_self_sub_right_tensor e1,
      intro e, injection e with e1, apply not_self_sub_left_tensor e1,
    assumption,
    symmetry, exact nAB,
      intro e, injection e with e1, apply not_self_sub_left_tensor e1,
      intro e, injection e with e1, apply not_self_sub_right_tensor e1 },
  case steps.par : A B ai bi ci st₁ {
    rcases (ps.valid _ hΔ) with _ | _ | _ | _ | ⟨_,_,_,_,_,nAB⟩,
    cases sB, cases S (Link.par ai bi ci A B); apply steps_par_unique_prev _ _ _ st₁,
    assumption, cases (ps.valid _ hΔ), assumption,
      intro e, injection e with e1, apply not_self_sub_right_par e1,
      intro e, injection e with e1, apply not_self_sub_left_par e1,
    assumption,
    symmetry, exact nAB,
      intro e, injection e with e1, apply not_self_sub_left_par e1,
      intro e, injection e with e1, apply not_self_sub_right_par e1 }
end

inductive subpath {α} : list α → list α → Prop
| nil (T) : subpath [] T
| cons (t X Y) : subpath X Y → subpath (t::X) (t::Y)

-- theorem trip_unique (ps : proof_structure) (S : switching) (Γ₁ Γ₂ : list (Form_occ × dir)) (Ai : Form_occ) (d : dir) : trip ps S ((Ai,d)::Γ₁) → trip ps S ((Ai,d)::Γ₂) → Γ₁.length ≤ Γ₂.length → subpath Γ₁ Γ₂ :=
-- begin
--   induction Γ₁, simp, intros, constructor,
--   case list.cons : Bid Γ₁ ih₁ {
--     intros t₁ t₂ hlt,
--     induction Γ₂, simp at hlt, contradiction,
--     case list.cons : Cid Γ₂ ih₂ {
--       suffices : Bid = Cid, rw this, constructor, 
--     },
--   }
-- end

inductive cycle_trip (ps : proof_structure) (S : switching) : list (Form_occ × dir) → Prop
| cycle_trip (Ai Bi) (d₁ d₂) (Δ) (Γ) : Δ ∈ ps.links → trip ps S ((Ai,d₁) :: Γ ++ [(Bi,d₂)]) → steps (S Δ) Δ (Bi,d₂) (Ai,d₁) → cycle_trip ((Ai,d₁) :: Γ ++ [(Bi,d₂)])

inductive cycle_equiv {α} (l : list α) : list α → Prop
| split (l₁ l₂) : l₂ ++ l₁ = l → cycle_equiv (l₁ ++ l₂)

def longtrip (ps : proof_structure) (S : switching) := 
  ∀ Γ₁ Γ₂, cycle_trip ps S Γ₁ → cycle_trip ps S Γ₂ → cycle_equiv Γ₁ Γ₂

