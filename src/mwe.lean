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

section
  variable {Δ : Link}
  variable {T : switch}
  variables {Ai Bi Ci : Form_occ}
  variables {X Y Z : Form_occ × dir}

  theorem steps_unique_prev : valid_link Δ → steps T Δ X Z → steps T Δ Y Z → X = Y := sorry

  theorem steps_unique_next : valid_link Δ → steps T Δ X Y → steps T Δ X Z → Y = Z := sorry

  lemma mem_ps_of_steps_next {ps : proof_structure} {d : dir} :
    Δ ∈ ps.links → steps T Δ X (Bi,d) → Bi ∈ ps := sorry

end

section
  variable {ps : proof_structure}
  variable {S : switching}
  variables {X Y Z : Form_occ × dir}
  variables {n m : ℕ}

  theorem link_unique_of_steps_prev {Δ₁ Δ₂} :
    Δ₁ ∈ ps.links → Δ₂ ∈ ps.links → steps (S Δ₁) Δ₁ X Y → steps (S Δ₂) Δ₂ X Z → Δ₁ = Δ₂ := sorry

  theorem link_unique_of_steps_next {Δ₁ Δ₂} :
    Δ₁ ∈ ps.links → Δ₂ ∈ ps.links → steps (S Δ₁) Δ₁ X Z → steps (S Δ₂) Δ₂ Y Z → Δ₁ = Δ₂ := sorry

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

  lemma trip_rcons_decompose {α : Prop} (f : Π Δ Y, Δ ∈ ps.links → trip ps S n X Y → steps (S Δ) Δ Y Z → α) :
    trip ps S n.succ X Z → α :=
  begin
    sorry
  end

  theorem trip_unique_stop : trip ps S n X Y → trip ps S n X Z → Y = Z :=
  begin
    revert Y Z,
    induction n,
    case nat.zero : { intros _ _ tXY tXZ, cases tXY, cases tXZ, refl},
    case nat.succ : n ih {
      rintros Y Z tXY tXZ,
      apply trip_rcons_decompose _ tXY,
      intros Δ V hΔ tXV sVY,
      apply trip_rcons_decompose _ tXZ,
      intros Δ' W hΔ' tXW sWZ,
      have : W = V, apply ih tXW tXV,
      rw this at sWZ,
      have : Δ' = Δ, apply link_unique_of_steps_prev hΔ' hΔ sWZ sVY,
      rw this at sWZ,
      apply steps_unique_next (ps.valid Δ hΔ) sVY sWZ,
      }
  end

end

