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

def Form_occ := Form × ℕ

inductive premise : Form_occ → Link → Prop
| cut_pos {A i j}          : premise (A,i) (Link.cut i j A)
| cut_neg {A i j}          : premise (~A,j) (Link.cut i j A)
| tensor_left {A B i j k}  : premise (A,i) (Link.tensor i j k A B)
| tensor_right {A B i j k} : premise (B,j) (Link.tensor i j k A B)
| par_left {A B i j k}     : premise (A,i) (Link.par i j k A B)
| par_right {A B i j k}    : premise (B,j) (Link.par i j k A B)

inductive conclusion : Form_occ → Link → Prop
| ax_pos {A i j}     : conclusion (A,i) (Link.ax i j A)
| ax_neg {A i j}     : conclusion (~A,j) (Link.ax i j A)
| tensor {A B i j k} : conclusion (A ⊗ B,k) (Link.tensor i j k A B)
| par {A B i j k}    : conclusion (A ⅋ B,k) (Link.par i j k A B)

inductive mem_Link (Ai : Form_occ) (l : Link) : Prop
| prem : premise Ai l → mem_Link
| con : conclusion Ai l → mem_Link

instance : has_mem Form_occ Link := ⟨mem_Link⟩

inductive valid_link : Link → Prop
| ax  {i j A} : valid_link (Link.ax i j A)
| cut {i j A} : valid_link (Link.cut i j A)
| tensor {i j k A B} : (A,i) ≠ (B,j) → valid_link (Link.tensor i j k A B)
| par {i j k A B} : (A,i) ≠ (B,j) → valid_link (Link.par i j k A B)

structure proof_structure : Type :=
(links : set Link)
(valid : ∀ l ∈ links, valid_link l)
(prem_unique : ∀ Ai : Form_occ, ∀ l₁ l₂ ∈ links, premise Ai l₁ → premise Ai l₂ → l₁ = l₂)
(con_unique : ∀ Ai : Form_occ, ∀ l₁ l₂ ∈ links, conclusion Ai l₁ → conclusion Ai l₂ → l₁ = l₂)

inductive mem_Form_occ_ps (Ai : Form_occ) (ps : proof_structure) : Prop
| mk {l} : l ∈ ps.links → Ai ∈ l → mem_Form_occ_ps

instance : has_mem Form_occ proof_structure := ⟨mem_Form_occ_ps⟩

def sequent := list Form

instance : has_append sequent := ⟨list.append⟩
instance : has_mem Form sequent := ⟨list.mem⟩

inductive proof : sequent → Type
| ax (A)                   : proof [~A, A]
| cut (A) {Γ Γ' Δ Δ'}      : proof (Γ ++ [A] ++ Γ') → proof (Δ ++ [~A] ++ Δ') → proof (Γ++Γ'++Δ++Δ')
| tensor {A B} {Γ Γ' Δ Δ'} : proof (Γ ++ [A] ++ Γ') → proof (Δ ++ [B] ++ Δ') → proof (Γ++Γ'++ [A ⊗ B] ++Δ++Δ') 
| par {A B} {Γ Γ'}         : proof (Γ ++ [A,B] ++ Γ') → proof (Γ ++ [A ⅋ B] ++ Γ')
| ex {A B} {Γ Γ'}          : proof (Γ ++ [A,B] ++ Γ') → proof (Γ ++ [B,A] ++ Γ')

inductive proof_net : sequent → Type
| mk {Γ : sequent} (ps : proof_structure) : (∀ A ∈ Γ, ∃ i, ∃ Δ ∈ ps.links, conclusion (A,i) Δ ∧ ∀ Δ' ∈ ps.links, ¬premise (A,i) Δ') → proof_net Γ

instance {Γ : sequent} : has_coe (proof_net Γ) proof_structure := ⟨by rintro ⟨Γ,ps,_⟩; exact ps⟩

def relabel_Link (f : ℕ → ℕ) : Link → Link
| (Link.ax pi ni A) := Link.ax (f pi) (f ni) A
| (Link.cut pi ni A) := Link.cut (f pi) (f ni) A
| (Link.tensor ai bi ci A B) := Link.tensor (f ai) (f bi) (f ci) A B
| (Link.par ai bi ci A B) := Link.par (f ai) (f bi) (f ci) A B

def proof_structure.relabel (ps : proof_structure) (f : ℕ → ℕ) (hf : function.injective f) : proof_structure :=
⟨set.image (relabel_Link f) ps.links, sorry, sorry, sorry⟩

def separators {α β} (f g : α → β) : Prop := ∀ x y, f x ≠ g y

lemma sep_even_odd : separators (λ x, 2 * x) (λ x, 2 * x + 1) :=
  λ x y, nat.two_mul_ne_two_mul_add_one

def disjoint_of_separators {ps₁ ps₂ : proof_structure} {f g} (hf hg) : separators f g → disjoint { Ai | Ai ∈ (ps₁.relabel f hf) } { Ai | Ai ∈ (ps₂.relabel g hg) } :=
 by sorry

def proof_net.disjoint {Γ Δ} : proof_net Γ → proof_net Δ → Prop :=
  by rintro ⟨_,ps₁,_⟩ ⟨_,ps₂,_⟩; exact disjoint {Ai | Ai ∈ ps₁} {Ai | Ai ∈ ps₂}

def net_links_ax (pi ni A) : set Link :=
  {Link.ax pi ni A}

def net_links_tensor (ai bi ci A B) (sA sB : set Link) : set Link :=
  {Link.tensor ai bi ci A B} ∪ sA ∪ sB

def net_links_par (ai bi ci A B) (s : set Link) : set Link :=
  {Link.par ai bi ci A B} ∪ s

def net_links_cut (pi ni A) (sA snA : set Link) : set Link :=
  {Link.cut pi ni A} ∪ sA ∪ snA

def proof_net_ax (A) : proof_net [~A,A] :=
⟨
  ⟨{Link.ax 0 0 A},
  by rintro l ⟨h⟩; exact valid_link.ax,
  by rintro Ai Δ₁ Δ₂ ⟨_⟩ ⟨_⟩; finish,
  by rintro Ai Δ₁ Δ₂ ⟨_⟩ ⟨_⟩; finish ⟩
,
  begin
    rintro B ⟨⟨_⟩⟩,
      refine ⟨0,Link.ax 0 0 A,by simp,conclusion.ax_neg,_⟩, rintro Δ' ⟨_⟩ ⟨_⟩,
    rcases H with ⟨⟨_⟩⟩,
      refine ⟨0,Link.ax 0 0 A,by simp,conclusion.ax_pos,_⟩, rintro Δ' ⟨_⟩ ⟨_⟩,
    cases H,
  end
⟩

def proof_net_tensor {Γ Γ' A B Δ Δ'} (pnA : proof_net (Γ ++ [A] ++ Γ')) (pnB : proof_net (Δ ++ [B] ++ Δ')) :
  pnA.disjoint pnB → proof_net (Γ ++ Γ' ++ [A ⊗ B] ++ Δ ++ Δ') :=
begin
  rcases pnA with ⟨_,psA, hA⟩,
  rcases pnB with ⟨_,psB, hB⟩,
  intro dAB,
  specialize hA A (by exact list.mem_append_left _ (list.mem_append_right _ (list.mem_cons_self A list.nil))),
  specialize hB B (by exact list.mem_append_left _ (list.mem_append_right _ (list.mem_cons_self B list.nil))),
  cases hA with ai ΔA hA,
  
end