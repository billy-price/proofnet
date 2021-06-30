import mll2

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
| mk {Γ : sequent} (ps : proof_structure) : (Π A ∈ Γ, { i : ℕ // (A,i) ∈ ps ∧ ∀ Δ ∈ ps.links, ¬premise (A,i) Δ }) → proof_net Γ

instance {Γ : sequent} : has_coe (proof_net Γ) proof_structure := ⟨by rintro ⟨Γ,ps,_⟩; exact ps⟩

def relabel_Link (f : ℕ → ℕ) : Link → Link
| (Link.ax pi ni A) := Link.ax (f pi) (f ni) A
| (Link.cut pi ni A) := Link.cut (f pi) (f ni) A
| (Link.tensor ai bi ci A B) := Link.tensor (f ai) (f bi) (f ci) A B
| (Link.par ai bi ci A B) := Link.par (f ai) (f bi) (f ci) A B

lemma relabel_valid {l f} (hf : function.injective f): valid_link l → valid_link (relabel_Link f l) :=
begin
  cases l,
  case Link.ax : pi ni A { rintro ⟨_⟩, constructor, },
  case Link.cut : pi ni A { rintro ⟨_⟩, constructor, },
  case Link.tensor : ai bi ci A B {
    rintro ⟨_⟩, constructor, rintro e, injection e with e₁ e₂, apply ᾰ_ᾰ, congr, assumption, exact hf e₂, },
  case Link.par : ai bi ci A B {
    rintro ⟨_⟩, constructor, rintro e, injection e with e₁ e₂, apply ᾰ_ᾰ, congr, assumption, exact hf e₂, },
end

lemma relabel_injective {f} (hf : function.injective f) : function.injective (relabel_Link f) :=
by rintros ⟨l₁⟩ ⟨l₂⟩; intros h; injection h; congr; repeat {refl <|> assumption <|> apply hf}

lemma relabel_premise {l f D i } (hf : function.injective f) : premise (D,i) (relabel_Link f l) → ∃ j, f j = i ∧ premise (D,j) l :=
begin
  cases l,
  case Link.ax : pi ni A { rintro ⟨_⟩ },
  case Link.cut : pi ni A { rintro ⟨_⟩, exact ⟨pi,rfl,premise.cut_pos⟩, exact ⟨ni,rfl,premise.cut_neg⟩, },
  case Link.tensor : ai bi ci A B {
    rintro ⟨_⟩, exact ⟨ai,rfl,premise.tensor_left⟩, exact ⟨bi,rfl,premise.tensor_right⟩, },
  case Link.par : ai bi ci A B {
    rintro ⟨_⟩, exact ⟨ai,rfl,premise.par_left⟩, exact ⟨bi,rfl,premise.par_right⟩, },
end

lemma relabel_conclusion {l f D i } (hf : function.injective f) : conclusion (D,i) (relabel_Link f l) → ∃j, f j = i ∧ conclusion (D,j) l :=
begin
  cases l,
  case Link.ax : pi ni A {
    rintro ⟨_⟩, exact ⟨pi,rfl,conclusion.ax_pos⟩, exact ⟨ni,rfl,conclusion.ax_neg⟩, },
  case Link.cut : pi ni A { rintro ⟨_⟩ },
  case Link.tensor : ai bi ci A B { rintro ⟨_⟩, exact ⟨ci,rfl,conclusion.tensor⟩ },
  case Link.par : ai bi ci A B { rintro ⟨_⟩, exact ⟨ci,rfl,conclusion.par⟩ },
end

lemma relabel_mem {Δ f A i} (hf : function.injective f) : (A,i) ∈ (relabel_Link f Δ) → ∃ j, f j = i ∧ (A,j) ∈ Δ :=
begin
  intro h, cases h with h h,
  rcases (relabel_premise hf h) with ⟨j, ⟨fji,pΔ⟩⟩, refine ⟨j,fji,mem_Link.prem pΔ⟩,
  rcases (relabel_conclusion hf h) with ⟨j, ⟨fji,pΔ⟩⟩, refine ⟨j,fji,mem_Link.con pΔ⟩,
end


def proof_structure.relabel (ps : proof_structure) (f : ℕ → ℕ) (hf : function.injective f) : proof_structure :=
⟨set.image (relabel_Link f) ps.links,
  by rintros l ⟨l', ⟨hl',⟨_⟩⟩⟩; exact relabel_valid hf (ps.valid l' hl'),
begin
  rintros ⟨A,i⟩ _ _ ⟨k₁, ⟨hk₁,⟨_⟩⟩⟩ ⟨k₂, ⟨hk₂,⟨_⟩⟩⟩,
  intros pk₁ pk₂,
  congr, 
  rcases relabel_premise hf pk₁ with ⟨j,hfj,u₁⟩,
  rcases relabel_premise hf pk₂ with ⟨j',hfj',u₂⟩,
  have : j' = j, rw ←hfj at hfj', exact hf hfj', rw this at u₂,  
  exact ps.prem_unique (A,j) _ _ hk₁ hk₂ u₁ u₂
end
,
begin
  rintros ⟨A,i⟩ _ _ ⟨k₁, ⟨hk₁,⟨_⟩⟩⟩ ⟨k₂, ⟨hk₂,⟨_⟩⟩⟩,
  intros pk₁ pk₂,
  congr, 
  rcases relabel_conclusion hf pk₁ with ⟨j,hfj,u₁⟩,
  rcases relabel_conclusion hf pk₂ with ⟨j',hfj',u₂⟩,
  have : j' = j, rw ←hfj at hfj', exact hf hfj', rw this at u₂,  
  exact ps.con_unique (A,j) _ _ hk₁ hk₂ u₁ u₂
end⟩

def separators {α β} (f g : α → β) : Prop := ∀ x y, f x ≠ g y

lemma sep_even_odd : separators (λ x, 2 * x) (λ x, 2 * x + 1) :=
  λ x y, nat.two_mul_ne_two_mul_add_one

def disjoint_of_separators {ps₁ ps₂ : proof_structure} {f g} (hf hg) : separators f g → disjoint { Ai | Ai ∈ (ps₁.relabel f hf) } { Ai | Ai ∈ (ps₂.relabel g hg) } :=
begin
  rintros s ⟨A,i⟩ ⟨⟨Δ₁,⟨Δ₁', hΔ₁', ⟨_⟩⟩,h₁⟩,⟨Δ₂,⟨Δ₂', hΔ₂', ⟨_⟩⟩,h₂⟩⟩,
  rcases (relabel_mem hf h₁) with ⟨j₁,hfg,h₁⟩,
  rcases (relabel_mem hg h₂) with ⟨j₂,⟨_⟩,h₂⟩,
  exact s j₁ j₂ hfg,
end

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
    rintro B Bmem,
    refine ⟨0,_,_⟩, rcases Bmem with ⟨_,_⟩, use Link.ax 0 0 A, simp, exact mem_Link.con conclusion.ax_neg,
      
      -- exact ⟨0,Link.ax 0 0 A,by simp,conclusion.ax_neg,_⟩, rintro Δ' ⟨_⟩ ⟨_⟩,
    rcases H with ⟨⟨_⟩⟩,
      exact ⟨0,Link.ax 0 0 A,by simp,conclusion.ax_pos,_⟩, rintro Δ' ⟨_⟩ ⟨_⟩,
    cases H,
  end
⟩

def proof_net_tensor {Γ Γ' A B Δ Δ'} (pnA : proof_net (Γ ++ [A] ++ Γ')) (pnB : proof_net (Δ ++ [B] ++ Δ')) : pnA.disjoint pnB → proof_net (Γ ++ Γ' ++ [A ⊗ B] ++ Δ ++ Δ') :=
begin
  rcases pnA with ⟨_,psA, hA⟩,
  rcases pnB with ⟨_,psB, hB⟩,
  intro dAB,
  specialize hA A (by refine list.mem_append_left _ (list.mem_append_right _ (list.mem_cons_self A list.nil))),
  specialize hB B,
  cases hA with ai ΔA hA,
  
end