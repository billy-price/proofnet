import mll

def sequent := list Form

instance : has_append sequent := ⟨list.append⟩
instance : has_mem Form sequent := ⟨list.mem⟩

inductive proof : sequent → Type
| ax (A)                   : proof [~A, A]
| cut (A) {Γ Γ' Δ Δ'}      : proof (Γ ++ [A] ++ Γ') → proof (Δ ++ [~A] ++ Δ') → proof (Γ++Γ'++Δ++Δ')
| tensor {A B} {Γ Γ' Δ Δ'} : proof (Γ ++ [A] ++ Γ') → proof (Δ ++ [B] ++ Δ') → proof (Γ++Γ'++ [A ⊗ B] ++Δ++Δ') 
| par {A B} {Γ Γ'}         : proof (Γ ++ [A,B] ++ Γ') → proof (Γ ++ [A ⅋ B] ++ Γ')
| ex {A B} {Γ Γ'}          : proof (Γ ++ [A,B] ++ Γ') → proof (Γ ++ [B,A] ++ Γ')

def ps_ax (A : Form) (pi ni : ℕ) : proof_structure :=
⟨ {Link.ax pi ni A, Link.con pi A, Link.con ni (~A)},
  begin rintros _ ⟨_|_⟩, constructor, cases H with H H, rw H, constructor, cases H, constructor end,
  begin rintro Ai l₁ l₂ ⟨_,_⟩ ⟨_,_⟩, finish, rintro ⟨_⟩, rintro _ ⟨_⟩,
    rcases H with ⟨_,_⟩;rcases H_1 with ⟨_,_⟩, finish, rcases H_1 with ⟨_,_⟩, intro pA, generalize e : A = A', cases pA,
    rintro ⟨_⟩, congr, exact e.symm, cases H, intro pnA, generalize e : A = A', cases pnA, rintro ⟨_⟩, exfalso, exact not_self_dual e.symm,
    cases H, cases H_1, finish,  end,
  begin rintros Ai l₁ l₂ ⟨_,_⟩ ⟨_,_⟩, finish, rcases H_1 with ⟨_,_⟩, rintro _ ⟨_⟩, cases H_1, rintro _ ⟨_⟩,
    rcases H with ⟨_,_⟩, rintro ⟨_⟩, rcases H with ⟨_⟩, rintro ⟨_⟩,
    rcases H with ⟨_,_⟩; rcases H_1 with ⟨_,_⟩, finish, rintro ⟨_⟩, rintro _ ⟨_⟩, cases H, cases H_1, finish,
  end ⟩

lemma ps_ax_conclusions {A pi ni} : Link.con pi A ∈ (ps_ax A pi ni).links ∧ Link.con ni (~A) ∈ (ps_ax A pi ni).links :=
  ⟨set.mem_union_right _ (set.mem_union_left _ rfl), set.mem_union_right _ (set.mem_union_right _ rfl)⟩ 


def ps.disjoint (ps₁ ps₂ : proof_structure) : Prop := ∀ Ai : Form_occ, (Ai ∈ ps₁ ∧ Ai ∈ ps₂) → false

def ps_tensor (A B) (ai bi ci : ℕ) (psA psB : proof_structure) :
  ps.disjoint psA psB →
  Link.con ai A ∈ psA.links →
  Link.con bi B ∈ psB.links →
  (A ⊗ B, ci) ∉ psA →
  (A ⊗ B, ci) ∉ psB →
  proof_structure :=
λ dAB conA conB hcA hcB,
⟨{Link.tensor ai bi ci A B} ∪ (psA.links \ {Link.con ai A}) ∪ (psB.links \ {Link.con bi B}),
begin
  rintros l ⟨⟨_,_⟩|⟨h₁,_⟩⟩,
    apply valid_link.tensor,
  rintros ⟨_⟩,
  exact dAB (A,ai) ⟨⟨conA,mem_Link.prem premise.con⟩,⟨conB,mem_Link.prem premise.con⟩⟩,
  exact psA.valid l h₁,
  cases H with h₂, exact psB.valid l h₂
end,
begin
  rintros Ai l₁ l₂ ⟨⟨u₁,u₂⟩|⟨u₁,u₂⟩⟩ ⟨⟨h₁,h₂⟩|⟨h₁,h₂⟩⟩,
    { finish },
    { rintros ⟨_|_⟩ h₃,
        exfalso, apply h₂, simp, apply psA.prem_unique _ _ _ h₁ conA h₃ premise.con,
        exfalso, refine dAB (B,bi) ⟨⟨h₁,mem_Link.prem h₃⟩,⟨conB,mem_Link.prem premise.con⟩⟩, },
    { rcases H_1 with ⟨h₁,h₂⟩, rintros ⟨_|_⟩ h₃,
        exfalso, refine dAB (A,ai) ⟨⟨conA,mem_Link.prem premise.con⟩,⟨h₁,mem_Link.prem h₃⟩⟩,
        simp at h₂, exfalso, apply h₂, apply psB.prem_unique _ _ _ h₁ conB h₃, constructor },
    { rintros h₃ ⟨_|_⟩,
        simp at u₂, exfalso, apply u₂, apply psA.prem_unique _ _ _ u₁ conA h₃, constructor,
        exfalso, refine dAB (B,bi) ⟨⟨u₁,mem_Link.prem h₃⟩,⟨conB,mem_Link.prem premise.con⟩⟩, },
    { intros pl₁ pl₂, apply psA.prem_unique Ai _ _ u₁ h₁ pl₁ pl₂, },
    { intros pl₁ pl₂, cases H_1 with h₁ h₂, exfalso, exact dAB Ai ⟨⟨u₁,mem_Link.prem pl₁⟩,⟨h₁,mem_Link.prem pl₂⟩⟩, },
    { cases H with h₁ h₂,
      rintros h₃ ⟨_|_⟩,
        exfalso, refine dAB (A,ai) ⟨⟨conA,mem_Link.prem premise.con⟩,⟨h₁,mem_Link.prem h₃⟩⟩,
        exfalso, apply h₂, simp, apply psB.prem_unique _ _ _ h₁ conB h₃ premise.con, },
    { intros pl₁ pl₂, cases H with u₁ u₂, exfalso, exact dAB Ai ⟨⟨h₁,mem_Link.prem pl₂⟩,⟨u₁,mem_Link.prem pl₁⟩⟩, },
    { cases H with h₁ h₂, cases H_1 with u₁ u₂, intros pl₁ pl₂, apply psB.prem_unique Ai _ _ h₁ u₁ pl₁ pl₂, },
end,
begin
  rintros Ai l₁ l₂ ⟨⟨u₁,u₂⟩|⟨u₁,u₂⟩⟩ ⟨⟨h₁,h₂⟩|⟨h₁,h₂⟩⟩,
    { finish },
    { rintros ⟨_|_⟩ h₃, exfalso, apply hcA ⟨h₁, mem_Link.con h₃⟩, },
    { rcases H_1 with ⟨h₁,h₂⟩, rintros ⟨_|_⟩ h₃, exfalso, apply hcB ⟨h₁, mem_Link.con h₃⟩ },
    { rintros h₃ ⟨_|_⟩, exfalso, apply hcA ⟨u₁, mem_Link.con h₃⟩, },
    { intros pl₁ pl₂, apply psA.con_unique Ai _ _ u₁ h₁ pl₁ pl₂, },
    { intros pl₁ pl₂, cases H_1 with h₁ h₂, exfalso, exact dAB Ai ⟨⟨u₁,mem_Link.con pl₁⟩,⟨h₁,mem_Link.con pl₂⟩⟩, },
    { cases H with h₁ h₂, rintros h₃ ⟨_|_⟩, exfalso, apply hcB ⟨h₁, mem_Link.con h₃⟩, },
    { intros pl₁ pl₂, cases H with u₁ u₂, exfalso, exact dAB Ai ⟨⟨h₁,mem_Link.con pl₂⟩,⟨u₁,mem_Link.con pl₁⟩⟩, },
    { cases H with h₁ h₂, cases H_1 with u₁ u₂, intros pl₁ pl₂, apply psB.con_unique Ai _ _ h₁ u₁ pl₁ pl₂, },
end
⟩

lemma ps_tensor_conclusions {A B ai bi ci psA psB dAB conA conB hcA hcB} :
  Link.tensor ai bi ci A B ∈ (ps_tensor A B ai bi ci psA psB dAB conA conB hcA hcB).links :=
  set.mem_union_left _ (set.mem_union_left _ rfl)

def ps_cut (A : Form) (pi ni : ℕ) (psA psnA : proof_structure) :
  ps.disjoint psA psnA →
  Link.con pi A ∈ psA.links →
  Link.con ni (~A) ∈ psnA.links →
  proof_structure :=
λ dAnA conA connA,
⟨{Link.cut pi ni A} ∪ (psA.links \ {Link.con pi A}) ∪ (psnA.links \ {Link.con ni (~A)}),
begin
  rintros l ⟨⟨_,_⟩|⟨h₁,_⟩⟩,
    apply valid_link.cut,
  exact psA.valid l h₁,
  cases H with h₂, exact psnA.valid l h₂
end,
begin
  rintros Ai l₁ l₂ ⟨⟨u₁,u₂⟩|⟨u₁,u₂⟩⟩ ⟨⟨h₁,h₂⟩|⟨h₁,h₂⟩⟩,
    { finish },
    { rintros ⟨_⟩ h₃,
        exfalso, apply h₂, simp, apply psA.prem_unique _ _ _ h₁ conA h₃ premise.con,
        exfalso, refine dAnA (~A,ni) ⟨⟨h₁,mem_Link.prem h₃⟩,⟨connA,mem_Link.prem premise.con⟩⟩, },
    { rcases H_1 with ⟨h₁,h₂⟩, rintros ⟨_⟩ h₃,
        exfalso, refine dAnA (A,pi) ⟨⟨conA,mem_Link.prem premise.con⟩,⟨h₁,mem_Link.prem h₃⟩⟩,
        simp at h₂, exfalso, apply h₂, apply psnA.prem_unique _ _ _ h₁ connA h₃, constructor },
    { rintros h₃ ⟨_⟩,
        simp at u₂, exfalso, apply u₂, apply psA.prem_unique _ _ _ u₁ conA h₃, constructor,
        exfalso, refine dAnA (~A,ni) ⟨⟨u₁,mem_Link.prem h₃⟩,⟨connA,mem_Link.prem premise.con⟩⟩, },
    { intros pl₁ pl₂, apply psA.prem_unique Ai _ _ u₁ h₁ pl₁ pl₂, },
    { intros pl₁ pl₂, cases H_1 with h₁ h₂, exfalso, exact dAnA Ai ⟨⟨u₁,mem_Link.prem pl₁⟩,⟨h₁,mem_Link.prem pl₂⟩⟩, },
    { cases H with h₁ h₂,
      rintros h₃ ⟨_⟩,
        exfalso, refine dAnA (A,pi) ⟨⟨conA,mem_Link.prem premise.con⟩,⟨h₁,mem_Link.prem h₃⟩⟩,
        exfalso, apply h₂, simp, apply psnA.prem_unique _ _ _ h₁ connA h₃ premise.con, },
    { intros pl₁ pl₂, cases H with u₁ u₂, exfalso, exact dAnA Ai ⟨⟨h₁,mem_Link.prem pl₂⟩,⟨u₁,mem_Link.prem pl₁⟩⟩, },
    { cases H with h₁ h₂, cases H_1 with u₁ u₂, intros pl₁ pl₂, apply psnA.prem_unique Ai _ _ h₁ u₁ pl₁ pl₂, },
end,
begin
  rintros Ai l₁ l₂ ⟨⟨u₁,u₂⟩|⟨u₁,u₂⟩⟩ ⟨⟨h₁,h₂⟩|⟨h₁,h₂⟩⟩,
    { finish },
    { rintros ⟨_⟩ },
    { rintros ⟨_⟩ },
    { rintros _ ⟨_⟩ },
    { intros pl₁ pl₂, apply psA.con_unique Ai _ _ u₁ h₁ pl₁ pl₂, },
    { intros pl₁ pl₂, cases H_1 with h₁ h₂, exfalso, exact dAnA Ai ⟨⟨u₁,mem_Link.con pl₁⟩,⟨h₁,mem_Link.con pl₂⟩⟩, },
    { rintros _ ⟨_⟩, },
    { intros pl₁ pl₂, cases H with u₁ u₂, exfalso, exact dAnA Ai ⟨⟨h₁,mem_Link.con pl₂⟩,⟨u₁,mem_Link.con pl₁⟩⟩, },
    { cases H with h₁ h₂, cases H_1 with u₁ u₂, intros pl₁ pl₂, apply psnA.con_unique Ai _ _ h₁ u₁ pl₁ pl₂, },
end
⟩

def ps_par (A B) (ai bi ci : ℕ) (ps : proof_structure) :
  (A,ai) ≠ (B,bi) →
  Link.con ai A ∈ ps.links →
  Link.con bi B ∈ ps.links →
  (A ⅋ B, ci) ∉ ps →
  proof_structure :=
λ nAB conA conB hcA,
⟨ {Link.par ai bi ci A B} ∪ (ps.links \ {Link.con ai A, Link.con bi B}),
  begin
    rintros l ⟨⟨_,_⟩|⟨h₁,_⟩⟩,
      apply valid_link.par _ _ _ _ _ nAB,
    cases H with h₂, exact ps.valid l h₂
  end
  ,
  begin
    rintros Ai l₁ l₂ ⟨_|_⟩ ⟨_|_⟩,
      { finish },
      { rintros ⟨_,_⟩ h₃,
        exfalso, cases H_1 with h₁ h₂, apply h₂, left, refine ps.prem_unique (A,ai) _ _ h₁ conA h₃ premise.con,
        exfalso, cases H_1 with h₁ h₂, apply h₂, right, refine ps.prem_unique (B,bi) _ _ h₁ conB h₃ premise.con },
      { rintros h₃ ⟨_,_⟩,
        exfalso, cases H with h₁ h₂, apply h₂, left, refine ps.prem_unique (A,ai) _ _ h₁ conA h₃ premise.con,
        exfalso, cases H with h₁ h₂, apply h₂, right, refine ps.prem_unique (B,bi) _ _ h₁ conB h₃ premise.con },
      { intros pl₁ pl₂, cases H with h₁ h₂, cases H_1 with u₁ u₂, exact ps.prem_unique Ai _ _ h₁ u₁ pl₁ pl₂, },
  end
  ,
  begin
    rintros Ai l₁ l₂ ⟨_|_⟩ ⟨_|_⟩,
      { finish },
      { rintros ⟨_,_⟩ h₃, exfalso, cases H_1 with h₁ h₂, refine hcA ⟨h₁,mem_Link.con h₃⟩, },
      { rintros h₃ ⟨_,_⟩,
        exfalso, cases H with h₁ h₂, refine hcA ⟨h₁,mem_Link.con h₃⟩, },
      { intros pl₁ pl₂, cases H with h₁ h₂, cases H_1 with u₁ u₂, exact ps.con_unique Ai _ _ h₁ u₁ pl₁ pl₂, },
  end
⟩

inductive ps_conclusion (A : Form) (ai : ℕ) (ps : proof_structure) : Prop
| notprem : (∀ l ∈ ps.links, ¬ premise (A,ai) l) → ps_conclusion
| con : Link.con ai A ∈ ps.links → ps_conclusion

def proof_structure.open (ps : proof_structure) (Γ : sequent) : Prop := ∀ A ∈ Γ, ∃ i : ℕ, ps_conclusion A i ps

def relabel_Link (f : ℕ → ℕ) : Link → Link
| (Link.ax pi ni A) := Link.ax (f pi) (f ni) A
| (Link.cut pi ni A) := Link.cut (f pi) (f ni) A
| (Link.tensor ai bi ci A B) := Link.tensor (f ai) (f bi) (f ci) A B
| (Link.par ai bi ci A B) := Link.par (f ai) (f bi) (f ci) A B
| (Link.con ai A) := Link.con (f ai) A

lemma relabel_valid {l f} (hf : function.injective f): valid_link l → valid_link (relabel_Link f l) :=
begin
  cases l,
  case Link.ax : pi ni A { rintro ⟨_⟩, constructor, },
  case Link.cut : pi ni A { rintro ⟨_⟩, constructor, },
  case Link.tensor : ai bi ci A B {
    rintro ⟨_⟩, constructor, rintro e, injection e with e₁ e₂, apply ᾰ_ᾰ, congr, assumption, exact hf e₂, },
  case Link.par : ai bi ci A B {
    rintro ⟨_⟩, constructor, rintro e, injection e with e₁ e₂, apply ᾰ_ᾰ, congr, assumption, exact hf e₂, },
  case Link.con : ai A { rintro _, constructor, }
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
  case Link.con : ai A { rintro ⟨_⟩, refine ⟨ai,rfl,premise.con⟩, }
end

lemma relabel_conclusion {l f D i } (hf : function.injective f) : conclusion (D,i) (relabel_Link f l) → ∃j, f j = i ∧ conclusion (D,j) l :=
begin
  cases l,
  case Link.ax : pi ni A {
    rintro ⟨_⟩, exact ⟨pi,rfl,conclusion.ax_pos⟩, exact ⟨ni,rfl,conclusion.ax_neg⟩, },
  case Link.cut : pi ni A { rintro ⟨_⟩ },
  case Link.tensor : ai bi ci A B { rintro ⟨_⟩, exact ⟨ci,rfl,conclusion.tensor⟩ },
  case Link.par : ai bi ci A B { rintro ⟨_⟩, exact ⟨ci,rfl,conclusion.par⟩ },
  case Link.con : ai A { rintro ⟨_⟩ }
end

def relabel (ps : proof_structure) (f : ℕ → ℕ) (hf : function.injective f) : proof_structure :=
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

def net : Π Γ, proof Γ → ∃ ps : proof_structure, ps.open Γ :=
begin
  intros Γ π,
  induction π,
  case proof.ax : A { use ps_ax A 0 0; rintros B ⟨_,H⟩; use 0,
    right, exact set.mem_union_right _ (set.mem_union_right _ rfl),
    rcases H with ⟨_,_⟩, right, exact set.mem_union_right _ (set.mem_union_left _ rfl), cases H, },
  case proof.cut : A Γ Γ' Δ Δ' pA nA ihA ihnA { 
    rcases ihA with ⟨psA,oA⟩,
    rcases ihnA with ⟨psnA,onA⟩,
    have h₁ := oA A (list.mem_append.mpr $ or.inl $ list.mem_append.mpr $ or.inr $ list.mem_cons_self A _ ),
    have h₂ := onA (~A) (list.mem_append.mpr $ or.inl $ list.mem_append.mpr $ or.inr $ list.mem_cons_self (~A) _ ),
    cases h₁ with pi h₁,
    cases h₂ with ni h₂,
    constructor, swap,
    apply ps_cut,
    repeat {sorry},
   },
   repeat {sorry},
end