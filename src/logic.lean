section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  by_contra,
  have i := h p,
  exact i,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p,
  by_contra,
  have i := p h,
  exact i,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro p,
  by_contra,
  exact p h,
  intro p,
  by_contra,
  exact h p,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p,
  cases p,
  right,
  exact p,
  left,
  exact p,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p,
  cases p with q r,
  split,
  exact r,
  exact q,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros p q,
  cases p,
  by_contra,
  exact p q,
  exact p,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros p q,
  cases p,
  by_contra,
  exact q p,
  exact p,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros p q r,
  have i := p r,
  exact q i,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros p q,
  by_contra,
  have i := p h,
  exact i q,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros p q r,
  have i := p r,
  exact q i,
  intros p q,
  by_contra,
  have i := p h,
  exact i q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro p,
  apply p,
  right,
  by_contra,
  have q : P ∨ ¬P,
  left,
  exact h,
  have i := p q,
  exact i,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros p q,
  have r : P,
  apply p,
  intro s,
  exfalso,
  exact q s,
  exact q r,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros p q,
  cases q with r s,
  cases p,
  exact r p,
  exact s p,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros p q,
  cases p with r s,
  cases q with t u,
  exact t r,
  exact u s,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_ndisj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro p,
  split,
  by_contra,
  have q : P ∨ Q,
  left,
  exact h,
  exact p q,
  by_contra,
  have q : P ∨ Q,
  right,
  exact h,
  exact p q,
end

theorem demorgan_ndisj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros p q,
  cases p with r s,
  cases q with j k,
  exact r j,
  exact s k,
end

theorem demorgan_nconj_converse :
   (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros p q,
  cases p with r s,
  cases q with j k,
  exact r k,
  cases q with x z,
  exact s x,
end


------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p,
  cases p with q r,
  cases r with s t,
  left,
  split,
  exact q,
  exact s,
  right,
  split,
  exact q,
  exact t,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro p,
  cases p with q r,
  split,
  cases q with s t,
  exact s,
  cases q with u v,
  left,
  exact v,
  cases r with w x,
  split,
  exact w,
  right,
  exact x,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p,
  split,
  cases p with q r s,
  left,
  exact q,
  cases r with t u,
  right,
  exact t,
  cases p with v w,
  left,
  exact v,
  cases w with x y,
  right,
  exact y,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro p,
  cases p with q r,
  cases q,
  left,
  exact q,
  cases r,
  left,
  exact r,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros p q r,
  apply p,
  split,
  exact q,
  exact r,
end
theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros p q,
  apply p,
  cases q with r s,
  exact r,
  cases q with r s,
  exact s,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro p,
  right,
  exact p,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p,
  cases p with q r,
  exact q,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p,
  cases p with q r,
  exact r,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p,
  cases p with q r,
  exact q,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idemp :
  (P∨P) ↔ P  :=
begin
  split,
  intro p,
  cases p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros p,
  cases p with q r,
  intro s,
  have i := s q,
  exact r i,
end

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros p q r,
  apply p,
  existsi q,
  exact r,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros p q,
  cases q with r s,
  have i := p r,
  exact i s,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro p,
  by_contra r,
  apply p,
  intro q,
  by_contra,
  apply r,
  existsi q,
  exact h,
end  
  
theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end

------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros p q,
  cases p with r s,
  have i := q r,
  exact i s,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros p q,
  cases q with r s,
  have i := p r,
  exact s i,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros p q,
  by_contra,
  apply p,
  existsi q,
  exact h,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro p,
  by_contra,
  apply p,
  intros q r,
  apply h,
  existsi q,
  exact r,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro p,
  cases p with q r,
  cases r with s t,
  split,
  existsi q,
  exact s,
  existsi q,
  exact t,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro p,
  cases p with q r,
  cases r with s t,
  left,
  existsi q,
  exact s,
  right,
  existsi q,
  exact t,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro p,
  cases p with q r,
  cases q with s t,
  existsi s,
  left,
  exact t,
  cases r with s t,
  existsi s,
  right,
  exact t,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro p,
  split,
  intro q,
  by_contra,
  have i := p q,
  cases i with j k,
  exact h j,
  intro s,
  have i := p s,
  cases i with j k,
  by_contra,
  exact h k,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros p q,
  split,
  cases p with r s,
  have i := r q,
  by_contra,
  exact h i,
  cases p with r s,
  by_contra,
  have i := s q,
  exact h i,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros p q,
  cases p with r s,
  have i := r q,
  left,
  by_contra,
  exact h i,
  have i := s q,
  right,
  by_contra,
  exact h i,
end


/--NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
  intro p,
  right,
  intro q,
  have i := p q,
  cases i,
  --teorema inválido
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
  intro p,
  cases p with q r,
  cases q with s t,
  cases r with u v,
  existsi u,
  split,
  --teorema inválido
end

---------------------------------------------- -/

end predicate
