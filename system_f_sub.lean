import data.list.basic

/- Prelude -/

attribute [simp] nat.succ_le_succ nat.zero_le


lemma {u v} if_distrib {c : Prop} {h : decidable c} {α : Sort u} {t e : α}
  {β : Sort v} (f : α → β) : f (ite c t e) = ite c (f t) (f e) :=
match h with
| (is_true  hc)  := rfl
| (is_false hnc) := rfl
end

lemma nat.succ_lt_succ_iff (n m : ℕ) : n.succ < m.succ ↔ n < m :=
⟨nat.lt_of_succ_lt_succ, nat.succ_lt_succ⟩

theorem nat.sub_lt_sub_right : Π {n m k : ℕ} (h₁ : n < m) (h₂ : k ≤ n), n - k < m - k
| n     m     0     h₁ h₂ := h₁
| (n+1) (m+1) (k+1) h₁ h₂ := by simp; apply nat.sub_lt_sub_right (nat.lt_of_succ_lt_succ h₁) (nat.le_of_succ_le_succ h₂)

theorem nat.le_sub_one_of_lt {a b : ℕ} (h : a < b) : a ≤ b - 1 :=
begin
  cases b,
  { simp [nat.not_lt_zero] at h; contradiction },
  { simp [nat.le_of_succ_le_succ h] }
end

namespace list
universe u
variables {α β : Type u}
@[simp]
lemma nth_map (xs : list α) (f : α → β) (i : ℕ) : (xs.map f).nth i = f <$> xs.nth i :=
begin
  induction xs generalizing i,
  { refl },
  { cases i, { refl },
    apply ih_1 }
end

@[simp]
lemma nth_drop (xs : list α) (i k : ℕ) : (xs.drop k).nth i = xs.nth (i + k) :=
begin
  induction xs generalizing k i,
  { cases k; refl },
  { cases k, { refl },
    simp [nat.add_succ],
    apply ih_1 }
end

lemma nth_take (xs : list α) (i k : ℕ) : (xs.take k).nth i = if i < k then xs.nth i else none :=
begin
  induction xs generalizing k i,
  { simp [list.nth] },
  { cases k, { refl },
    cases i, { refl },
    simp [list.take, ih_1, nat.succ_lt_succ_iff],
    apply if_congr; refl }
end

lemma nth_append (xs ys : list α) (i : ℕ) : (xs ++ ys).nth i =
  if i < length xs then xs.nth i else ys.nth (i - length xs) :=
begin
  induction xs generalizing i,
  case list.nil { refl },
  case list.cons x xs { cases i with i,
    { refl },
    { simp [ih_1, nat.one_add, nat.succ_lt_succ_iff],
      apply if_congr; refl }
  }
end
end list

namespace system_f_sub

/- Recursive types in F<: -/

inductive type
| var (idx : ℕ)
| top
| «fun» (domain body : type)
| abs (bound body : type)
| mu (rec : type)

open type

infixr ` →ₛ `:55 := type.fun
notation `∀0<: ` t `, ` s := abs t s

/- Parallel substitution -/

def rename := ℕ → ℕ
def rename.up (ξ : rename) : rename
| 0     := 0
| (k+1) := ξ k + 1

@[simp]
def type.rename : rename → type → type
| ξ (var x)    := var (ξ x)
| ξ top        := top
| ξ (a →ₛ b)   := a.rename ξ →ₛ b.rename ξ
| ξ (∀0<:a, b) := ∀0<:a.rename ξ, b.rename ξ.up
| ξ (mu a)     := mu (a.rename ξ.up)

def subst := ℕ → type
def subst.up (σ : subst) : subst
| 0     := var 0
| (k+1) := (σ k).rename (+1)

@[simp]
def type.subst : subst → type → type
| σ (var x)    := σ x
| σ top        := top
| σ (a →ₛ b)   := a.subst σ →ₛ b.subst σ
| σ (∀0<:a, b) := ∀0<:a.subst σ, b.subst σ.up
| σ (mu a)     := mu (a.subst σ.up)

def subst.comp (σ' σ : subst) : subst := type.subst σ' ∘ σ

infix ` ∘ₛ `:90 := subst.comp

def lift_idx (k : ℕ) (d := 0) : rename :=
λ i, if i ≥ d then i + k else i

def type.lift (a : type) (k : ℕ) (d := 0) : type :=
a.rename (lift_idx k d)

def instantiate_idx (r : type) (d := 0) : subst :=
λ i, if d < i then var (i-1) else if i = d then r.lift d else var i

def type.instantiate (a b : type) (d := 0) : type :=
a.subst (instantiate_idx b d)

def type.expand (a : type) : type :=
a.instantiate (mu a)

def type.free_range : type → ℕ
| (var d)     := d + 1
| top         := 0
| (a →ₛ b)    := max a.free_range b.free_range
| (∀0<: a, b) := max a.free_range (b.free_range - 1)
| (mu a)      := a.free_range - 1

def type.closed (t : type) := t.free_range = 0

/- The subtyping relation -/

@[reducible] def env := list type

def env.lift : env → ℕ → opt_param ℕ 0 → env
| [] k d := []
| (a::e) k d := a.lift k (d + e.length) :: env.lift e k d

inductive sub : env → type → type → Prop
  notation e ` ⊢ `:40 a ` <: `:40 b:40 := sub e a b
| var_refl (e x) : e ⊢ var x <: var x
| env {e x a b} : list.nth e x = some a → e ⊢ a.lift (x+1) <: b → e ⊢ var x <: b
| top (e a) : e ⊢ a <: top
| «fun» {e a a' b b'} : e ⊢ a' <: a → e ⊢ b <: b' → e ⊢ a →ₛ b <: a' →ₛ b'
| abs {e a a' b b'} : e ⊢ a' <: a → a'::e ⊢ b <: b' → e ⊢ ∀0<:a, b <: ∀0<:a', b'
-- violates the positivity restriction
--| mu {e a a'} : (∀ b b', e ⊢ b <: b' → e ⊢ type.instantiate a b <: type.instantiate a' b') → e ⊢ mu a <: mu a'
| mu_refl (e a) : e ⊢ mu a <: mu a
| expₗ {e a a'} : e ⊢ type.expand a <: a' → e ⊢ mu a <: a'
| expᵣ {e a a'} : e ⊢ a <: type.expand a' → e ⊢ a <: mu a'

notation e ` ⊢ `:40 a:41 ` <: `:40 b:40 := sub e a b
notation a ` <: `:40 b:40 := sub [] a b

lemma sub.refl : Π e a, e ⊢ a <: a
| e (var x)    := sub.var_refl e x
| e top        := sub.top e top
| e (a →ₛ b)   := sub.fun (sub.refl e a) (sub.refl e b)
| e (∀0<:a, b) := sub.abs (sub.refl e a) (sub.refl _ b)
| e (mu a)     := sub.mu_refl e a

/- A macro for translating Lean types into F<: types -/

section
open lean
open lean.parser
open interactive
open interactive.types

open expr (app pi const lam)

reserve notation `⟦ₛ`:1000
def mu_helper := 0
notation `μ ` binder `, ` a:scoped := mu_helper a

private meta def aux : ℕ → ℕ → pexpr → parser pexpr
| d d' (expr.var n) := let n := n - d' in pure ``(var %%(reflect n))
| d d' (const n ls) := pure $ const n ls
| d d' (app (const ``mu_helper _) (lam _ _ _ a)) := do a ← aux (d+1) d' a, pure ``(mu %%a)
| d d' (expr.local_const n m bi t) := pure $ ``(type.lift  %%(expr.local_const n m bi t) %%(reflect d))
-- ``(∀ x <: %%a, %%b)
| d d' (pi _ _ _ (pi _ _ (app (app (app (const `system_f_sub.sub []) _) (expr.var 0)) a) b)) :=
do a ← aux (d+1) (d'+1) a, b ← aux (d+1) (d'+1) b, pure ``(∀0<:%%a, %%b)
| d d' (expr.pi _ _ dom b) :=
if (@unchecked_cast _ expr b).has_var_idx 0 then
     do b ← aux (d+1) d' b, pure ``(∀0<:top, %%b)
   else
     do dom ← aux d d' dom, b ← aux d (d'+1) b, pure ``(%%dom →ₛ %%b)
| d d' e := match e.get_structure_instance_info with
  | some info :=
    do fields ← (info.field_names.zip info.field_values).mmap (λ ⟨n, v⟩,
      do v ← aux d d' v,
         pure ``(⟨%%(const (`system_f_sub.labels ++ n) [] : pexpr), %%v⟩)),
    pure (app (const `system_f_sub.record []) (fields.foldr (λ e f, ``(%%e::%%f)) ``([])))
  | _ := tactic.fail format!"unsupported sub-expression {e.to_raw_fmt}"
  end

@[user_notation]
meta def interpret_notation (_ : parse $ tk "⟦ₛ") (e : parse $ parser.pexpr <* tk "⟧") : parser pexpr :=
aux 0 0 e
end

/- Basic types -/

-- def Bool := ∀0<:top, var 0 →ₛ var 0 →ₛ var 0
def Bool := ⟦ₛ ∀ a, a → a → a ⟧
def True := ⟦ₛ ∀ a, a → top → a ⟧
def False := ⟦ₛ ∀ a, top → a → a ⟧
def None := ⟦ₛ ∀ a, top → top → a ⟧

example : None <: True := by repeat {constructor}
example : None <: False := by repeat {constructor}
example : True <: Bool := by repeat {constructor}
example : False <: Bool := by repeat {constructor}

def prod (a b : type) := ⟦ₛ ∀ r, (a → b → r) → r ⟧
infix ` ×ₛ `:45 := prod

def tuple : list type → type
| []      := top
| (a::as) := a ×ₛ tuple as

structure field :=
(idx : ℕ)
(type : type)

def record_list (fields : list field) : list type :=
let max_idx := (fields.map field.idx).foldr max 0 in
(list.range (max_idx+1)).map (λ i, (field.type <$> fields.find (λ f, f.idx = i)).get_or_else top)

def record (fields : list field) : type :=
tuple (record_list fields ++ [top])

/- Finally, some proofs -/

lemma rename_up_id : rename.up id = id :=
begin
  apply funext, intro i,
  cases i; simp [rename.up]
end

lemma rename_up_comp_rename_up (ξ ξ' : rename) : ξ'.up ∘ ξ.up = rename.up (ξ' ∘ ξ) :=
begin
  apply funext, intro i,
  cases i; simp [function.comp, rename.up]
end

@[simp]
lemma rename_rename (a : type) (ξ ξ') : (a.rename ξ).rename ξ' = a.rename (ξ' ∘ ξ) :=
by induction a generalizing ξ ξ'; simp [*,rename_up_comp_rename_up]

lemma subst_up_comp_rename_up (ξ : rename) (σ : subst) : σ.up ∘ ξ.up = subst.up (σ ∘ ξ) :=
begin
  apply funext, intro i,
  cases i; simp [function.comp, rename.up, subst.up]
end

@[simp]
lemma rename_subst (a : type) (ξ σ) : (a.rename ξ).subst σ = a.subst (σ ∘ ξ) :=
by induction a generalizing ξ σ; simp [*,subst_up_comp_rename_up]

lemma rename_up_comp_subst_up (ξ : rename) (σ : subst) : type.rename ξ.up ∘ σ.up = subst.up (type.rename ξ ∘ σ) :=
begin
  apply funext, intro i,
  cases i with i; simp [function.comp, rename.up, subst.up]
end

@[simp]
lemma subst_rename (a : type) (ξ σ) : (a.subst σ).rename ξ = a.subst (type.rename ξ ∘ σ) :=
by induction a generalizing ξ σ; simp [*,rename_up_comp_subst_up]

lemma subst_up_comp_subst_up (σ σ' : subst) : σ'.up ∘ₛ σ.up = (σ' ∘ₛ σ).up :=
begin
  apply funext, intro i,
  cases i with i; simp [subst.comp, function.comp, subst.up]
end

@[simp]
lemma subst_subst (a : type) (σ σ') : (a.subst σ).subst σ' = a.subst (σ' ∘ₛ σ) :=
begin
  induction a generalizing σ σ'; simp [*,subst_up_comp_subst_up],
  case var { simp [subst.comp, function.comp] }
end

lemma lift_lift {k k' d d'} (a : type) : d ≤ d' → d' ≤ k + d → (a.lift k d).lift k' d' = a.lift (k + k') d :=
begin
  intros, simp [type.lift,rename_rename,function.comp],
  apply congr_fun, apply congr_arg, apply funext, intro i,
  by_cases i ≥ d,
  { simp [ge, h, type.lift, lift_idx, le_trans ‹d' ≤ k + d› (add_le_add_left h _)] },
  { have : ¬d' ≤ i, from λ hcontr, h (le_trans ‹d ≤ d'› hcontr),
    simp [ge, h, type.lift, lift_idx, this] }
end

@[simp]
lemma lift_lift' (k k') (a : type) : (a.lift k).lift k' = a.lift (k + k') :=
lift_lift _ dec_trivial dec_trivial

lemma lift_lift2 (k k' d d') (a : type) : k + d ≤ d' → (a.lift k d).lift k' d' = (a.lift k' (d' - k)).lift k d :=
begin
  intros, simp [type.lift,rename_rename,function.comp],
  apply congr_fun, apply congr_arg, apply funext, intro i,
  have : k ≤ d', from le_trans (nat.le_add_right _ _) ‹k + d ≤ d'›,
  by_cases i ≥ d,
  { by_cases d' ≤ k + i with h',
    { have : d' - k ≤ k + i - k, from nat.sub_le_sub_right h' k,
      simp [nat.add_sub_cancel_left] at this,
      simp [ge, h, type.lift, lift_idx, h', this, le_add_of_nonneg_of_le (nat.zero_le _) h] },
    { have : ¬ d' - k ≤ i, begin
        assume hcontr, apply h',
        have : d' - k + k ≤ i + k, from nat.add_le_add_right hcontr k,
        simp [nat.sub_add_cancel ‹k ≤ d'›] at this,
        simp [this],
      end,
      simp [ge, h, type.lift, lift_idx, h', this] }
  },
  { simp [ge, lift_idx, h],
    have : ¬d' - k ≤ i, begin
      have : k + i < k + d, from add_lt_add_left (lt_of_not_ge h) _,
      have : i + k < k + d, by simp [this],
      have : d' > i + k, from lt_of_lt_of_le this ‹k + d ≤ d'›,
      have : d' - k > i + k - k, from nat.sub_lt_sub_right this (nat.le_add_left _ _),
      simp only [nat.add_sub_cancel] at this,
      exact not_le_of_gt this,
    end,
    have : d ≤ d', from le_trans (nat.le_add_left _ _) ‹k + d ≤ d'›,
    have : ¬d' ≤ i, from not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge h) this),
    simp [*, h, type.lift, this] }
end

lemma nat.succ_le_iff_lt (n m : ℕ) : n.succ ≤ m ↔ n < m := ⟨nat.succ_le_of_lt, nat.lt_of_succ_le⟩

@[simp]
lemma expand_lift (k d) (a : type) : (a.lift k (d+1)).expand = a.expand.lift k d :=
begin
  intros, simp [type.expand,type.instantiate,type.lift,instantiate_idx,rename_rename,function.comp],
  -- HACK
  apply @congr_fun _ _ (type.subst _) (type.subst _),
  apply congr_arg, apply funext, intro i,
  simp [nat.not_lt_zero,ge,lift_idx,nat.succ_le_iff_lt],
  by_cases d < i,
  { have : 0 < i, from lt_of_le_of_lt (nat.zero_le _) ‹d < i›,
    have : 0 < k + i, from lt_of_lt_of_le this (nat.le_add_left _ _),
    simp [*, le_of_lt h, nat.add_sub_assoc, nat.succ_le_iff_lt, nat.le_sub_one_of_lt] },
  { simp [*],
    cases i with i,
    { simp [rename_up_comp_rename_up, nat.not_lt_zero],
      apply congr_arg, apply congr_fun, apply congr_arg, apply funext, intro j,
      cases j, --by_cases d ≤ j,
      { simp [rename.up,*] },
      { simp [rename.up,*, function.comp, if_distrib nat.succ, nat.add_one, nat.add_succ,
          nat.lt_succ_iff_le],
        erw rename_up_id, apply if_congr; simp }
    },
    { have : ¬ d ≤ i, from h ∘ nat.lt_succ_of_le,
      simp [nat.zero_lt_succ,*] }
  }
end

@[simp]
lemma env.length_lift (e : env) (k d) : (e.lift k d).length = e.length :=
by induction e; simp [env.lift, *]

@[simp]
lemma option_has_map_map_none {α β : Type} (f : α → β) : f <$> none = none := rfl

@[simp]
lemma option_has_map_map_some {α β : Type} (f : α → β) (x : α) : f <$> some x = f x := rfl

@[simp]
lemma env.nth_lift {e : env} (k d i) : (e.lift k d).nth i = (λ a : type, a.lift k (d + (e.length - 1 - i))) <$> e.nth i :=
begin
  induction e generalizing i,
  { simp [env.lift] },
  { simp [list.nth],
    cases i with i,
    { simp [env.lift, list.nth, nat.add_sub_cancel_left], refl },
    { simp [env.lift, ih_1, nat.add_sub_cancel_left, nat.sub_sub] }
  }
end

/-@[simp]
lemma lift_zero (a : type) : a.lift 0 = a :=
by induction a; simp [*, type.lift]-/

@[simp]
lemma up_lift_idx (k d) : (lift_idx k d).up = lift_idx k (d+1) :=
begin
  apply funext, intro i,
  simp [lift_idx],
  cases i,
  { have : d + 1 > 0, from nat.zero_lt_succ _,
    simp [rename.up, ge, not_le_of_gt this] },
  { simp [rename.up, ge, nat.succ_le_succ_iff],
    rw if_distrib (has_add.add 1),
    simp [nat.add_one],
    apply if_congr; refl }
end

@[simp]
lemma up_instantiate_idx (a d) : (instantiate_idx a d).up = instantiate_idx a (d+1) :=
begin
  apply funext, intro i,
  simp [instantiate_idx],
  cases i with i,
  { have : d + 1 > 0, from nat.zero_lt_succ _,
    simp [subst.up, not_lt_of_ge (nat.zero_le _), ne_of_lt this] },
  { simp [subst.up, ge, nat.succ_lt_succ_iff, nat.add_one],
    by_cases d < i,
    { have : 0 < i, from lt_of_le_of_lt (nat.zero_le _) h,
      simp [*, (nat.succ_sub this).symm] },
    { simp *,
      by_cases i = d,
      { simp [*,type.lift,lift_idx,function.comp,nat.zero_le,ge,nat.add_succ] },
      { have : i.succ ≠ d.succ, from h ∘ nat.succ.inj,
        simp [*] }
    }
  }
end

section
variables (k d : ℕ)
@[simp] def type.lift_idx (x : ℕ) : (var x).lift k d = var (lift_idx k d x) := rfl
@[simp] def type.lift_top : top.lift k d = top := rfl
@[simp] def type.lift_app (a b) : (a →ₛ b).lift k d = a.lift k d →ₛ b.lift k d := rfl
@[simp] def type.lift_abs (a b) : (∀0<:a, b).lift k d = ∀0<:a.lift k d, b.lift k (d+1) := by simp [type.lift]
@[simp] def type.lift_mu (a) : (mu a).lift k d = mu (a.lift k (d+1)) := by simp [type.lift]

variables (r : type)
@[simp] def type.instantiate_var (x : ℕ) : (var x).instantiate r d = if d < x then var (x-1) else if x = d then r.lift d else var x := rfl
@[simp] def type.instantiate_top : top.instantiate r d = top := rfl
@[simp] def type.instantiate_app (a b) : (a →ₛ b).instantiate r d = a.instantiate r d →ₛ b.instantiate r d := rfl
@[simp] def type.instantiate_abs (a b) : (∀0<: a, b).instantiate r d = ∀0<:a.instantiate r d, b.instantiate r (d+1) := by simp [type.instantiate]
@[simp] def type.instantiate_mu (a) : (mu a).instantiate r d = mu (a.instantiate r (d+1)) := by simp [type.instantiate]
end

lemma sub_insert {e₁ e₂ : env} {a b c} : e₁ ++ e₂ ⊢ a <: b → e₁.lift 1 ++ c::e₂ ⊢ a.lift 1 e₁.length <: b.lift 1 e₁.length :=
begin
  generalize he' : e₁ ++ e₂ = e',
  intro h, induction h generalizing c e₁,
  all_goals { simp [lift_idx, -add_comm], try {constructor; done} },
  case sub.env e' x a b h₁ h₂ ih {
    subst e',
    by_cases x ≥ e₁.length,
    { simp [if_pos h], apply sub.env,
      { have : ¬ (x + 1 < e₁.length), from
          λ hcontr, not_lt_of_ge h (nat.lt_of_succ_lt hcontr),
        simp [list.nth_append, this, nat.sub_add_comm h, -add_comm, list.nth],
        simp [list.nth_append, if_neg (not_lt_of_ge h)] at h₁,
        apply h₁ },
      { have ih := ih rfl,
        rw lift_lift _ (nat.zero_le _) (nat.le_succ_of_le h) at ih,
        apply ih }
    },
    { simp [if_neg h], apply sub.env,
      { simp [list.nth_append, lt_of_not_ge h] at ⊢ h₁,
        -- HACK
        show _ = some (a.lift 1 (e₁.length - 1 - x)),
        simp [h₁], refl },
      { have ih := ih rfl,
        rw lift_lift2 at ih,
        { rw [nat.sub_sub, nat.one_add], apply ih },
        { apply nat.succ_le_of_lt (lt_of_not_ge h) }
      }
    }
  },
  case sub.abs {
    have ih_2 := @ih_2 c (a'::e₁),
    apply sub.abs; simp [*, env.lift] at *
  },
  case sub.fun {
    apply sub.fun (ih_1 he') (ih_2 he')
  },
  case sub.expₗ {
    apply sub.expₗ,
    simp only [expand_lift],
    apply ih_1 he'
  },
  case sub.expᵣ {
    apply sub.expᵣ,
    simp only [expand_lift],
    apply ih_1 he'
  }
end

lemma prod.sub {e : env} {a a' b b'} :
  e ⊢ a <: a' →
  e ⊢ b <: b' →
  e ⊢ a ×ₛ b <: a' ×ₛ b' :=
begin
  intros,
  repeat {any_goals {constructor}},
  apply @sub_insert []; assumption,
  apply @sub_insert []; assumption
end

lemma {u} list.elem_zip_cons_of_elem_zip {α β : Type u} {a : α} {b : β} {p as bs} : p ∈ list.zip as bs → p ∈ list.zip (a::as) (b::bs) :=
or.inr

lemma list.sub {e : env} {as as'} : list.length as = list.length as' → (∀ p ∈ as.zip as', e ⊢ prod.fst p <: p.2) → e ⊢ tuple as <: tuple as' :=
begin
  intros hlen helem, induction as generalizing as',
  { cases as', {constructor}, {contradiction} },
  { cases as', {contradiction},
    simp [tuple],
    apply prod.sub,
    { apply helem (a, a_2), simp [list.zip, list.zip_with] },
    { simp [list.length] at hlen, apply ih_1 (eq_of_add_eq_add_left hlen),
      intros p hp, apply helem p (list.elem_zip_cons_of_elem_zip hp), }
  }
end

@[simp]
lemma lift_tuple (as k d) : (tuple as).lift k d = tuple (as.map (λ a, a.lift k d)) :=
begin
  induction as generalizing d,
  { refl },
  { simp [tuple, prod, lift_idx, lift_lift2, *, ge, not_le_of_gt (nat.zero_lt_succ _)] }
end

@[simp]
lemma instantiate_idx_lift_idx (i b d) : instantiate_idx b (d + 1) (lift_idx 1 0 i) = type.rename (lift_idx 1) (instantiate_idx b d i) :=
begin
  simp [instantiate_idx, lift_idx, ge, nat.zero_le, nat.add_one, nat.succ_lt_succ_iff],
  by_cases d < i,
  { have : 0 < i, from lt_of_le_of_lt (nat.zero_le _) ‹d < i›,
    simp [*, has_sub.sub, nat.sub, nat.succ_pred_eq_of_pos this] },
  { simp [*],
    by_cases i = d,
    { simp [*, type.lift, lift_idx, function.comp, ge, nat.zero_le, nat.add_succ] },
    { simp [*, show i.succ ≠ d.succ, from h ∘ nat.succ.inj] }
  }
end

@[simp]
lemma instantiate_tuple (as b d) : (tuple as).instantiate b d = tuple (as.map (λ a, a.instantiate b d)) :=
begin
  generalize h : as.length = l,
  induction l generalizing as b d,
  { simp [list.eq_nil_of_length_eq_zero h], refl },
  { cases as,
    { contradiction },
    { rw list.length at h, injection h with h,
      simp [tuple, prod, nat.not_lt_zero],
      rw ih_1 _ b (d+1),
      { have : 0 ≠ d + 1, by intro hcontr; injection hcontr,
        simp [*, type.instantiate, type.lift, function.comp, list.length_map] },
      { simp [*, list.length_map] }
    }
  }
end

lemma instantiate_record (b fs) : (record fs).instantiate b = record (fs.map (λ ⟨i, a⟩, ⟨i, a.instantiate b⟩)) :=
begin
  simp [record, record_list],
  apply congr_arg,
  apply congr_fun,
  { apply congr_arg,
    apply congr,
    { apply congr_arg,
      apply funext, intro i,
      induction fs,
      { refl },
      { simp [list.find], cases a,
        simp,
        by_cases idx = i,
        { simp [function.comp, h, option.get_or_else, has_map.map, option.map, option.bind] },
        { simp [function.comp, h], apply ih_1 },
      }
    },
    { apply congr_arg,
      apply congr_arg,
      apply congr_fun, simp,
      apply congr_fun,
      apply congr_arg,
      apply funext, intro a, cases a with idx ty,
      simp }
  }
end

lemma record.sub {e} {fs fs' : list field} :
  (record_list fs).length ≥ (record_list fs').length →
  (∀ p : _ × _, p ∈ (record_list fs).zip (record_list fs') → e ⊢ p.1 <: p.2) →
  e ⊢ record fs <: record fs' :=
begin
  simp [record],
  generalize : record_list fs = rfs,
  induction record_list fs' generalizing rfs,
  all_goals { intros hlen helem },
  case list.nil {
    cases rfs,
    { apply sub.refl },
    { simp [tuple], apply prod.sub; apply sub.top }
  },
  case list.cons {
    cases rfs,
    { cases hlen },
    { simp [tuple], apply prod.sub,
      { apply helem, simp [list.zip, list.zip_with] },
      { apply ih_1,
        { simp at hlen, apply le_of_add_le_add_left hlen },
        { intros a b hab, apply helem a b (list.elem_zip_cons_of_elem_zip hab) }
      }
    }
  }
end

lemma lift_free_range {t : type} (k m) : t.free_range ≤ m → t.lift k m = t :=
begin
  induction t generalizing m,
  all_goals { simp [type.free_range] },
  { intro h,  simp [lift_idx, ge, not_le_of_gt (nat.lt_of_succ_le h)] },
  { intro h,
    have := ih_1 m (le_trans (le_max_left _ _) h),
    rw [this],
    have := ih_2 m (le_trans (le_max_right _ _) h),
    rw [this] },
  { intro h,
    have := ih_1 m (le_trans (le_max_left _ _) h),
    rw [this],
    have : body.lift k (m+1) = body, {
      apply ih_2 (m+1),
      have : body.free_range - 1 ≤ m, from le_trans (le_max_right _ _) h,
      show body.free_range ≤ m + 1, from nat.le_succ_of_pred_le this,
    },
    rw [this] },
  { intro h,
    have := ih_1 (m+1) (nat.le_succ_of_pred_le h),
    rw [this] }
end

lemma lift_closed {t : type} (k) : t.closed → (t.lift k) = t :=
begin
  intro h, apply lift_free_range,
  simp [type.closed] at h, simp [h]
end

lemma left_le_of_max_le {a b c : ℕ} : max a b ≤ c → a ≤ c :=
begin
  intro h,
  by_cases a ≤ b with ab,
  { simp [max, ab] at h, apply le_trans ab h },
  { simp [max, ab] at h, apply h }
end

lemma right_le_of_max_le {a b c : ℕ} : max a b ≤ c → b ≤ c :=
begin
  intro h,
  by_cases a ≤ b with ab,
  { simp [max, ab] at h, apply h },
  { simp [max, ab] at h, apply le_trans (le_of_not_le ab) h }
end

lemma instantiate_free_range {t t' : type} {d} : t.free_range ≤ d → t.instantiate t' d = t :=
begin
  induction t generalizing d,
  all_goals { simp [type.free_range] },
  { intro h,
    have : idx < d, from nat.lt_of_succ_le h,
    simp [lift_idx, instantiate_idx, ne_of_lt this, not_lt_of_gt this] },
  { intro h, rw[ih_1 (le_trans (left_le_of_max_le h) (le_refl _)),
                ih_2 (le_trans (right_le_of_max_le h) (le_refl _))] },
  { intro h, rw[ih_1 (le_trans (left_le_of_max_le h) (le_refl _)),
                ih_2 (le_trans (nat.le_succ_of_pred_le (right_le_of_max_le h)) (le_refl _))] },
  { intro h, rw[ih_1 (le_trans (nat.le_succ_of_pred_le h) (le_refl _))] },
end

@[simp]
lemma instantiate_closed {t t' : type} : t.closed → t.instantiate t' = t :=
begin
  intro h, apply instantiate_free_range,
  simp [type.closed] at h, simp [h]
end

section
parameter int : type

def labels.a := 0
def labels.b := 1
def labels.c := 2

def foo := ⟦ₛ { a := int, b := top } ⟧
def bar := ⟦ₛ { a := int, b := int, c := int } ⟧

example : bar <: foo :=
record.sub dec_trivial (λ ⟨a, b⟩ h, begin
  conv at h {
    find (list.zip _ _) {whnf},
    simp,
    find (option.get_or_else _ _) {whnf},
    find (option.get_or_else _ _) {whnf},
    find (option.get_or_else _ _) {whnf},
    find (option.get_or_else _ _) {whnf},
  },
  cases h with h h; simp [h],
  { apply sub.refl },
  { apply sub.top },
end)

end

end system_f_sub

/- Unused experiments -/

section
open lean
open lean.parser
open interactive
open interactive.types
open tactic

@[user_command]
meta def extend_inductive_cmd (dmi : decl_meta_info) (_ : parse $ tk "extend_inductive") : parser unit :=
do base ← ident,
   base ← resolve_constant base,
   env ← get_env,
   guard (env.is_inductive base) <|> fail "expected inductive type",
   tk "with",
   decl ← inductive_decl.parse dmi,
   [idecl] ← pure decl.decls | fail "mutual inductives not supported",
   let new := idecl.sig.app_fn.local_uniq_name,
   let ls : list name := [], -- TODO
   let p := env.inductive_num_params base,
   ty ← declaration.type <$> env.get base,
   is ← (env.constructors_of base).mmap (λ ctor,
     do ty ← declaration.type <$> env.get ctor,
     let ty := ty.replace (λ e _, match e with
     | expr.const n ls := if n = base then some (expr.const new ls) else none
     | _ := none
     end) in
     pure (new ++ ctor.components.ilast, ty)),
   let is := is ++ idecl.intros.map (λ e, (e.local_uniq_name, e.local_type)),
   set_env $ env.add_namespace new,
   add_inductive new ls p ty is

meta def dunfold_productive (cfg : delta_config := {}) : conv unit :=
let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
  (expr.const f_name _) ← return e.get_app_fn,
  es ← get_eqn_lemmas_for ff f_name,
  guard $ es.length > 1,
  sl ← es.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
  new_e ← sl.drewrite e,
  return (u, new_e, tt)
in do e ← target,
      (c, new_e) ← dsimplify_core () (λ c e, failed) unfold e {max_steps := cfg.max_steps, canonize_instances := cfg.visit_instances},
      change new_e

meta def delta_target (cs : list name) (cfg : delta_config := {}) : tactic unit :=
do t ← target, delta cs t cfg >>= unsafe_change

run_cmd add_interactive [`dunfold_productive] `conv.interactive
end
