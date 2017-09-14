import data.list.basic

lemma {u} if_pos' {c : Prop} {h : decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t :=
match h with
| (is_true  hc)  := rfl
| (is_false hnc) := absurd hc hnc
end

lemma {u} if_neg' {c : Prop} {h : decidable c} (hnc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e :=
match h with
| (is_true hc)   := absurd hc hnc
| (is_false hnc) := rfl
end

@[congr]
lemma {u} if_simp_congr' {α : Sort u} {b c : Prop} {dec_b : decidable b} {x y u v : α}
                    (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) α u v) :=
@if_ctx_simp_congr α b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)
local attribute [-congr] if_simp_congr

lemma nat.succ_lt_succ_iff (n m : ℕ) : n.succ < m.succ ↔ n < m :=
⟨nat.lt_of_succ_lt_succ, nat.succ_lt_succ⟩

theorem nat.sub_lt_sub_right : Π {n m k : ℕ} (h₁ : n < m) (h₂ : k ≤ n), n - k < m - k
| n     m     0     h₁ h₂ := h₁
| (n+1) (m+1) (k+1) h₁ h₂ := by simp; apply nat.sub_lt_sub_right (nat.lt_of_succ_lt_succ h₁) (nat.le_of_succ_le_succ h₂)

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

inductive type
| var (idx : ℕ)
| top
| «fun» (domain body : type)
| abs (bound body : type)
| mu (rec : type)

open type

local infixr ` →ₛ `:50 := type.fun
local notation `∀0<: ` t `, ` s := abs t s

@[simp]
def type.lift (k : ℕ) : type → opt_param ℕ 0 → type
| (var x)    d := if x ≥ d then var (x+k) else var x
| top        d := top
| (a →ₛ b)   d := a.lift d →ₛ b.lift d
| (∀0<:a, b) d := ∀0<:a.lift d, b.lift (d+1)
| (mu a)     d := mu (a.lift (d+1))

@[simp]
def type.instantiate : type → type → opt_param ℕ 0 → type
| (var n)     r d := if n < d then var (n-1) else if n = d then r.lift d else var n
| top         r d := top
| (a →ₛ b)    r d := a.instantiate r d →ₛ b.instantiate r d
| (∀0<: a, b) r d := ∀0<:a.instantiate r d, b.instantiate r (d+1)
| (mu a)      r d := mu (a.instantiate r (d+1))

def type.expand (a : type) : type :=
a.instantiate (mu a)

def type.free_range : type → ℕ
| (var d)     := d + 1
| top         := 0
| (a →ₛ b)    := max a.free_range b.free_range
| (∀0<: a, b) := max a.free_range (b.free_range - 1)
| (mu a)      := a.free_range - 1

@[reducible]
def type.closed (t : type) := t.free_range = 0

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
| d d' (expr.local_const n m bi t) := pure $ ``(type.lift  %%(reflect d) %%(expr.local_const n m bi t))
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

attribute [simp] nat.succ_le_succ

lemma lift_lift {k k' d d'} (a : type) : d ≤ d' → d' ≤ k + d → (a.lift k d).lift k' d' = a.lift (k + k') d :=
begin
  intros, induction a generalizing d d',
  all_goals { simp [*,type.lift] },
  case type.var {
    by_cases idx ≥ d,
    { simp [ge, h, type.lift, le_trans ‹d' ≤ k + d› (add_le_add_left h _)] },
    { have : ¬d' ≤ idx, from λ hcontr, h (le_trans ‹d ≤ d'› hcontr),
      simp [ge, h, type.lift, this] }
  },
  all_goals { simp [nat.add_one, *] }
end

@[simp]
lemma lift_lift' (k k') (a : type) : (a.lift k).lift k' = a.lift (k + k') :=
lift_lift _ dec_trivial dec_trivial

lemma lift_lift2 (k k' d d') (a : type) : k + d ≤ d' → (a.lift k d).lift k' d' = (a.lift k' (d' - k)).lift k d :=
begin
  intro h, induction a generalizing d d',
  all_goals {
    have : k ≤ d', from le_trans (nat.le_add_right _ _) ‹k + d ≤ d'›,
    simp [*,type.lift] },
  case type.var {
    by_cases idx ≥ d,
    { by_cases d' ≤ k + idx with h',
      { have : d' - k ≤ k + idx - k, from nat.sub_le_sub_right h' k,
        simp [nat.add_sub_cancel_left] at this,
        simp [ge, h, type.lift, h', this, le_add_of_nonneg_of_le (nat.zero_le _) h] },
      { have : ¬ d' - k ≤ idx, begin
          assume hcontr, apply h',
          have : d' - k + k ≤ idx + k, from nat.add_le_add_right hcontr k,
          simp [nat.sub_add_cancel ‹k ≤ d'›] at this,
          simp [this],
        end,
        simp [ge, h, type.lift, h', this] }
    },
    { simp [ge, h],
      have : ¬d' - k ≤ idx, begin
        have : k + idx < k + d, from add_lt_add_left (lt_of_not_ge h) _,
        have : idx + k < k + d, by simp [this],
        have : d' > idx + k, from lt_of_lt_of_le this ‹k + d ≤ d'›,
        have : d' - k > idx + k - k, from nat.sub_lt_sub_right this (nat.le_add_left _ _),
        simp only [nat.add_sub_cancel] at this,
        exact not_le_of_gt this,
      end,
      have : d ≤ d', from le_trans (nat.le_add_left _ _) ‹k + d ≤ d'›,
      have : ¬d' ≤ idx, from not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge h) this),
      simp [*, if_neg' h, type.lift, if_neg' this] }
  },
  case type.abs {
    rw [ih_2, add_comm, nat.add_sub_assoc ‹k ≤ d'›],
    { simp [nat.add_one, *] } },
  case type.mu {
    rw [ih_1, add_comm, nat.add_sub_assoc ‹k ≤ d'›],
    { simp [nat.add_one, *] } }
end

lemma nat.succ_le_iff_lt (n m : ℕ) : n.succ ≤ m ↔ n < m := ⟨nat.succ_le_of_lt, nat.lt_of_succ_le⟩

@[simp]
lemma instantiate_lift (a b : type) (k d d') : d' < d → (a.lift k (d + 1)).instantiate (b.lift k d) d' = (a.instantiate b d').lift k d :=
begin
  intro, induction a generalizing d d',
  all_goals { simp },
  case type.var {
    simp [nat.add_one, ge, nat.succ_le_iff_lt],
    by_cases d < idx,
    { have : ¬ k + idx < d', from sorry,
      have : k + idx ≠ d', from sorry,
      have : d' < idx, from lt_trans ‹d' < d› ‹d < idx›,
      simp [*, ge, le_of_lt h, not_lt_of_gt this, (ne_of_lt this).symm] },
    { simp [h],
      by_cases idx < d' with h',
      { have : ¬ idx - 1 ≥ d, from sorry,
        simp * },
      { by_cases idx = d',
        { simp [*] } }
    }
  }
end

@[simp]
lemma expand_lift (k d) (a : type) : (a.lift k (d+1)).expand = a.expand.lift k d :=
by simp [type.expand]; rw [←type.lift, instantiate_lift]

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

lemma sub_insert {e₁ e₂ : env} {a b c} : e₁ ++ e₂ ⊢ a <: b → e₁.lift 1 ++ c::e₂ ⊢ a.lift 1 e₁.length <: b.lift 1 e₁.length :=
begin
  generalize he' : e₁ ++ e₂ = e',
  intro h, induction h generalizing c e₁,
  all_goals { simp [type.lift, -add_comm], try {constructor; done} },
  case sub.var_refl {
    by_cases x ≥ e₁.length,
    { simp [if_pos h], apply sub.var_refl },
    { simp [if_neg h], apply sub.var_refl }
  },
  case sub.env e' x a b h₁ h₂ ih {
    subst e',
    by_cases x ≥ e₁.length,
    { simp [if_pos h], apply sub.env,
      { have : ¬ (x + 1 < e₁.length), from
          λ hcontr, not_lt_of_ge h (nat.lt_of_succ_lt hcontr),
        simp [list.nth_append, if_neg' this, nat.sub_add_comm h, -add_comm, list.nth],
        simp [list.nth_append, if_neg (not_lt_of_ge h)] at h₁,
        apply h₁ },
      { have ih := ih rfl,
        rw lift_lift _ (nat.zero_le _) (nat.le_succ_of_le h) at ih,
        apply ih }
    },
    { simp [if_neg h], apply sub.env,
      { simp [list.nth_append, if_pos' (lt_of_not_ge h)] at ⊢ h₁,
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

def tuple : list type → type
| []      := top
| (a::as) := a ×ₛ tuple as

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

section records
structure field :=
(idx : ℕ)
(type : type)

def record_list (fields : list field) : list type :=
let max_idx := (fields.map field.idx).foldr max 0 in
(list.range (max_idx+1)).map (λ i, (field.type <$> fields.find (λ f, f.idx = i)).get_or_else top)

def record (fields : list field) : type :=
tuple (record_list fields ++ [top])

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

end records

section
parameter int : type

def a := 0
def b := 1
def c := 2

def foo := record [⟨a, int⟩, ⟨b, top⟩]
def bar := record [⟨a, int⟩, ⟨b, int⟩, ⟨c, int⟩]

open tactic
--set_option trace.type_context.is_def_eq true
--set_option trace.simplify true
example : bar <: foo :=
record.sub dec_trivial (λ ⟨a, b⟩ h, begin
  conv at h {
    find (list.zip _ _) {whnf,reflexivity},
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

@[simp]
lemma lift_tuple (as k) : (tuple as).lift k = tuple (as.map (λ a, a.lift k 1)) :=
begin
  induction as,
  { refl },
  { simp [tuple, prod] }
end

@[simp]
lemma instantiate_tuple (as b) : (tuple as).instantiate b = tuple (as.map (λ a, a.instantiate b)) :=
begin
  induction as,
  { refl },
  { simp [tuple, prod, type.instantiate, ih_1] }
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
        { simp [function.comp, h, option.get_or_else, has_map.map, option_map, option_bind] },
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

lemma lift_free_range {t : type} (k m) : t.free_range ≤ m → t.lift k m = t :=
begin
  induction t generalizing m,
  all_goals { simp [type.free_range, type.lift] },
  { intro h,  simp [if_neg' (not_le_of_gt (nat.lt_of_succ_le h))] },
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
  all_goals { simp [type.instantiate, type.free_range] },
  { intro h, simp [if_neg (ne_of_lt (nat.lt_of_succ_le h))] },
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

end system_f_sub

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

example : ⟦ₛ μ a, top → a ⟧ = ⟦ₛ top → μ a, top → a ⟧ :=
begin
  apply quotient.sound,
  apply relμ.expand,
  apply relμ.refl
end

end system_f_sub_mu
