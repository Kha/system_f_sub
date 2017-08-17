import data.list.basic

namespace system_f_sub

inductive type
| var (idx : ℕ)
| top
| «fun» (domain body : type)
| abs (bound body : type)

-- inductive type : opt_param ℕ 0 → Type
-- | var {depth} (idx : fin depth) : type depth
-- | top {depth} : type depth
-- | «fun» {depth} (domain body : type depth) : type depth
-- | abs {depth} (bound : type depth) (body : type (depth + 1)) : type depth

open type

local infixr ` →ₛ `:50 := type.fun
local notation `∀0<: ` t `, ` s := abs t s

def type.lift : ℕ → type → type
| d (var x) := var (x+d)
| d top := top
| d (a →ₛ b) := type.lift d a →ₛ type.lift d b
| d (∀0<:a, b) := ∀0<:type.lift d a, type.lift d b

-- def fin.add' {n} : Π k, fin n → fin (n+k)
-- | 0 n := n
-- | (k+1) n := (fin.add' k n).succ
-- 
-- def type.lift (k : ℕ) : Π {d}, type d → type (d+k)
-- | d (var x) := var $ x.add' k
-- | d top := top
-- | d (a →ₛ b) := type.lift a →ₛ type.lift b
-- | d (∀0<:a, b) := ∀0<:type.lift a, cast (by simp) (type.lift b)

-- instance nat_to_type : has_coe ℕ type := ⟨bound⟩

def env := list type
-- inductive env : ℕ → Type
-- | nil : env 0
-- | push {d} : type d → env d → env (d+1)

-- def env.add (e : env) (a : type) : env :=
-- (a :: e).map type.lift

-- def env.add {d} (e : env d) (a : type d) : env (d+1) :=
-- (a :: e).map type.lift

inductive sub : env → type → type → Prop
  notation e ` ⊢ `:40 a ` <: `:40 b:40 := sub e a b
| var_refl (e x) : e ⊢ var x <: var x
| env {e x a b} : list.nth e x = some a → e ⊢ b <: a.lift x → e ⊢ var x <: b
| top (e a) : e ⊢ a <: top
| «fun» {e a a' b b'} : e ⊢ a' <: a → e ⊢ b <: b' → e ⊢ a →ₛ b <: a' →ₛ b'
| abs {e a a' b b'} : e ⊢ a' <: a → a'::e ⊢ b <: b' → e ⊢ ∀0<:a, b <: ∀0<:a', b'

--inductive sub : Π {d}, env d → type d → type d → Prop
--  notation e ` ⊢ `:40 a ` <: `:40 b:40 := sub e a b
--| var_refl {d} (e : env d) (x) : e ⊢ var x <: var x
----| trans {d a b c} {e : env d} : e ⊢ a <: b → e ⊢ b <: c → e ⊢ a <: c
--| env {d a b} {e : env d} : e ⊢ a <: b → e.push a ⊢ var 0 <: b.lift 1
----| lift {d a b c} {e : env d} : e ⊢ b <: c → e.push a ⊢ b.lift 1 <: c.lift 1
--| top {d} (e : env d) (a) : e ⊢ a <: top
--| «fun» {d} {e : env d} {a a' b b'} : e ⊢ a' <: a → e ⊢ b <: b' → e ⊢ a →ₛ b <: a' →ₛ b'
--| abs {d} {e : env d} {a a' b b'} : e ⊢ a' <: a → e.push a' ⊢ b <: b' → e ⊢ ∀0<:a, b <: ∀0<:a', b'

notation e ` ⊢ `:40 a:41 ` <: `:40 b:40 := sub e a b
notation a ` <: `:40 b:40 := sub [] a b
-- notation a ` <: `:40 b:40 := sub vector.nil a b

lemma sub.refl : Π e a, e ⊢ a <: a
| e (var x)    := sub.var_refl e x
| e top        := sub.top e top
| e (a →ₛ b)   := sub.fun (sub.refl e a) (sub.refl e b)
| e (∀0<:a, b) := sub.abs (sub.refl e a) (sub.refl _ b)
--lemma sub.refl : Π {d} (e : env d) a, e ⊢ a <: a
--| d e (var x)    := sub.var_refl e x
--| d e top        := sub.top e top
--| d e (a →ₛ b)   := sub.fun (sub.refl e a) (sub.refl e b)
--| d e (∀0<:a, b) := sub.abs (sub.refl e a) (sub.refl _ b)

-- private def trans_env : ℕ → env → Prop
-- | _ [] := true
-- | d (a::e) := trans_env (d+1) e ∧ ∀ b, e ⊢ a <: b → a::e ⊢ var d <: b
-- 
-- private lemma trans_env_nth {d e a x} : trans_env d e → e.nth x = some a → e ⊢ var x <: a.lift x :=
-- begin
--   intros,
--   induction e,
--   case list.nil { apply nth}
-- end
-- 
-- lemma sub.trans {e a b c}
--   (he : trans_env 0 e) : e ⊢ a <: b → e ⊢ b <: c → e ⊢ a <: c :=
-- begin
--   intros h₁ h₂,
--   induction h₁,
--   case sub.var_refl { apply h₂ },
--   case sub.env {
--   }
-- end

--lemma type_succ {d} (t : type (d+1)) : t ≠ var 0 → ∃ t' : type d, t = t'.lift 1 :=
--begin
--  intro h, tactic.get_local `t >>= tactic.induction
--end
--
--lemma type_succ {d} (t : type (d+1)) : t = var 0 ∨ ∃ t' : type d, t = t'.lift 1 :=

--lemma sub.trans {e a b c} : e ⊢ a <: b → e ⊢ b <: c → e ⊢ a <: c :=
--begin
--  intros h₁ h₂,
--  induction b,
--  { generalize h : var idx = b, rw h at h₁, induction h₁,
--    { rw ←h, apply h₂ },
--    { apply sub.env a_2 }
--
--    }
--  induction h₁,
--  case sub.var_refl { apply h₂ },
--  case sub.env { apply sub.env ‹_› }
--end

--lemma sub.trans {d} {e : env d} {a b c} : e ⊢ a <: b → e ⊢ b <: c → e ⊢ a <: c :=
--begin
--  intros h₁ h₂,
--  -- induction e,
--  -- { },
--  induction h₁,
--  case sub.var_refl { apply h₂ },
--  case sub.env { apply sub.env }
--end

section
open lean
open lean.parser
open interactive
open interactive.types

open expr (app pi const)

reserve notation `⟦ₛ`:1000

private meta def aux : ℕ → ℕ → pexpr → parser pexpr
| d d' (expr.var n) := let n := n - d' in pure ``(var %%(reflect n))
| d d' (expr.const ``top _) := pure ``(top)
| d d' (expr.local_const n m bi t) := pure $ ``(type.lift  %%(reflect d) %%(expr.local_const n m bi t))
-- ``(∀ x <: %%a, %%b)
| d d' (pi _ _ _ (pi _ _ (app (app (app (const `sub []) _) (expr.var 0)) a) b)) :=
do a ← aux (d+1) (d'+1) a, b ← aux (d+1) (d'+1) b, pure ``(∀0<:%%a, %%b)
| d d' (expr.pi _ _ dom b) :=
if (@unchecked_cast _ expr b).has_var_idx 0 then
     do b ← aux (d+1) d' b, pure ``(∀0<:top, %%b)
   else
     do dom ← aux d d' dom, b ← aux d (d'+1) b, pure ``(%%dom →ₛ %%b)
| d d' e := match e.get_structure_instance_info with
  | some info :=
    let fields := (info.field_names.zip info.field_values).map (λ ⟨n, v⟩,
      ``(⟨%%(const (`labels ++ n) [] : pexpr), %%v⟩)) in
    pure ```(record %%(fields.foldr (λ e f, ``(%%e::%%f)) ``([])))
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

--lemma sub.antisymm {e a b} : e ⊢ a <: b → e ⊢ b <: a → a = b :=
--begin
--  intros h₁ h₂,
--  induction h₁,
--  case sub.var_refl e x { show var x = var x, from rfl },
--  case sub.env e a b {{
--    cases h₂,
--    { refl },
--  }},
--end
--
--example : ¬ (True <: False) := by intro; cases a

def prod (a b : type) := ⟦ₛ ∀ r, (a → b → r) → r ⟧
infix ` ×ₛ `:45 := prod

lemma sub_iff_sub_lift {e k a b} : e ⊢ type.lift k a <: type.lift k b ↔ e.drop k ⊢ a <: b := sorry

lemma prod.sub {e a a' b b'} :
  e ⊢ a <: a' →
  e ⊢ b <: b' →
  e ⊢ a ×ₛ b <: a' ×ₛ b' :=
by intros; repeat { any_goals {constructor <|> apply sub_iff_sub_lift.mpr <|> assumption} }

def tuple : list type → type
| []      := top
| (a::as) := a ×ₛ tuple as

lemma {u} list.elem_zip_cons_of_elem_zip {α β : Type u} {a : α} {b : β} {p as bs} : p ∈ list.zip as bs → p ∈ list.zip (a::as) (b::bs) :=
or.inr

lemma list.sub {e as as'} : list.length as = list.length as' → (∀ p ∈ as.zip as', e ⊢ prod.fst p <: p.2) → e ⊢ tuple as <: tuple as' :=
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
example : bar <: foo :=
record.sub dec_trivial (λ ⟨a, b⟩ h, begin
  conv at h { reduce, simp },
  cases h with h h; simp [h],
  { apply sub.top },
  { apply sub.refl },
end)

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
end

namespace system_f_sub_mu
--extend_inductive type with type
--| μ : type → type

inductive type
| var (idx : ℕ)
| top
| «fun» (domain body : type)
| abs (bound body : type)
| mu (rec : type)

open type

local infixr ` →ₛ `:50 := type.fun
local notation `∀0<: ` t `, ` s := abs t s

def type.instantiate_aux (b : type) : ℕ → type → type
| d (var n) := if n = d then b else var n
| d top     := top
| d (a →ₛ b) := type.instantiate_aux d a →ₛ type.instantiate_aux d b
| d (∀0<: a, b) := ∀0<:type.instantiate_aux d a, type.instantiate_aux (d+1) b
| d (mu a) := mu (type.instantiate_aux (d+1) a)

def type.instantiate (a b : type) := type.instantiate_aux b 0 a

def type.expand (a : type) : type :=
a.instantiate (mu a)

inductive relμ : type → type → Prop
  infix ` ~ `:40 := relμ
| expand {a b : type} : a.expand ~ b → mu a ~ b
| retract {a b : type} : a ~ b.expand → a ~ mu b
| var (n) : var n ~ var n
| top : top ~ top
| «fun» {d d' b b'} : d ~ d' → b ~ b' → d →ₛ b ~ d' →ₛ b'
| abs {a a' b b'} : a ~ a' → b ~ b' → abs a b ~ abs a' b'
| mu {a a'} : a ~ a' → mu a ~ mu a'

local infix ` ~ `:40 := relμ

lemma relμ.refl (a) : a ~ a := sorry

def type' := quot relμ
instance : setoid type := ⟨relμ, sorry⟩

example : ⟦ mu (top →ₛ var 0) ⟧ = ⟦ top →ₛ mu (top →ₛ var 0) ⟧ :=
begin
  apply quotient.sound,
  apply relμ.expand,
  apply relμ.refl
end

def prod (a b : type) := ∀0<:top, (a.lift 1 →ₛ b.lift 1 →ₛ var 0) →ₛ var 0 --⟦ₛ ∀ r, (a → b → r) → r ⟧
infix ` ×ₛ `:45 := prod

def tuple : list type → type
| []      := top
| (a::as) := a ×ₛ tuple as

section records
structure field :=
(idx : ℕ)
(type : type)

def record_list (fields : list field) : list type :=
let max_idx := (fields.map field.idx).foldr max 0 in
(list.range (max_idx+1)).map (λ i, (field.type <$> fields.find (λ f, f.idx = i)).get_or_else top)

def record (fields : list field) : type :=
tuple (record_list fields ++ [top])
end records

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
| d d' (expr.const n ls) := pure $ const n ls
| d d' (app (const ``mu_helper _) (lam _ _ _ a)) := do a ← aux (d+1) d' a, pure ``(mu %%a)
| d d' (expr.local_const n m bi t) := pure $ ``(type.lift  %%(reflect d) %%(expr.local_const n m bi t))
-- ``(∀ x <: %%a, %%b)
| d d' (pi _ _ _ (pi _ _ (app (app (app (const `sub []) _) (expr.var 0)) a) b)) :=
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
         pure ``(⟨%%(const (`system_f_sub_mu.labels ++ n) [] : pexpr), %%v⟩)),
    pure ``(record %%(fields.foldr (λ e f, ``(%%e::%%f)) ``([])))
  | _ := tactic.fail format!"unsupported sub-expression {e.to_raw_fmt}"
  end

@[user_notation]
meta def interpret_notation (_ : parse $ tk "⟦ₛ") (e : parse $ parser.pexpr 0 <* tk "⟧") : parser pexpr :=
do e ← aux 0 0 e, pure ``(⟦%%e⟧)
end

example : ⟦ₛ μ a, top → a ⟧ = ⟦ₛ top → μ a, top → a ⟧ :=
begin
  apply quotient.sound,
  apply relμ.expand,
  apply relμ.refl
end

end system_f_sub_mu
