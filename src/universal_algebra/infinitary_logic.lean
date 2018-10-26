import logic.basic

universe u

namespace infinitary_logic

/-- The possible arities (i.e., types) of function symbols in a
  signature with set of sorts S. -/
structure fn_arity (S : Type u) :=
(arity : Type u)
(arg : arity → S)
(res : S)

/-- The possible arities (i.e., types) of relation symbols in a
  signature with set of sorts S. -/
structure rel_arity (S : Type u) :=
(arity : Type u)
(arg : arity → S)

/-- A signature on the set of sorts S, consisting of collections of
  function and relation symbols, with specified arities. -/
structure signature (S : Type u) :=
(fn : Type u)
(fn_arity : fn → fn_arity S)
(rel : Type u)
(rel_arity : rel → rel_arity S)

/-- A collection of free variables, indexed by their sorts. -/
def vars (S : Type u) := S → Type u

def vars.empty {S : Type u} : vars S := λ s, pempty
def vars.oplus {S : Type u} (V W : vars S) : vars S := λ s, V s ⊕ W s

section syntax
/- Logical syntax of a particular signature. -/
variables {S : Type u} (sig : signature S)

/-- Terms in the given free variables and of a particular sort. -/
inductive term (V : vars S) : S → Type u
| var {} : Π {s}, V s → term s
| app : Π (f : sig.fn)
          (t : Π (i : (sig.fn_arity f).arity), term ((sig.fn_arity f).arg i)),
        term (sig.fn_arity f).res

/-- Atomic formulas in the given free variables. -/
inductive atomic_formula (V : vars S) : Type u
| eq : Π {s : S}, term sig V s → term sig V s → atomic_formula
| rel : Π (r : sig.rel)
          (t : Π (i : (sig.rel_arity r).arity), term sig V ((sig.rel_arity r).arg i)),
        atomic_formula

/-- Formulas with the given free variables. -/
inductive formula : vars S → Type (u+1)
| atom : Π {V}, atomic_formula sig V → formula V
| neg : Π {V}, formula V → formula V
| imp : Π {V}, formula V → formula V → formula V
| disj : Π {V} {I : Type u}, (I → formula V) → formula V
| conj : Π {V} {I : Type u}, (I → formula V) → formula V
| fa : Π {V : vars S} (W : vars S), formula (V.oplus W) → formula V
| ex : Π {V : vars S} (W : vars S), formula (V.oplus W) → formula V

def sentence : Type (u+1) := formula sig vars.empty

variables {sig}

section subst

open term atomic_formula formula

/-- Substituting terms for the free variables of a term. This makes
  `term sig` into an "S-sorted monad" (that is, a monad on the category
  Set^S). The order of the arguments here is the reverse of that of
  `monad.bind` so that we can define `term.subst` by induction easily. -/
def term.subst {V V' : vars S} (t' : Π {s'}, V s' → term sig V' s') :
  Π {s}, term sig V s → term sig V' s
| _ (var v) := t' v
| _ (app f ts) := app f (λ i, (ts i).subst)

/-- Substitute new variables for old in a term (`term sig` is a functor). -/
def term.map {V V' : vars S} (f : Π {s'}, V s' → V' s') {s : S}
  (t : term sig V s) : term sig V' s :=
t.subst (λ s' v, var (f v))

/-- Substituting terms for the free variables of an atomic formula.
  This makes `atomic_formula sig` into a module over `term sig`. -/
def atomic_formula.subst {V V' : vars S} (t' : Π s', V s' → term sig V' s') :
  atomic_formula sig V → atomic_formula sig V'
| (eq t₁ t₂) := eq (t₁.subst t') (t₂.subst t')
| (rel r ts) := rel r (λ i, (ts i).subst t')

/-- Extend a substitution when crossing a quantifier binding variables W. -/
private def extend_substitution {V V' W : vars S}
  (t' : Π s', V s' → term sig V' s') :
  Π s', (V.oplus W) s' → term sig (V'.oplus W) s'
| s' (sum.inl v) := (t' s' v).map (λ _, sum.inl)
| s' (sum.inr w) := var (sum.inr w)

/-- Substituting terms for the free variables of a formula, as above. -/
def formula.subst : Π {V V' : vars S}, (Π s', V s' → term sig V' s') →
  formula sig V → formula sig V'
| _ _ t' (atom a) := atom (a.subst t')
| _ _ t' (neg φ) := neg (φ.subst t')
| _ _ t' (imp φ ψ) := imp (φ.subst t') (ψ.subst t')
| _ _ t' (disj φ) := disj (λ i, (φ i).subst t')
| _ _ t' (conj φ) := conj (λ i, (φ i).subst t')
| _ _ t' (fa W φ) := fa W (φ.subst (extend_substitution t'))
| _ _ t' (ex W φ) := ex W (φ.subst (extend_substitution t'))

/-- Substitute new variables for old in a formula. -/
def formula.map {V V' : vars S} (f : Π {s'}, V s' → V' s') :
  formula sig V → formula sig V' :=
formula.subst (λ s' v, var (f v))

end subst

-- Constructing formulas.

open formula

inductive ptwo : Type u
| left
| right

local attribute [elab_with_expected_type] ptwo.rec

/-- Empty conjunction of formulas, i.e., "true". -/
def formula.true {V : vars S} : formula sig V :=
formula.conj (pempty.rec _)

/-- Empty disjunction of formulas, i.e., "false". -/
def formula.false {V : vars S} : formula sig V :=
formula.disj (pempty.rec _)

/-- Binary conjunction of formulas. -/
def formula.and {V : vars S} (φ ψ : formula sig V) : formula sig V :=
formula.conj (ptwo.rec φ ψ)

/-- Binary disjunction of formulas. -/
def formula.or {V : vars S} (φ ψ : formula sig V) : formula sig V :=
formula.disj (ptwo.rec φ ψ)

local notation `⊤'` := formula.true
local notation `⊥'` := formula.false
local infixr ` ∧' `:35 := formula.and
local infixr ` ∨' `:30 := formula.or
local notation a ` =' `:50 b:50 := atom (atomic_formula.eq a b)

/-- The "unique existential" quantifier: ∃! (xᵢ) φ means
  (∃ (xᵢ) φ(xᵢ)) ∧ (∀ (xᵢ) (yᵢ), φ(xᵢ) ∧ φ(yᵢ) → ⋀ᵢ xᵢ = yᵢ). -/
def formula.ex_uniq {V : vars S} (W : vars S) (φ : formula sig (V.oplus W)) : formula sig V :=
ex W φ ∧' fa W (fa W (
  imp (φ.map (λ s' v, sum.inl v) ∧' φ.map (λ s' v, sum.rec_on v (sum.inl ∘ sum.inl) sum.inr))
      (conj (λ (w : sigma W), term.var (sum.inl (sum.inr w.2)) =' term.var (sum.inr w.2)))))

end syntax

section semantics
/- Structures and homomorphisms for a particular signature. -/
variables {S : Type u} (sig : signature S)

/-- A structure of the given signature on an S-sorted carrier `α`. -/
class str (α : S → Type u) : Type u :=
(fn : Π f : sig.fn, (Π i, α ((sig.fn_arity f).arg i)) → α (sig.fn_arity f).res)
(rel : Π r : sig.rel, (Π i, α ((sig.rel_arity r).arg i)) → Prop)

/-- Property for an S-sorted map `f` of being a homomorphism. -/
structure is_hom {α β : S → Type u} [sα : str sig α] [sβ : str sig β]
  (h : Π {s}, α s → β s) : Prop :=
(fn : ∀ (f : sig.fn) (xs : Π i, α ((sig.fn_arity f).arg i)),
  h (str.fn f xs) = str.fn f (λ i, h (xs i)))
(rel : ∀ (r : sig.rel) (xs : Π i, α ((sig.rel_arity r).arg i)),
  str.rel r xs → str.rel r (λ i, h (xs i)))

end semantics

end infinitary_logic
