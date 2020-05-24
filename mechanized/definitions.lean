import data.set data.list finite_map

-- Assume opaque types for program variables and addresses (with decidable equality)
constants (x: Type) (x_eq: decidable_eq x)
constants (a: Type) (a_eq: decidable_eq a)

-- Program label, divided into ones from the concrete and symbolic parts
inductive ℓ
| kn: ℓ -- can generalize to be more fine-grained
| uk: ℓ

-- λ-calculus extended with natural numbers and symbolic values standing for any
-- The only error that can happen in this language is a blame on an application site
-- for applying a non-function
inductive e: Type
-- values
| n  : ℕ → e
| s  : e
| lam: x → e → e
-- others
| x  : x → e
| app: ℓ → e → e → e
| set: x → e → e

-- Environment
noncomputable def ρ: Type := map x a
attribute [reducible] ρ

-- Semantic value
inductive V
| n: ℕ → V
| c: x → e → ρ → V
| s: V -- symbolic value

-- An evaluation answer is either a value or a blame
inductive A
| V  : V → A
| blm: ℓ → A

-- Context
inductive E
| ev: e → ρ → E -- executing code `e` under environment `ρ`
| rt: A → E     -- returning answer `A`
| hv: E -- executing arbitrary code (with access to leaked transparent code)

-- Kontinuation frame
inductive φ
| fn: ℓ → V → φ
| ar: ℓ → e → ρ → φ
| st: a → φ

-- Kontinuation
def κ := list φ

-- Value store
noncomputable def σ := map a V
attribute [reducible] σ

-- Special value for leak set
constant aₗ: a

-- State
record s := of :: (ctx: E) (kont: κ) (sto: σ)

noncomputable def inj  (e: e): s := ⟨E.ev e [], [], []⟩
noncomputable def inj' (e: e): s := ⟨E.ev e [], [], [(aₗ, V.s)]⟩ -- tmp ugly hack
attribute [reducible] inj
attribute [reducible] inj'

-- Map between addresses
noncomputable def F:= map a a
attribute [reducible] F
