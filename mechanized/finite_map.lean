-- This module defines the relational version of `lookup` for finite maps
-- represented as associated lists, because `lookup(l, x) = some v` is more disgusting
-- than `lookup l x v`
-- Both deterministic and non-deterministic maps are represented as associated list.
-- It's the lookup relation (`map_to` vs `map_to₁` that makes it different).

import data.set

def map α β := list (α × β)

inductive map_to {α β: Type}: map α β → α → β → Prop
| fnd: ∀ {m k v}, map_to ((k, v) :: m) k v
| rst: ∀ {m p k v}, map_to m k v → map_to (p :: m) k v

inductive map_to₁ {α β: Type}: map α β → α → β → Prop
| fnd: ∀ {m k v}, map_to₁ ((k,v) :: m) k v
| rst: ∀ {m k₁ k v₁ v}, k₁ ≠ k → map_to₁ m k v → map_to₁ ((k₁,v₁) :: m) k v

inductive map_excl {α β: Type}: map α β → α → Prop
| mt : ∀ {a}, map_excl [] a
| ext: ∀ {a a₁ b₁ m}, a ≠ a₁ → map_excl m a → map_excl ((a₁,b₁) :: m) a 

lemma excl_not_map_to {α β: Type} {m: map α β} {a: α} {b: β}
  (m_a : map_to m a b)
  (m_na: map_excl m a):
  false :=
begin induction m_a,
  {cases m_na, contradiction},
  {cases m_na, exact ih_1 (by assumption)}
end

def ext_map {α β: Type} (m: map α β) (k: α) (v: β) := (k, v) :: m
attribute [reducible] ext_map

lemma excl_implies_ineq {α β: Type} {m: map α β} {a a': α} {b: β}
  (mem : map_to m a b)
  (excl: map_excl m a'):
  a' ≠ a :=
begin induction mem,
  {cases excl, assumption},
  {cases excl, apply ih_1, assumption}
end

lemma excl_implies_ineq₁ {α β: Type} {m: map α β} {a a': α} {b: β}
  (mem : map_to₁ m a b)
  (excl: map_excl m a'):
  a' ≠ a :=
begin induction mem,
  {cases excl, assumption},
  {cases excl, apply ih_1, assumption}
end

lemma ext_preserves_map_to {α β: Type} [decidable_eq α] {m: map α β} {a a': α} {b b': β}
  (m_a: map_to m a b):
  map_to (ext_map m a' b') a b :=
map_to.rst m_a

lemma map_to₁_unique {α β: Type} {m: map α β} {a: α} {b₁ b₂: β}
  (map₁: map_to₁ m a b₁)
  (map₂: map_to₁ m a b₂):
  b₁ = b₂ :=
begin induction map₁,
  {cases map₂,
     {reflexivity},
     {contradiction}},
  {cases map₂,
     {contradiction},
     {exact ih_1 (by assumption)}}
end
