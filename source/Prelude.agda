module Prelude where

open import Agda.Primitive using (Level)
open import Relation.Nullary using (¬_) public
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Core using (_≢_) public
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Equality using (_≡_) public
open import Function.Base using (_∘_) public
open ≡-Reasoning public
open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω)
  renaming (lzero to ℓ₀; lsuc to next-level)
open import Function.Base using (const)
open import Relation.Binary.Core using (Rel; REL)
open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂) public
open import Data.Product.Properties public
open import Relation.Nullary using (yes; no) public
open import Data.List.Relation.Unary.Any using (here; there; Any) public
import Data.List
open import Function public
open import Data.Empty renaming (⊥-elim to ex-falso) public
open import Data.Unit using (⊤) renaming (tt to truth) public

pattern reflexivity = refl

symmetry : ∀ {universe} → {A : Set universe} → Symmetric {A = A} _≡_
symmetry = sym

transitivity : ∀ {universe} → {A : Set universe} → Transitive {A = A} _≡_
transitivity = trans

congruence : {ℓ : Level} {A B : Set ℓ} → ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruence = cong

substitute : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
substitute property refl evidence = evidence

constant : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → A → B → A
constant value = const value

Relation : {ℓ : Level} → Set ℓ → (ℓ' : Level) → Set (ℓ ⊔ next-level ℓ')
Relation = Rel

BinaryRelation : {ℓ₁ ℓ₂ : Level} → Set ℓ₁ → Set ℓ₂ → (ℓ : Level) → Set (ℓ₁ ⊔ ℓ₂ ⊔ next-level ℓ)
BinaryRelation = REL

_—_[_] = BinaryRelation

one-to-one : ∀ {source target : Set} (function : source → target) → Set
one-to-one {source} function = ∀ {x₁ x₂ : source} → function x₁ ≡ function x₂ → x₁ ≡ x₂

_∈_ : ∀ {A : Set} → A → Data.List.List A → Set
x ∈ xs = Any (x ≡_) xs

import Agda.Builtin.Nat
module ℕ where
  open import Data.Nat.Base hiding (ℕ; suc; _⊔_) public
  open import Data.Nat.Properties public
  pattern successor x = Agda.Builtin.Nat.suc x
open ℕ using ( ) renaming (zero to ℕ-zero; successor to ℕ-successor) public
ℕ : Set
ℕ = Agda.Builtin.Nat.Nat

module 𝔹 where
  open import Agda.Builtin.Bool using (Bool; false; true)
  open import Agda.Builtin.Bool using (false; true) public
  𝔹 : Set
  𝔹 = Bool
open 𝔹 using (𝔹; false; true) public

open import Data.Fin.Base
import Data.Fin
module Finite where
  open import Data.Fin hiding (suc; Fin) public
  open import Data.Fin.Properties hiding (setoid) public
  pattern successor {n} x = Data.Fin.Base.Fin.suc {n} x
open Finite using ( ) renaming (zero to Finite-zero; successor to Finite-successor) public
Finite : ℕ → Set
Finite x = Data.Fin.Base.Fin x

fork
  : {Source Index : Set} {Indexed : Index → Set}
  → (leftwards : Source → Index)
  → ((source : Source) → Indexed (leftwards source))
  → Source → Σ Index (λ index → Indexed index)
fork leftwards rightwards source = leftwards source , rightwards source
