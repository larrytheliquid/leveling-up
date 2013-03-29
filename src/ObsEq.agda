open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
open import FixedHierarchy
module ObsEq where

data Propo : ℕ → Set where
  `⊥ `⊤ : ∀{ℓ} → Propo ℓ
  `Lift : ∀{ℓ} → Propo ℓ → Propo (suc ℓ)
  _`∧_ : ∀{ℓ} (P Q : Propo ℓ) → Propo ℓ
  `∀ : ∀{ℓ} (A : Type ℓ)
       (P : ⟦ ℓ ∣ A ⟧ → Propo ℓ)
       → Propo ℓ

reifyPropo : ∀{ℓ} → Propo ℓ → Type ℓ
reifyPropo `⊥ = `⊥
reifyPropo `⊤ = `⊤
reifyPropo (`Lift P) = `⟦ reifyPropo P ⟧
reifyPropo (P `∧ Q) =
  `Σ (reifyPropo P) (const (reifyPropo Q))
reifyPropo (`∀ A Q) = `Π A (λ a → reifyPropo (Q a))

_`⇒_ : ∀{ℓ} (P Q : Propo ℓ) → Propo ℓ
P `⇒ Q = `∀ (reifyPropo P) (const Q)

Proof : ∀{ℓ} → Propo ℓ → Set
Proof {ℓ} P = ⟦ ℓ ∣ reifyPropo P ⟧

ObsEq : (ℓ : ℕ) (A B : Type ℓ) → Propo ℓ
obsEq : (ℓ : ℕ) (A : Type ℓ) → ⟦ ℓ ∣ A ⟧
  → (B : Type ℓ) → ⟦ ℓ ∣ B ⟧ → Propo ℓ

ObsEq ℓ `⊥ `⊥ = `⊤
ObsEq ℓ `⊤ `⊤ = `⊤
ObsEq ℓ `Bool `Bool = `⊤
ObsEq ℓ `ℕ `ℕ = `⊤
ObsEq ℓ `String `String = `⊤
ObsEq ℓ `Type `Type = `⊤
ObsEq ℓ (`Π A B) (`Π A′ B′) =
  ObsEq ℓ A′ A `∧
  `∀ A λ a → `∀ A′ λ a′
  →  obsEq ℓ A′ a′ A a
  `⇒ ObsEq ℓ (B a) (B′ a′)
ObsEq ℓ (`Σ A B) (`Σ A′ B′) =
  ObsEq ℓ A A′ `∧
  `∀ A λ a → `∀ A′ λ a′
  →  obsEq ℓ A a A′ a′
  `⇒ ObsEq ℓ (B a) (B′ a′)
ObsEq zero `⟦ () ⟧ `⟦ () ⟧
ObsEq (suc ℓ) `⟦ A ⟧ `⟦ A′ ⟧ = `Lift (ObsEq ℓ A A′)
ObsEq ℓ A B = `⊥

obsEq ℓ `⊥ () `⊥ ()
obsEq ℓ `⊤ tt `⊤ tt = `⊤
obsEq ℓ `Bool true `Bool true = `⊤
obsEq ℓ `Bool false `Bool false = `⊤
obsEq ℓ `ℕ zero `ℕ zero = `⊤
obsEq ℓ `ℕ (suc n) `ℕ (suc n′) = obsEq ℓ `ℕ n `ℕ n′
obsEq ℓ `String str `String str′ =
  if str == str′ then `⊤ else `⊥
obsEq zero `Type () `Type ()
obsEq (suc ℓ) `Type A `Type A′ = `Lift (ObsEq ℓ A A′)
obsEq ℓ (`Π A B) f (`Π A′ B′) f′ =
  `∀ A λ a → `∀ A′ λ a′
  →  obsEq ℓ A′ a′ A a
  `⇒ obsEq ℓ (B a) (f a) (B′ a′) (f′ a′)
obsEq ℓ (`Σ A B) (a , b) (`Σ A′ B′) (a′ , b′) =
  obsEq ℓ A a A′ a′ `∧ obsEq ℓ (B a) b (B′ a′) b′
obsEq zero `⟦ () ⟧ a `⟦ () ⟧ b
obsEq (suc ℓ) `⟦ A ⟧ a `⟦ B ⟧ b =
  `Lift (obsEq ℓ A a B b)
obsEq ℓ A a B b = `⊥
