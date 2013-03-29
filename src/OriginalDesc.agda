open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
module OriginalDesc where

----------------------------------------------------------------------

data Desc : Set₁ where
  `⊤ `X : Desc
  _`⊎_ _`×_ : (D E : Desc) → Desc
  `Π `Σ : (A : Set)
    (D : A → Desc)
    → Desc

⟦_⟧ᵈ : Desc → Set → Set
⟦ `⊤ ⟧ᵈ X = ⊤
⟦ `X ⟧ᵈ X = X
⟦ D `⊎ E ⟧ᵈ X =
  Σ Bool (λ b → if b then ⟦ D ⟧ᵈ X else ⟦ E ⟧ᵈ X )
⟦ D `× E ⟧ᵈ X = Σ (⟦ D ⟧ᵈ X) (const (⟦ E ⟧ᵈ X))
⟦ `Π A D ⟧ᵈ X = (a : A) → ⟦ D a ⟧ᵈ X
⟦ `Σ A D ⟧ᵈ X = Σ A (λ a → ⟦ D a ⟧ᵈ X)

data μ (D : Desc) : Set where
  con : ⟦ D ⟧ᵈ (μ D) → μ D

----------------------------------------------------------------------

ℕD : Desc
ℕD = `⊤ `⊎ `X

μℕ : Set
μℕ = μ ℕD

myZero : μℕ
myZero = con (true , tt)

myOne : μℕ
myOne = con (false , myZero)

myTwo : μℕ
myTwo = con (false , myOne)

data WrapBool : Set where
  wrap : Bool → WrapBool

WrapBoolD : Desc
WrapBoolD = `Σ Bool (const `⊤)

μWrapBool : Set
μWrapBool = μ WrapBoolD

myWrap : μWrapBool
myWrap = con (false , tt)

postulate
  showDesc : Desc → String
  showμ : (D : Desc) → μ D → String

----------------------------------------------------------------------


