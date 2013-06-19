open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
module Paper.Background where

mutual
  data Type : Set where
    `Bool : Type
    `Σ : (A : Type) (B : ⟦ A ⟧ → Type) → Type

  ⟦_⟧ : Type → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)

----------------------------------------------------------------------

showType : (A : Type) → String
showType `Bool = "Bool"
showType (`Σ A B) = "Σ " ++ showType A ++ " λ"

show : (A : Type) → ⟦ A ⟧ → String
show `Bool true = "true"
show `Bool false = "false"
show (`Σ A B) (a , b)
  = show A a ++ " , " ++ show (B a) b

----------------------------------------------------------------------
