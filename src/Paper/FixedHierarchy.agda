open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
module Paper.FixedHierarchy where

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

----------------------------------------------------------------------

mutual
  data TypeForm (U : Universe) : Set where
    `⊥ `⊤ `Bool `ℕ `String `Type : TypeForm U
    `Π `Σ : (A : TypeForm U)
      (B : ⟦ U / A ⟧ → TypeForm U)
      → TypeForm U
    `⟦_⟧ : Universe.Codes U → TypeForm U

  ⟦_/_⟧ : (U : Universe) → TypeForm U → Set
  ⟦ U / `⊥ ⟧ = ⊥
  ⟦ U / `⊤ ⟧ = ⊤
  ⟦ U / `Bool ⟧ = Bool
  ⟦ U / `ℕ ⟧ = ℕ
  ⟦ U / `String ⟧ = String
  ⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
  ⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
  ⟦ U / `Type ⟧ = Universe.Codes U
  ⟦ U / `⟦ A ⟧ ⟧ = Universe.Meaning U A

----------------------------------------------------------------------

infixr 1 _`→_
_`→_ : ∀{U} (A B : TypeForm U) → TypeForm U
A `→ B = `Π A (λ _ → B)

Level : (ℓ : ℕ) → Universe
Level zero = record { Codes = ⊥ ; Meaning = λ() }
Level (suc ℓ) = record { Codes = TypeForm (Level ℓ)
                       ; Meaning = ⟦_/_⟧ (Level ℓ) }

Type : ℕ → Set
Type ℓ = TypeForm (Level ℓ)

infix 0 ⟦_∣_⟧
⟦_∣_⟧ : (ℓ : ℕ) → Type ℓ → Set
⟦ ℓ ∣ A ⟧ = ⟦ Level ℓ / A ⟧

----------------------------------------------------------------------

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

append₁ : (A : Set) (m : ℕ) (xs : Vec A m)
  (n : ℕ) (ys : Vec A n) → Vec A (m + n)
append₁ A .zero nil n ys = ys
append₁ A .(suc m) (cons m x xs) n ys =
  cons (m + n) x (append₁ A m xs n ys)

elimVec : (A : Set) (P : (n : ℕ) → Vec A n → Set)
  → P zero nil
  → ((n : ℕ) (x : A) (xs : Vec A n)
      → P n xs → P (suc n) (cons n x xs))
  → (n : ℕ) (xs : Vec A n) → P n xs
elimVec A P pn pc .zero nil = pn
elimVec A P pn pc .(suc n) (cons n x xs) =
  pc n x xs (elimVec A P pn pc n xs)

append₂ : (A : Set) (m : ℕ) (xs : Vec A m)
  (n : ℕ) (ys : Vec A n) → Vec A (m + n)
append₂ A = elimVec A
  (λ m xs → (n : ℕ) (ys : Vec A n) → Vec A (m + n))
  (λ n ys → ys)
  (λ m x xs rec n ys → cons (m + n) x (rec n ys))
  

----------------------------------------------------------------------

showType : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type `→ `String ⟧
showType ℓ `⊥ = "⊥"
showType ℓ `⊤ = "⊤"
showType ℓ `Bool = "Bool"
showType ℓ `ℕ = "ℕ"
showType ℓ `String = "String"
showType ℓ (`Π A B) = "Π " ++ showType ℓ A ++ " λ"
showType ℓ (`Σ A B) = "Σ " ++ showType ℓ A ++ " λ"
showType ℓ `Type = "Type"
showType zero `⟦ () ⟧
showType (suc ℓ) `⟦ A ⟧ = "⟦ " ++ showType ℓ A ++ " ⟧" 

show : (ℓ : ℕ)
  → ⟦ suc ℓ ∣ `Π `Type (λ A → `⟦ A ⟧ `→ `String) ⟧
show ℓ `⊥ ()
show ℓ `⊤ tt = "tt"
show ℓ `Bool true = "true"
show ℓ `Bool false = "false"
show ℓ `ℕ zero = "zero"
show ℓ `ℕ (suc n) = "suc " ++ show ℓ `ℕ n
show ℓ `String str = "\"" ++ str ++ "\""
show ℓ (`Π A B) f = "λ"
show ℓ (`Σ A B) (a , b) =
  show ℓ A a ++ " , " ++ show ℓ (B a) b
show zero `Type ()
show (suc ℓ) `Type A = showType ℓ A
show zero `⟦ () ⟧ a
show (suc ℓ) `⟦ A ⟧ a = "lift " ++ show ℓ A a

----------------------------------------------------------------------
