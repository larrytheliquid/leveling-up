open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
module Paper.HList where

----------------------------------------------------------------------

data HList : Set₁ where
  nil : HList
  cons : (A : Set) → A → HList → HList

mapHList : (Σ Set (λ A → A) → Σ Set (λ A → A))
  → HList → HList
mapHList f nil = nil
mapHList f (cons A a xs) =
  let B , b = f (A , a) in
  cons B b (mapHList f xs)

myHList : HList
myHList = cons Bool false (cons ℕ 7 nil)

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

data HListForm (U : Universe) : Set where
  nil : HListForm U
  cons : (A : Universe.Codes U)
    → Universe.Meaning U A
    → HListForm U → HListForm U

----------------------------------------------------------------------

data TypeForm (U : Universe) : Set
⟦_/_⟧ : (U : Universe) → TypeForm U → Set

data TypeForm U where
  `⊥ `⊤ `Bool `ℕ `String `Type : TypeForm U
  `Π `Σ : (A : TypeForm U)
    (B : ⟦ U / A ⟧ → TypeForm U)
    → TypeForm U
  `HList : TypeForm U
  `⟦_⟧ : Universe.Codes U → TypeForm U

⟦ U / `⊥ ⟧ = ⊥
⟦ U / `⊤ ⟧ = ⊤
⟦ U / `Bool ⟧ = Bool
⟦ U / `ℕ ⟧ = ℕ
⟦ U / `String ⟧ = String
⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
⟦ U / `HList ⟧ = HListForm U
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
showType ℓ `HList = "Hlist"

show : (ℓ : ℕ)
  → ⟦ suc ℓ ∣ `Π `Type (λ A → `⟦ A ⟧ `→ `String) ⟧
showHList : (ℓ : ℕ)
  → ⟦ ℓ ∣ `HList `→ `String ⟧

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
show ℓ `HList xs = showHList ℓ xs

showHList ℓ nil = "nil"
showHList zero (cons () a xs)
showHList (suc ℓ) (cons A a xs) =
  "cons " ++ showType ℓ A ++ " " ++ show ℓ A a
    ++ " " ++ showHList (suc ℓ) xs

----------------------------------------------------------------------

`mapHList : (ℓ : ℕ) → ⟦ suc ℓ ∣
  (`Σ `Type `⟦_⟧ `→ `Σ `Type `⟦_⟧)
  `→ `HList `→ `HList ⟧
`mapHList ℓ f nil = nil
`mapHList ℓ f (cons A a xs) =
  let B , b = f (A , a) in
  cons B b (`mapHList ℓ f xs)

`myHList : (ℓ : ℕ) → ⟦ suc ℓ ∣ `HList ⟧
`myHList ℓ = cons `Bool false (cons `ℕ 7 nil)

`myHListShown : (ℓ : ℕ) → ⟦ suc ℓ ∣ `HList ⟧
`myHListShown ℓ = `mapHList ℓ
  (λ { (A , a) → `String , show ℓ A a  })
  (`myHList ℓ)

----------------------------------------------------------------------
