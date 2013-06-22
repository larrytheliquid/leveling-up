open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Fin.Props
open import Data.Product
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality
module Extras.FixedHierarchy where

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

----------------------------------------------------------------------

data Even : ℕ → Set where
  ezero : Even 0
  esuc : {n : ℕ} → Even n → Even (2 + n)

data Odd : ℕ → Set where
  ozero : Odd 1
  osuc : {n : ℕ} → Odd n → Odd (2 + n)

data Id (A : Set) (a : A) : A → Set where
  refl : Id A a a

----------------------------------------------------------------------

data TypeForm (U : Universe) : Set
⟦_/_⟧ : (U : Universe) → TypeForm U → Set

data TypeForm U where
  `⊥ `⊤ `Bool `ℕ `Type : TypeForm U
  `Fin `Even `Odd : (n : ℕ) → TypeForm U
  `Π `Σ : (A : TypeForm U)
    (B : ⟦ U / A ⟧ → TypeForm U)
    → TypeForm U
  `Id : (A : TypeForm U) (x y : ⟦ U / A ⟧) → TypeForm U
  `⟦_⟧ : (A : Universe.Codes U) → TypeForm U

⟦ U / `⊥ ⟧ = ⊥
⟦ U / `⊤ ⟧ = ⊤
⟦ U / `Bool ⟧ = Bool
⟦ U / `ℕ ⟧ = ℕ
⟦ U / `Fin n ⟧ = Fin n
⟦ U / `Even n ⟧ = Even n
⟦ U / `Odd n ⟧ = Odd n
⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
⟦ U / `Id A x y ⟧ = Id ⟦ U / A ⟧ x y
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

⟦_∣_⟧ : (ℓ : ℕ) → Type ℓ → Set
⟦ ℓ ∣ A ⟧ = ⟦ Level ℓ / A ⟧

----------------------------------------------------------------------

doubleType : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Type `→ `Type ⟧
double : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Π `Type (λ A → `⟦ A ⟧ `→ `⟦ doubleType ℓ A ⟧) ⟧

doubleType ℓ (`Fin n) =
  (`Fin n `→ `Fin (n + n)) `→
  `Fin (n + n)
doubleType ℓ (`Even n) =
  (`Even n `→ `Even (n + n)) `→
  `Even (n + n)
doubleType ℓ (`Odd n) =
  (`Odd n `→ `Odd (n + n)) `→
  `Odd (n + n)
doubleType ℓ (`Π A B) =
  `Π (doubleType ℓ A `→ A) λ f →
  `Π (doubleType ℓ A) λ a →
  doubleType ℓ (B (f a))
doubleType ℓ (`Σ A B) =
  `Π (doubleType ℓ A `→ A) λ f →
  `Π A (λ a → B a `→ B (f (double ℓ A a))) `→ 
  `Σ (doubleType ℓ A) λ a →
  doubleType ℓ (B (f a))
doubleType ℓ (`Id A x y) = `Id (doubleType ℓ A) (double ℓ A x) (double ℓ A y)
doubleType zero `⟦ () ⟧
doubleType (suc ℓ) `⟦ A ⟧ = `⟦ doubleType ℓ A ⟧
doubleType ℓ A = A

double ℓ `ℕ n = n + n
double ℓ (`Fin n) i = λ f → f i
double ℓ (`Even n) i = λ f → f i
double ℓ (`Odd n) i = λ f → f i

double ℓ (`Π A B) f = λ g a → double ℓ (B (g a)) (f (g a))
double ℓ (`Σ A B) (a , b) = λ f g →
  double ℓ A a ,
  double ℓ (B (f (double ℓ A a))) (g a b)
double zero `⟦ () ⟧ a
double (suc ℓ) `⟦ A ⟧ a = double ℓ A a
double ℓ (`Id A .a a) refl = refl

double ℓ `⊥ a = a
double ℓ `⊤ a = a
double ℓ `Bool a = a
double ℓ `Type a = a

----------------------------------------------------------------------

`Choice : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Fin 2 `→ `Type ⟧
`Choice ℓ zero = `Bool
`Choice ℓ (suc zero) = `ℕ
`Choice ℓ (suc (suc ()))

----------------------------------------------------------------------

`dub : (ℓ : ℕ) → ⟦ ℓ ∣ `Fin 2 `→ `Fin 4 ⟧
`dub ℓ zero = # 2
`dub ℓ (suc zero) = # 3
`dub ℓ (suc (suc ()))

`half : (ℓ : ℕ) → ⟦ ℓ ∣ `Fin 4 `→ `Fin 2 ⟧
`half ℓ zero = # 0
`half ℓ (suc zero) = # 1
`half ℓ (suc (suc zero)) = # 0
`half ℓ (suc (suc (suc zero))) = # 1
`half ℓ (suc (suc (suc (suc ()))))

`inv : (ℓ : ℕ) → ⟦ ℓ ∣ `Π (`Fin 2) (λ i → `Choice ℓ i `→ `Choice ℓ (`half ℓ (`dub ℓ i))) ⟧
`inv ℓ zero = id
`inv ℓ (suc zero) = id
`inv ℓ (suc (suc ()))

----------------------------------------------------------------------

`Fun :  (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type ⟧
`Fun ℓ = `Π (`Fin 2) (`Choice ℓ)

`fun : (ℓ : ℕ) → ⟦ ℓ ∣ `Fun ℓ ⟧
`fun ℓ zero = true
`fun ℓ (suc zero) = 7
`fun ℓ (suc (suc ()))

`fun-result : (ℓ : ℕ) → ⟦ ℓ ∣ doubleType ℓ (`Fun ℓ) ⟧
`fun-result ℓ = double ℓ (`Fun ℓ) (`fun ℓ)

`fun-result-satisfied : (ℓ : ℕ) → ⟦ ℓ ∣
  `Π (doubleType ℓ (`Fin 2)) (λ f →
  doubleType ℓ (`Choice ℓ (`half ℓ (f (`dub ℓ))))) ⟧
`fun-result-satisfied ℓ = `fun-result ℓ
  (λ f → `half ℓ (f (`dub ℓ)))

`fun-test1 : (ℓ : ℕ) → true ≡ (`fun-result-satisfied ℓ) (const (# 0))
`fun-test1 ℓ = refl

`fun-test2 : (ℓ : ℕ) → 14 ≡ (`fun-result-satisfied ℓ) (const (# 1))
`fun-test2 ℓ = refl

`fun-test3 : (ℓ : ℕ) → true ≡ (`fun-result-satisfied ℓ) (const (# 2))
`fun-test3 ℓ = refl

`fun-test4 : (ℓ : ℕ) → 14 ≡ (`fun-result-satisfied ℓ) (const (# 3))
`fun-test4 ℓ = refl

----------------------------------------------------------------------

`Pair : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type ⟧
`Pair ℓ = `Σ (`Fin 2) (`Choice ℓ)

`pair : (ℓ : ℕ) → ⟦ ℓ ∣ `Pair ℓ ⟧
`pair ℓ = # 1 , 7

`pair-result : (ℓ : ℕ) → ⟦ ℓ ∣ doubleType ℓ (`Pair ℓ) ⟧
`pair-result ℓ = double ℓ (`Pair ℓ) (`pair ℓ)

`pair-result-satisfied : (ℓ : ℕ) → ⟦ ℓ ∣
  `Σ (doubleType ℓ (`Fin 2)) (λ f →
  doubleType ℓ (`Choice ℓ (`half ℓ (f (`dub ℓ))))) ⟧
`pair-result-satisfied ℓ = `pair-result ℓ
  (λ f → `half ℓ (f (`dub ℓ)))
  (λ i p → `inv ℓ i p)

`pair-test1 : (ℓ : ℕ) → # 3 ≡ proj₁ (`pair-result-satisfied ℓ) (`dub ℓ)
`pair-test1 ℓ = refl

`pair-test2 : (ℓ : ℕ) → 14 ≡ proj₂ (`pair-result-satisfied ℓ)
`pair-test2 ℓ = refl

----------------------------------------------------------------------
