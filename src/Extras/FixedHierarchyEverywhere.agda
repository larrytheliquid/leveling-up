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
module Extras.FixedHierarchyEverywhere where

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

everyType : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Π (`Π `Type (λ B → `⟦ B ⟧ `→ `⟦ B ⟧)) (λ act →
  `Type `→ `Type) ⟧
every : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Π (`Π `Type (λ B → `⟦ B ⟧ `→ `⟦ B ⟧)) (λ act →
  `Π `Type (λ A → `⟦ A ⟧ `→ `⟦ everyType ℓ act A ⟧)) ⟧

everyType ℓ act (`Fin n) =
  (`Fin n `→ `Fin (act `ℕ n)) `→
  `Fin (act `ℕ n)
everyType ℓ act (`Even n) =
  (`Even n `→ `Even (act `ℕ n)) `→
  `Even (act `ℕ n)
everyType ℓ act (`Odd n) =
  (`Odd n `→ `Odd (act `ℕ n)) `→
  `Odd (act `ℕ n)
everyType ℓ act (`Π A B) =
  `Π (everyType ℓ act A `→ A) λ f →
  `Π (everyType ℓ act A) λ a →
  everyType ℓ act (B (f a))
everyType ℓ act (`Σ A B) =
  `Π (everyType ℓ act A `→ A) λ f →
  `Π A (λ a → B a `→ B (f (every ℓ act A a))) `→ 
  `Σ (everyType ℓ act A) λ a →
  everyType ℓ act (B (f a))
everyType ℓ act (`Id A x y) = `Id (everyType ℓ act A) (every ℓ act A x) (every ℓ act A y)
everyType zero act `⟦ () ⟧
everyType (suc ℓ) act `⟦ A ⟧ = `⟦ everyType ℓ (λ B b → act `⟦ B ⟧ b) A ⟧
everyType ℓ act `⊥ = `⊥
everyType ℓ act `⊤ = `⊤
everyType ℓ act `Bool = `Bool
everyType ℓ act `ℕ = `ℕ
everyType ℓ act `Type = `Type

every ℓ act (`Fin n) i = λ f → act (`Fin (act `ℕ n)) (f i)
every ℓ act (`Even n) i = λ f → act (`Even (act `ℕ n)) (f i)
every ℓ act (`Odd n) i = λ f → act (`Odd (act `ℕ n)) (f i)

every ℓ act (`Π A B) f = λ g a → every ℓ act (B (g a)) (f (g a))

every ℓ act (`Σ A B) (a , b) = 
  λ f g →
  every ℓ act A a ,
  every ℓ act (B (f (every ℓ act A a))) (g a b)

every zero act `⟦ () ⟧ a
every (suc ℓ) act `⟦ A ⟧ a = act
  (everyType (suc ℓ) act `⟦ A ⟧)
  (every ℓ (λ B b → act `⟦ B ⟧ b) A a)

every ℓ act (`Id A .a a) refl = refl

every zero act `Type ()
every (suc ℓ) act `Type A = act `Type
  (everyType ℓ (λ B b → act `⟦ B ⟧ b) A)

every ℓ act `⊥ ()
every ℓ act `⊤ tt = tt
every ℓ act `Bool b = act `Bool b
every ℓ act `ℕ n = act `ℕ n

----------------------------------------------------------------------

`double : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Π `Type (λ A → `⟦ A ⟧ `→ `⟦ A ⟧) ⟧
`double ℓ `ℕ n = n + n
`double ℓ A a = a

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

`fun-result : (ℓ : ℕ) → ⟦ ℓ ∣ everyType ℓ (`double ℓ) (`Fun ℓ) ⟧
`fun-result ℓ = every ℓ (`double ℓ) (`Fun ℓ) (`fun ℓ)

`fun-result-satisfied : (ℓ : ℕ) → ⟦ ℓ ∣
  `Π (everyType ℓ (`double ℓ) (`Fin 2)) (λ f →
  everyType ℓ (`double ℓ) (`Choice ℓ (`half ℓ (f (`dub ℓ))))) ⟧
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

`pair-result : (ℓ : ℕ) → ⟦ ℓ ∣ everyType ℓ (`double ℓ) (`Pair ℓ) ⟧
`pair-result ℓ = every ℓ (`double ℓ) (`Pair ℓ) (`pair ℓ)

`pair-result-satisfied : (ℓ : ℕ) → ⟦ ℓ ∣
  `Σ (everyType ℓ (`double ℓ) (`Fin 2)) (λ f →
  everyType ℓ (`double ℓ) (`Choice ℓ (`half ℓ (f (`dub ℓ))))) ⟧
`pair-result-satisfied ℓ = `pair-result ℓ
  (λ f → `half ℓ (f (`dub ℓ)))
  (λ i p → `inv ℓ i p)

`pair-test1 : (ℓ : ℕ) → # 3 ≡ proj₁ (`pair-result-satisfied ℓ) (`dub ℓ)
`pair-test1 ℓ = refl

`pair-test2 : (ℓ : ℕ) → 14 ≡ proj₂ (`pair-result-satisfied ℓ)
`pair-test2 ℓ = refl

----------------------------------------------------------------------
