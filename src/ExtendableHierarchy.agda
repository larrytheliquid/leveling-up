open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
module ExtendableHierarchy where

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

----------------------------------------------------------------------

data DescForm (U : Universe) : Set where
  `⊤ `X : DescForm U
  _`⊎_ _`×_ : (D E : DescForm U) → DescForm U
  `Π `Σ : (A : Universe.Codes U)
    (D : Universe.Meaning U A → DescForm U)
    → DescForm U

⟦_/_⟧ᵈ : (U : Universe) → DescForm U → Set → Set
⟦ U / `⊤ ⟧ᵈ X = ⊤
⟦ U / `X ⟧ᵈ X = X
⟦ U / D `⊎ E ⟧ᵈ X =
  Σ Bool (λ b → if b then ⟦ U / D ⟧ᵈ X else ⟦ U / E ⟧ᵈ X )
⟦ U / D `× E ⟧ᵈ X = Σ (⟦ U / D ⟧ᵈ X) (const (⟦ U / E ⟧ᵈ X))
⟦ U / `Π A D ⟧ᵈ X =
  (a : Universe.Meaning U A) → ⟦ U / D a ⟧ᵈ X
⟦ U / `Σ A D ⟧ᵈ X =
  Σ (Universe.Meaning U A) (λ a → ⟦ U / D a ⟧ᵈ X)

data μ {U : Universe} (D : DescForm U) : Set where
  con : ⟦ U / D ⟧ᵈ (μ D) → μ D

----------------------------------------------------------------------

data TypeForm (U : Universe) : Set
⟦_/_⟧ : (U : Universe) → TypeForm U → Set

data TypeForm U where
  `⊥ `⊤ `Bool `ℕ `String `Type : TypeForm U
  `Π `Σ : (A : TypeForm U)
    (B : ⟦ U / A ⟧ → TypeForm U)
    → TypeForm U
  `⟦_⟧ : Universe.Codes U → TypeForm U
  `Desc : TypeForm U
  `μ : DescForm U → TypeForm U

⟦ U / `⊥ ⟧ = ⊥
⟦ U / `⊤ ⟧ = ⊤
⟦ U / `Bool ⟧ = Bool
⟦ U / `ℕ ⟧ = ℕ
⟦ U / `String ⟧ = String
⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
⟦ U / `Type ⟧ = Universe.Codes U
⟦ U / `⟦ A ⟧ ⟧ = Universe.Meaning U A
⟦ U / `Desc ⟧ = DescForm U
⟦ U / `μ D ⟧ = μ D

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

Desc : ℕ → Set
Desc ℓ = DescForm (Level ℓ)

infix 0 ⟦_∣_⟧
⟦_∣_⟧ : (ℓ : ℕ) → Type ℓ → Set
⟦ ℓ ∣ A ⟧ = ⟦ Level ℓ / A ⟧

----------------------------------------------------------------------

`⟦_∣_⟧ᵈ : (ℓ : ℕ) → Desc ℓ → Type ℓ → Type ℓ
`⟦ ℓ ∣ `⊤ ⟧ᵈ X = `⊤
`⟦ ℓ ∣ `X ⟧ᵈ X = X
`⟦ ℓ ∣ D `⊎ E ⟧ᵈ X =
  `Σ `Bool
    (λ b → if b then `⟦ ℓ ∣ D ⟧ᵈ X else `⟦ ℓ ∣ E ⟧ᵈ X)
`⟦ ℓ ∣ D `× E ⟧ᵈ X =
  `Σ (`⟦ ℓ ∣ D ⟧ᵈ X) (const (`⟦ ℓ ∣ E ⟧ᵈ X))
`⟦ ℓ ∣ `Π A D ⟧ᵈ X = `Π `⟦ A ⟧ (λ a → `⟦ ℓ ∣ D a ⟧ᵈ X)
`⟦ ℓ ∣ `Σ A D ⟧ᵈ X = `Σ `⟦ A ⟧ (λ a → `⟦ ℓ ∣ D a ⟧ᵈ X)

----------------------------------------------------------------------

showType : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type `→ `String ⟧
show : (ℓ : ℕ)
  → ⟦ suc ℓ ∣ `Π `Type (λ A → `⟦ A ⟧ `→ `String) ⟧
showDesc : (ℓ : ℕ) → ⟦ ℓ ∣ `Desc `→ `String ⟧
showμ : (ℓ : ℕ)
  → ⟦ ℓ ∣ `Π `Desc (λ D → `μ D `→ `String) ⟧
show⟦D⟧ᵈ : (ℓ : ℕ)
  (D E : Desc ℓ) → ⟦ Level ℓ / D ⟧ᵈ (μ E) → String
  -- → ⟦ ℓ ∣ `Π `Desc (λ D → `Π `Desc (λ E → `⟦ ℓ ∣ D ⟧ᵈ (`μ E) `→ `String)) ⟧

show⟦D⟧ᵈ ℓ `⊤ E tt = "tt"
show⟦D⟧ᵈ ℓ `X E x = showμ ℓ E x
show⟦D⟧ᵈ ℓ (D₁ `⊎ D₂) E (true , x) =
  "inj₁ " ++ show⟦D⟧ᵈ ℓ D₁ E x
show⟦D⟧ᵈ ℓ (D₁ `⊎ D₂) E (false , x) =
  "inj₂ " ++ show⟦D⟧ᵈ ℓ D₂ E x
show⟦D⟧ᵈ ℓ (D₁ `× D₂) E (x , y) =
  show⟦D⟧ᵈ ℓ D₁ E x ++ " , " ++ show⟦D⟧ᵈ ℓ D₂ E y
show⟦D⟧ᵈ zero (`Π () D) E f
show⟦D⟧ᵈ (suc ℓ) (`Π A D) E f = "λ"
show⟦D⟧ᵈ zero (`Σ () D) E (x , y)
show⟦D⟧ᵈ (suc ℓ) (`Σ A D) E (x , y) =
  show ℓ A x ++ " , " ++ show⟦D⟧ᵈ (suc ℓ) (D x) E y

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
showType ℓ `Desc = "Desc"
showType ℓ (`μ D) = "μ " ++ showDesc ℓ D

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
show ℓ `Desc D = showDesc ℓ D
show ℓ (`μ D) x = showμ ℓ D x

showDesc ℓ `⊤ = "⊤"
showDesc ℓ `X = "X"
showDesc ℓ (D `⊎ E) = showDesc ℓ D ++ " ⊎ " ++ showDesc ℓ E
showDesc ℓ (D `× E) = showDesc ℓ D ++ " × " ++ showDesc ℓ E
showDesc zero (`Π () D)
showDesc (suc ℓ) (`Π A D) =
  "Π " ++ showType ℓ A ++ " λ"
showDesc zero (`Σ () D)
showDesc (suc ℓ) (`Σ A D) =
  "Σ " ++ showType ℓ A ++ " λ"

showμ ℓ D (con x) = show⟦D⟧ᵈ ℓ D D x

----------------------------------------------------------------------

`ℕD : (ℓ : ℕ) → ⟦ ℓ ∣ `Desc ⟧
`ℕD ℓ = `⊤ `⊎ `X

`μℕ : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type ⟧
`μℕ ℓ = `μ (`ℕD ℓ)

`myZero : (ℓ : ℕ)→ ⟦ ℓ ∣ `μ (`ℕD ℓ) ⟧
`myZero ℓ = con (true , tt)

`myOne : (ℓ : ℕ)→ ⟦ ℓ ∣ `μ (`ℕD ℓ) ⟧
`myOne ℓ = con (false , `myZero ℓ)

----------------------------------------------------------------------

`WrapBoolD : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Desc ⟧
`WrapBoolD ℓ = `Σ `Bool (const `⊤)

`μWrapBoolD : (ℓ : ℕ) → Type (suc ℓ)
`μWrapBoolD ℓ = `μ (`WrapBoolD ℓ)

`myWrap : (ℓ : ℕ) → ⟦ suc ℓ ∣ `μ (`WrapBoolD ℓ) ⟧
`myWrap ℓ = con (false , tt)

----------------------------------------------------------------------

`HListD : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Desc ⟧
`HListD ℓ = `⊤ `⊎
  `Σ `Type (λ A → `Σ `⟦ A ⟧ (const `X))

`μHList : (ℓ : ℕ) → Set
`μHList ℓ = μ (`HListD ℓ)

`myHList : (ℓ : ℕ)
  → ⟦ suc (suc ℓ) ∣ `μ (`HListD (suc ℓ)) ⟧
`myHList ℓ =
  con (false , `Bool , false ,
    con (false , `ℕ , 7 , con (true , tt)))

----------------------------------------------------------------------

`VecD : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type `→ `ℕ `→ `Desc ⟧
`VecD ℓ A zero = `⊤
`VecD ℓ A (suc n) = `Σ A (const (`VecD ℓ A n))

----------------------------------------------------------------------


