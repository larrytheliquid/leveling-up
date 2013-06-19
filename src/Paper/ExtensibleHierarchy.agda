open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality
module Paper.ExtensibleHierarchy where

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

----------------------------------------------------------------------

infixr 3 _`×_
data DescForm (U : Universe) : Set where
  `⊤ `X : DescForm U
  _`⊎_ _`×_ : (D E : DescForm U) → DescForm U
  `Π `Σ : (A : Universe.Codes U)
    (D : Universe.Meaning U A → DescForm U)
    → DescForm U
  `[_] : Universe.Codes U → DescForm U

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
⟦ U / `[ A ] ⟧ᵈ X = Universe.Meaning U A

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
  `⟦_⟧ᵈ : DescForm U → TypeForm U → TypeForm U
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
⟦ U / `⟦ D ⟧ᵈ X ⟧ = ⟦ U / D ⟧ᵈ ⟦ U / X ⟧
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

⟦_∣_⟧ᵈ : (ℓ : ℕ) → Desc ℓ → Type ℓ → Set
⟦ ℓ ∣ D ⟧ᵈ X = ⟦ Level ℓ / D ⟧ᵈ ⟦ ℓ ∣ X ⟧

----------------------------------------------------------------------

showType : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type `→ `String ⟧
showDesc : (ℓ : ℕ) → ⟦ ℓ ∣ `Desc `→ `String ⟧
show : (ℓ : ℕ)
  → ⟦ suc ℓ ∣ `Π `Type (λ A → `⟦ A ⟧ `→ `String) ⟧
showᵈ : (ℓ : ℕ)
  → ⟦ suc ℓ ∣ `Π `⟦ `Desc ⟧ (λ D → `Π `Type (λ X → `⟦ `⟦ D ⟧ᵈ X ⟧ `→ `String)) ⟧

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
showType ℓ (`⟦ D ⟧ᵈ X) = "⟦ " ++ showDesc ℓ D ++ " ⟧ᵈ " ++ showType ℓ X
showType ℓ (`μ D) = "μ " ++ showDesc ℓ D

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
showDesc zero `[ () ]
showDesc (suc ℓ) `[ A ] =
  "[ " ++ showType ℓ A ++ " ]"

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
show ℓ (`⟦ D ⟧ᵈ X) x = showᵈ ℓ D X x
show ℓ (`μ D) (con x) = "con " ++ showᵈ ℓ D (`μ D) x

showᵈ ℓ `⊤ X tt = "tt"
showᵈ ℓ `X X x = show ℓ X x
showᵈ ℓ (D `⊎ E) X (true , x) =
  "inj₁ " ++ showᵈ ℓ D X x
showᵈ ℓ (D `⊎ E) X (false , y) =
  "inj₂ " ++ showᵈ ℓ E X y
showᵈ ℓ (D `× E) X (x , y) =
  showᵈ ℓ D X x ++ " , " ++ showᵈ ℓ E X y
showᵈ zero (`Π () D) X f
showᵈ (suc ℓ) (`Π A D) X f = "λ"
showᵈ zero (`Σ () D) X (x , y)
showᵈ (suc ℓ) (`Σ A D) X (x , y) =
  show ℓ A x ++ " , " ++ showᵈ (suc ℓ) (D x) X y
showᵈ zero `[ () ] X x
showᵈ (suc ℓ) `[ A ] X x = show ℓ A x

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

`BinTreeBoolD : (ℓ : ℕ) → ⟦ ℓ ∣ `Desc ⟧
`BinTreeBoolD ℓ = (`⊤ `⊎ `⊤) `⊎ (`X `× `X)

`μBinTreeBool : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type ⟧
`μBinTreeBool ℓ = `μ (`BinTreeBoolD ℓ)

-- previously defined inductive or built-in types
`BinTreeℕD : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Desc ⟧
`BinTreeℕD ℓ = `Σ `ℕ (const `⊤) `× (`X `× `X)

`μBinTreeℕ : (ℓ : ℕ) → ⟦ suc (suc ℓ) ∣ `Type ⟧
`μBinTreeℕ ℓ = `μ (`BinTreeℕD ℓ)

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
`⟦ ℓ ∣ `[ A ] ⟧ᵈ X = `⟦ A ⟧

`con : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `⟦ `Desc ⟧
  (λ D → `⟦ `⟦ D ⟧ᵈ (`μ D) ⟧ `→ `⟦ `μ D ⟧) ⟧
`con ℓ D x = con x

-- `con2 : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `⟦ `Desc ⟧
--   (λ D → `⟦ `⟦ ℓ ∣ D ⟧ᵈ (`μ D) ⟧ `→ `⟦ `μ D ⟧) ⟧
-- `con2 ℓ D x = con ?

----------------------------------------------------------------------

doubleType : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type `→ `Type ⟧
doubleDesc : (ℓ : ℕ) → ⟦ ℓ ∣ `Desc `→ `Desc ⟧
double : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Type (λ A → `Π `⟦ A ⟧ (λ a → `⟦ A ⟧)) ⟧
doubleᵈ : (ℓ : ℕ)
  → ⟦ suc ℓ ∣ `Π `⟦ `Desc ⟧ (λ D →
  `Π `Type (λ X → `⟦ `⟦ D ⟧ᵈ X ⟧ `→ `⟦ `⟦ D ⟧ᵈ X ⟧)) ⟧

doubleType ℓ (`Π A B) = `Π A (λ a → doubleType ℓ (B a))
doubleType ℓ (`Σ A B) = `Σ A (λ a → doubleType ℓ (B a))
doubleType zero `⟦ () ⟧
doubleType (suc ℓ) `⟦ A ⟧ = `⟦ doubleType ℓ A ⟧
doubleType ℓ (`⟦ D ⟧ᵈ X) = `⟦ doubleDesc ℓ D ⟧ᵈ (doubleType ℓ X)
doubleType ℓ (`μ D) = `μ (doubleDesc ℓ D)
doubleType ℓ A = A

doubleDesc ℓ (D `⊎ E) = doubleDesc ℓ D `⊎ doubleDesc ℓ E
doubleDesc ℓ (D `× E) = doubleDesc ℓ D `× doubleDesc ℓ E
doubleDesc zero (`Π () D)
doubleDesc (suc ℓ) (`Π A D) = `Π A (λ a → doubleDesc (suc ℓ) (D a))
doubleDesc zero (`Σ () D)
doubleDesc (suc ℓ) (`Σ A D) = `Σ A (λ a → doubleDesc (suc ℓ) (D a))
doubleDesc zero `[ () ]
doubleDesc (suc ℓ) `[ A ] = `[ doubleType ℓ A ]
doubleDesc ℓ D = D

double ℓ `ℕ n = n + n
double ℓ (`Π A B) f = λ a → double ℓ (B a) (f a)
double ℓ (`Σ A B) (a , b) = a , double ℓ (B a) b
double zero `⟦ () ⟧ a
double (suc ℓ) `⟦ A ⟧ a = double ℓ A a
double ℓ (`⟦ D ⟧ᵈ X) x = doubleᵈ ℓ D X x
double ℓ (`μ D) (con x) = con (doubleᵈ ℓ D (`μ D) x)
double ℓ `Desc D = doubleDesc ℓ D
double zero `Type ()
double (suc ℓ) `Type A = doubleType ℓ A
double ℓ A a = a

doubleᵈ ℓ `⊤ X x = tt
doubleᵈ ℓ `X X x = double ℓ X x 
doubleᵈ ℓ (D `⊎ E) X (true , x) =
  true , doubleᵈ ℓ D X x
doubleᵈ ℓ (D `⊎ E) X (false , x) =
  false , doubleᵈ ℓ E X x
doubleᵈ ℓ (D `× E) X (x , y) =
  doubleᵈ ℓ D X x , doubleᵈ ℓ E X y
doubleᵈ zero (`Π () D) X f
doubleᵈ (suc ℓ) (`Π A D) X f =
  λ x → doubleᵈ (suc ℓ) (D x) X (f x)
doubleᵈ zero (`Σ () D) X (x , y)
doubleᵈ (suc ℓ) (`Σ A D) X (x , y) =
  x , doubleᵈ (suc ℓ) (D x) X y
doubleᵈ zero `[ () ] X x
doubleᵈ (suc ℓ) `[ A ] X x =
  double ℓ A x

----------------------------------------------------------------------

δoubleType : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Type `→ `Type ⟧
δoubleDesc : (ℓ : ℕ) → ⟦ ℓ ∣ `Desc `→ `Desc ⟧
δouble : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Π `Type (λ A → `⟦ A ⟧ `→ `⟦ δoubleType ℓ A ⟧) ⟧
δoubleᵈ : (ℓ : ℕ) → ⟦ suc ℓ ∣
  `Π `⟦ `Desc ⟧ (λ D → `Π `Type (λ X →
  `⟦ `⟦ D ⟧ᵈ X ⟧ `→
  `⟦ `⟦ δoubleDesc ℓ D ⟧ᵈ (δoubleType ℓ X) ⟧)) ⟧

δoubleType ℓ (`Π A B) = `Π (δoubleType ℓ A `→ A) (λ f → `Π (δoubleType ℓ A) (λ a → δoubleType ℓ (B (f a))))
δoubleType ℓ (`Σ A B) = `Σ A (λ a → `Σ (δoubleType ℓ A) (λ _ → δoubleType ℓ (B a)))
δoubleType zero `⟦ () ⟧
δoubleType (suc ℓ) `⟦ A ⟧ = `⟦ δoubleType ℓ A ⟧
δoubleType ℓ (`⟦ D ⟧ᵈ X) = `⟦ δoubleDesc ℓ D ⟧ᵈ (δoubleType ℓ X)
δoubleType ℓ (`μ D) = `μ (δoubleDesc ℓ D)
δoubleType ℓ A = A

δoubleDesc ℓ (D `⊎ E) = δoubleDesc ℓ D `⊎ δoubleDesc ℓ E
δoubleDesc ℓ (D `× E) = δoubleDesc ℓ D `× δoubleDesc ℓ E
δoubleDesc zero (`Π () D)
δoubleDesc (suc ℓ) (`Π A D) = `Π (δoubleType ℓ A `→ A) (λ f → `Π (δoubleType ℓ A) (λ a → δoubleDesc (suc ℓ) (D (f a))))
δoubleDesc zero (`Σ () D)
δoubleDesc (suc ℓ) (`Σ A D) = `Σ A (λ a → `Σ (δoubleType ℓ A) (λ _ → δoubleDesc (suc ℓ) (D a)))
δoubleDesc zero `[ () ]
δoubleDesc (suc ℓ) `[ A ] = `[ δoubleType ℓ A ]
δoubleDesc ℓ D = D

δouble ℓ `ℕ n = n + n
δouble ℓ (`Π A B) f = λ g a → δouble ℓ (B (g a)) (f (g a))
δouble ℓ (`Σ A B) (a , b) = a , δouble ℓ A a , δouble ℓ (B a) b
δouble zero `⟦ () ⟧ a
δouble (suc ℓ) `⟦ A ⟧ a = δouble ℓ A a
δouble ℓ (`⟦ D ⟧ᵈ X) x = δoubleᵈ ℓ D X x
δouble ℓ (`μ D) (con x) = con (δoubleᵈ ℓ D (`μ D) x)
δouble ℓ `Desc D = δoubleDesc ℓ D
δouble zero `Type ()
δouble (suc ℓ) `Type A = δoubleType ℓ A
δouble ℓ `⊥ a = a
δouble ℓ `⊤ a = a
δouble ℓ `Bool a = a
δouble ℓ `String a = a

δoubleᵈ ℓ `⊤ X x = tt
δoubleᵈ ℓ `X X x = δouble ℓ X x 
δoubleᵈ ℓ (D `⊎ E) X (true , x) =
  true , δoubleᵈ ℓ D X x
δoubleᵈ ℓ (D `⊎ E) X (false , x) =
  false , δoubleᵈ ℓ E X x
δoubleᵈ ℓ (D `× E) X (x , y) =
  δoubleᵈ ℓ D X x , δoubleᵈ ℓ E X y
δoubleᵈ zero (`Π () D) X f
δoubleᵈ (suc ℓ) (`Π A D) X f =
  λ g a → δoubleᵈ (suc ℓ) (D (g a)) X (f (g a))
δoubleᵈ zero (`Σ () D) X (x , y)
δoubleᵈ (suc ℓ) (`Σ A D) X (x , y) =
  x , δouble ℓ A x , δoubleᵈ (suc ℓ) (D x) X y
δoubleᵈ zero `[ () ] X x
δoubleᵈ (suc ℓ) `[ A ] X x = δouble ℓ A x

----------------------------------------------------------------------

record Generic (ℓ : ℕ) : Set where
  field
    GType : ⟦ 2 + ℓ ∣ `Type `→ `Type ⟧
    gType : ⟦ 1 + ℓ ∣ `Π `Type (λ A → GType `⟦ A ⟧) ⟧

    GDesc : ⟦ 1 + ℓ ∣ `⟦ `Desc ⟧ `→ `Type ⟧
    gDesc : ⟦ 0 + ℓ ∣ `Π `Desc (λ D → GDesc D) ⟧

    GVal  : ⟦ 2 + ℓ ∣ `Π `Type (λ A → `⟦ A ⟧ `→ `Type) ⟧
    gVal  : ⟦ 1 + ℓ ∣ `Π `Type (λ A → `Π `⟦ A ⟧ (λ a → GVal `⟦ A ⟧ a)) ⟧

    GValᵈ : ⟦ 1 + ℓ ∣ `Π `⟦ `Desc ⟧ (λ D → `Π `Type (λ X → `⟦ `⟦ D ⟧ᵈ X ⟧ `→ `Type)) ⟧
    gValᵈ : ⟦ 1 + ℓ ∣ `Π `⟦ `Desc ⟧ (λ D → `Π `Type (λ X → `Π `⟦ `⟦ D ⟧ᵈ X ⟧ (λ x → `⟦ GValᵈ D X x ⟧))) ⟧

----------------------------------------------------------------------

gshow : (ℓ : ℕ) → Generic ℓ
gshow ℓ = record {
    GType = λ A → `String
  ; gType = showType ℓ
  ; GDesc = λ D → `String
  ; gDesc = showDesc ℓ
  ; GVal  = λ A a → `String 
  ; gVal = show ℓ
  ; GValᵈ = λ D X x → `String
  ; gValᵈ = showᵈ ℓ
  }

gdouble : (ℓ : ℕ) → Generic ℓ
gdouble ℓ = record {
    GType = λ A → `Type
  ; gType = doubleType ℓ
  ; GDesc = λ D → `Desc
  ; gDesc = doubleDesc ℓ
  ; GVal  = λ A a → A
  ; gVal = double ℓ
  ; GValᵈ = λ D X x → `⟦ D ⟧ᵈ X
  ; gValᵈ = doubleᵈ ℓ
  }

gδouble : (ℓ : ℕ) → Generic ℓ
gδouble ℓ = record {
    GType = λ A → `Type
  ; gType = δoubleType ℓ
  ; GDesc = λ D → `Desc
  ; gDesc = δoubleDesc ℓ
  ; GVal  = λ A a → δoubleType (suc ℓ) A
  ; gVal = δouble ℓ
  ; GValᵈ = λ D X x → `⟦ δoubleDesc ℓ D ⟧ᵈ (δoubleType ℓ X)
  ; gValᵈ = δoubleᵈ ℓ
  }

----------------------------------------------------------------------

record GenericΔ (ℓ : ℕ) : Set where
  field
    gType : ⟦ suc ℓ ∣ `Type `→ `Type ⟧
    gDesc : ⟦ ℓ ∣ `Desc `→ `Desc ⟧

    gVal : ⟦ suc ℓ ∣ `Π `Type (λ A → `⟦ A ⟧ `→ `⟦ gType A ⟧) ⟧
    gValᵈ : ⟦ suc ℓ ∣ `Π `⟦ `Desc ⟧ (λ D → `Π `Type (λ X → `⟦ `⟦ D ⟧ᵈ X ⟧ `→ `⟦ `⟦ gDesc D ⟧ᵈ (gType X) ⟧)) ⟧

----------------------------------------------------------------------

gdoubleΔ : (ℓ : ℕ) → GenericΔ ℓ
gdoubleΔ ℓ = record {
    gType = id
  ; gDesc = id
  ; gVal = double ℓ
  ; gValᵈ = doubleᵈ ℓ
  }

gδoubleΔ : (ℓ : ℕ) → GenericΔ ℓ
gδoubleΔ ℓ = record {
    gType = δoubleType ℓ
  ; gDesc = δoubleDesc ℓ
  ; gVal = δouble ℓ
  ; gValᵈ = δoubleᵈ ℓ
  }

----------------------------------------------------------------------

Eg₁ : (ℓ : ℕ) → ⟦ 2 + ℓ ∣ `Type ⟧
Eg₁ ℓ = `μ (`[ `ℕ ] `× `[ `Bool ] `× `[ `ℕ ])

eg₁ : (ℓ : ℕ) → ⟦ suc ℓ ∣ Eg₁ ℓ ⟧
eg₁ ℓ = con (1 , true , 3)

eg₁′ : (ℓ : ℕ) → ⟦ suc ℓ ∣ Eg₁ ℓ ⟧
eg₁′ ℓ = double (suc ℓ) (Eg₁ ℓ) (eg₁ ℓ)

test-eg₁ : (ℓ : ℕ) → eg₁′ ℓ ≡ con (2 , true , 6)
test-eg₁ ℓ = refl

----------------------------------------------------------------------

isOne : (ℓ : ℕ) → ⟦ suc ℓ ∣ `ℕ `→ `Bool  ⟧
isOne ℓ (suc zero) = true
isOne ℓ _ = false

Eg₂ : (ℓ : ℕ) → ⟦ 2 + ℓ ∣ `Type ⟧
Eg₂ ℓ = `Σ `ℕ (λ b → if isOne ℓ b then `ℕ else `⊥)

eg₂ : (ℓ : ℕ) → ⟦ suc ℓ ∣ Eg₂ ℓ  ⟧
eg₂ ℓ = 1 , 3

Eg₂′ : (ℓ : ℕ) → ⟦ 2 + ℓ ∣ `Type ⟧
Eg₂′ ℓ = δoubleType (suc ℓ) (Eg₂ ℓ)

eg₂′ : (ℓ : ℕ) → ⟦ suc ℓ ∣ Eg₂′ ℓ ⟧
eg₂′ ℓ = δouble (suc ℓ) (Eg₂ ℓ) (eg₂ ℓ)

test-eg₂′ : (ℓ : ℕ) → eg₂′ ℓ ≡ (1 , 2 , 6)
test-eg₂′ ℓ = refl

----------------------------------------------------------------------

