open import TT.DenotationalTypes
module TT.OperationalTerms where

----------------------------------------------------------------------

data Context : Set₁
Environment : Context → Set

ScopedType : Context → Set₁
ScopedType Γ = Environment Γ → Set

data Context where
  ∅ : Context
  _,_ : (Γ : Context) (A : ScopedType Γ) → Context

Environment ∅ = ⊤
Environment (Γ , A) = Σ (Environment Γ) A

data Var :  (Γ : Context) (A : ScopedType Γ) → Set₁ where
 here : ∀{Γ A} → Var (Γ , A) (λ vs → A (proj₁ vs))
 there : ∀{Γ A} {B : ScopedType Γ}
   → Var Γ A → Var (Γ , B) (λ vs → A (proj₁ vs))

lookup : ∀{Γ A} → Var Γ A → (vs : Environment Γ) → A vs
lookup here (vs , v) = v
lookup (there i) (vs , v) = lookup i vs

ScopedDesc : Context → ℕ → Set
ScopedDesc Γ ℓ = Environment Γ → Desc ℓ

ScopedType₂ : (Γ : Context) → ScopedType Γ → Set₁
ScopedType₂ Γ A = (vs : Environment Γ) → A vs → Set

----------------------------------------------------------------------

data Term (Γ : Context) : ScopedType Γ → Set₁
eval : ∀{Γ A} → Term Γ A → (vs : Environment Γ) → A vs

----------------------------------------------------------------------

data Term Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `ℕ `Desc `Type : ∀{ℓ}
    → Term Γ (const (Type ℓ))
  `μ : ∀{ℓ}
    (D : Term Γ (const (Desc ℓ)))
    → Term Γ (const (Type ℓ))
  `Π `Σ : ∀{ℓ}
    (A : Term Γ (const (Type ℓ)))
    (B : Term (Γ , λ vs → ⟦ ℓ ∣ eval A vs ⟧) (const (Type ℓ)))
    → Term Γ (const (Type ℓ))
  `⟦_⟧ᵈ : ∀{ℓ}
    (D : Term Γ (const (Desc ℓ)))
    (X : Term Γ (const (Type ℓ)))
    → Term Γ (const (Type ℓ))
  `⟦_⟧ : ∀{ℓ}
    (A : Term Γ (const (Type ℓ)))
    → Term Γ (const (Type (suc ℓ)))

  {- Type elimination -}
  `elimType : ∀{ℓ}
    (P : Term ((Γ , const ℕ) , λ { (vs , n) → Type n }) (const (Type ℓ)))
    (p⊥ : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `⊥) ⟧))
    (p⊤ : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `⊤) ⟧))
    (pBool : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `Bool) ⟧))
    (pℕ : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `ℕ) ⟧))
    (pDesc : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `Desc) ⟧))
    (pType : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `Type) ⟧))
    (pμ : Term ((Γ , const ℕ) ,
      λ { (vs , n) → Desc n })
      λ { ((vs , n) , D) → ⟦ ℓ ∣ eval P ((vs , n) , `μ D) ⟧ })
    (pΠ : Term (((((Γ , const ℕ) ,
      λ { (vs , n) → Type n }) , 
      λ { ((vs , n) , A) → ⟦ n ∣ A ⟧ → Type n }) ,
      λ { (((vs , n) , A) , B) → ⟦ ℓ ∣ eval P ((vs , n) , A) ⟧ }) ,
      λ { ((((vs , n) , A) , B) , rec₁) → (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval P ((vs , n) , B a) ⟧ })
      λ { (((((vs , n) , A) , B) , rec₁) , rec₂) → ⟦ ℓ ∣ eval P ((vs , n) , `Π A B) ⟧ })
    (pΣ : Term (((((Γ , const ℕ) ,
      λ { (vs , n) → Type n }) , 
      λ { ((vs , n) , A) → ⟦ n ∣ A ⟧ → Type n }) ,
      λ { (((vs , n) , A) , B) → ⟦ ℓ ∣ eval P ((vs , n) , A) ⟧ }) ,
      λ { ((((vs , n) , A) , B) , rec₁) → (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval P ((vs , n) , B a) ⟧ })
      λ { (((((vs , n) , A) , B) , rec₁) , rec₂) → ⟦ ℓ ∣ eval P ((vs , n) , `Σ A B) ⟧ })
    (p⟦D⟧ᵈ : Term ((((Γ , const ℕ) ,
      λ { (vs , n) → Desc n }) , 
      λ { ((vs , n) , D) → Type n }) ,
      λ { (((vs , n) , D) , X) → ⟦ ℓ ∣ eval P ((vs , n) , X) ⟧ })
      λ { ((((vs , n) , D) , X) , rec) → ⟦ ℓ ∣ eval P ((vs , n) , `⟦ D ⟧ᵈ X) ⟧ })
    (p⟦A⟧ : Term (((Γ , const ℕ) ,
      λ { (vs , n) → Type n }) , 
      λ { ((vs , n) , A) → ⟦ ℓ ∣ eval P ((vs , n) , A) ⟧ })
      λ { (((vs , n) , A) , rec) → ⟦ ℓ ∣ eval P ((vs , suc n) , `⟦ A ⟧) ⟧ })
    (n : Term Γ (const ℕ))
    (A : Term Γ (λ vs → Type (eval n vs)))
    → Term Γ (λ vs → ⟦ ℓ ∣ eval P ((vs , eval n vs) , eval A vs) ⟧)

  {- Desc introduction -}
  `⊤ᵈ `Xᵈ : ∀{ℓ}
    → Term Γ (const (Desc ℓ))
  `Πᵈ `Σᵈ : ∀{ℓ}
    (A : Term Γ (const (Type ℓ)))
    (D : Term (Γ , λ vs → ⟦ ℓ ∣ eval A vs ⟧) (const (Desc (suc ℓ))))
    → Term Γ (const (Desc (suc ℓ)))

  {- Desc elimination -}
  `elimDesc : ∀{ℓ}
    (P : Term ((Γ , const ℕ) , λ { (vs , n) → Desc n }) (const (Type ℓ)))
    (p⊤ : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `⊤) ⟧))
    (pX : Term (Γ , const ℕ) (λ vs → ⟦ ℓ ∣ eval P (vs , `X) ⟧))
    (pΠ : Term ((((Γ , const ℕ) ,
      λ { (vs , n) → Type n }) , 
      λ { ((vs , n) , A) → ⟦ n ∣ A ⟧ → Desc (suc n) }) ,
      λ { (((vs , n) , A) , D) → (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval P ((vs , suc n) , D a) ⟧ })
      λ { ((((vs , n) , A) , D) , rec) → ⟦ ℓ ∣ eval P ((vs , suc n) , `Π A D) ⟧ })
    (pΣ : Term ((((Γ , const ℕ) ,
      λ { (vs , n) → Type n }) , 
      λ { ((vs , n) , A) → ⟦ n ∣ A ⟧ → Desc (suc n) }) ,
      λ { (((vs , n) , A) , D) → (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval P ((vs , suc n) , D a) ⟧ })
      λ { ((((vs , n) , A) , D) , rec₁) → ⟦ ℓ ∣ eval P ((vs , suc n) , `Σ A D) ⟧ })
    (n : Term Γ (const ℕ))
    (D : Term Γ (λ vs → Desc (eval n vs)))
    → Term Γ (λ vs → ⟦ ℓ ∣ eval P ((vs , eval n vs) , eval D vs) ⟧)

  {- Value introduction -}
  `tt : Term Γ (const ⊤)
  `true `false : Term Γ (const Bool)
  `zero : Term Γ (const ℕ)
  `suc : Term Γ (const ℕ) → Term Γ (const ℕ)
  `λ : ∀{A} {B : ScopedType₂ Γ A}
    (f : Term (Γ , A) (λ vs → B (proj₁ vs) (proj₂ vs)))
    → Term Γ (λ vs → (v : A vs) → (B vs v))
  _`,_ : ∀{A} {B : ScopedType₂ Γ A}
    (a : Term Γ A)
    (b : Term Γ (λ vs → B vs (eval a vs)))
    → Term Γ (λ vs → Σ (A vs) (λ v → B vs v))

  {- Value elimination -}
  `var : ∀{A} (a : Var Γ A) → Term Γ A
  `elim⊥ : ∀{A ℓ}
    (P : Term Γ (const (Type ℓ)))
    (x : Term Γ (const ⊥))
    → Term Γ A
  `elimBool : ∀{ℓ}
    (P : Term (Γ , const Bool) (const (Type ℓ)))
    (pt : Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , true) ⟧))
    (pf : Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , false) ⟧))
    (b : Term Γ (const Bool))
    → Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , eval b vs) ⟧)
  `elimℕ : ∀{ℓ}
    (P : Term (Γ , const ℕ) (const (Type ℓ)))
    (pz : Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , zero) ⟧))
    (ps : Term ((Γ , const ℕ) , (λ { (vs , n)  → ⟦ ℓ ∣ eval P (vs , n) ⟧ }))
            (λ { ((vs , n) , p) → ⟦ ℓ ∣ eval P (vs , suc n) ⟧ }))
    (n : Term Γ (const ℕ))
    → Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , eval n vs) ⟧)
  _`$_ : ∀{A} {B : ScopedType₂ Γ A}
    (f : Term Γ (λ vs → (v : A vs) → (B vs v)))
    (a : Term Γ A)
    → Term Γ (λ vs → B vs (eval a vs))
  `proj₁ : ∀{A} {B : ScopedType₂ Γ A}
    (ab : Term Γ (λ vs → Σ (A vs) (B vs)))
    → Term Γ A
  `proj₂ : ∀{A} {B : ScopedType₂ Γ A}
    (ab : Term Γ (λ vs → Σ (A vs) (B vs)))
    → Term Γ (λ vs → B vs (proj₁ (eval ab vs)))
  `des : ∀{ℓ} {D : ScopedDesc Γ ℓ}
    (x : Term Γ (λ vs → μ (D vs)))
    → Term Γ (λ vs → ⟦ ℓ ∣ D vs ⟧ᵈ (μ (D vs)))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ vs = `⊥
eval `⊤ vs = `⊤
eval `Bool vs = `Bool
eval `ℕ vs = `ℕ
eval `Desc vs = `Desc
eval `Type vs = `Type
eval (`μ D) vs = `μ (eval D vs)
eval (`Π A B) vs = `Π (eval A vs) λ v → eval B (vs , v)
eval (`Σ A B) vs = `Σ (eval A vs) λ v → eval B (vs , v)
eval (`⟦ D ⟧ᵈ X) vs = `⟦ eval D vs ⟧ᵈ (eval X vs)
eval `⟦ A ⟧ vs = `⟦ eval A vs ⟧

{- Type elimination -}
eval (`elimType {ℓ} P p⊥ p⊤ pBool pℕ pDesc pType pμ pΠ pΣ p⟦D⟧ᵈ p⟦A⟧ n A) vs =
  elimType (λ n A → ⟦ ℓ ∣ eval P ((vs , n) , A) ⟧)
     (λ n → eval p⊥ (vs , n))
     (λ n → eval p⊤ (vs , n))
     (λ n → eval pBool (vs , n))
     (λ n → eval pℕ (vs , n))
     (λ n → eval pDesc (vs , n))
     (λ n → eval pType (vs , n))
     (λ n D → eval pμ ((vs , n) , D))
     (λ n A B rec₁ rec₂ → eval pΠ (((((vs , n) , A) , B) , rec₁) , rec₂))
     (λ n A B rec₁ rec₂ → eval pΣ (((((vs , n) , A) , B) , rec₁) , rec₂))
     (λ n D X rec → eval p⟦D⟧ᵈ ((((vs , n) , D) , X) , rec))
     (λ n A rec → eval p⟦A⟧ (((vs , n) , A) , rec))
     (eval n vs)
     (eval A vs)

{- Desc introduction -}
eval `⊤ᵈ vs = `⊤
eval `Xᵈ vs = `X
eval (`Πᵈ A D) vs = `Π (eval A vs) λ v → eval D (vs , v)
eval (`Σᵈ A D) vs = `Σ (eval A vs) λ v → eval D (vs , v)

{- Desc elimination -}
eval (`elimDesc {ℓ} P p⊤ pX pΠ pΣ n D) vs =
  elimDesc (λ n D → ⟦ ℓ ∣ eval P ((vs , n) , D) ⟧)
    (λ n → eval p⊤ (vs , n))
    (λ n → eval pX (vs , n))
    (λ n A D rec → eval pΠ ((((vs , n) , A) , D) , rec))
    (λ n A D rec → eval pΣ ((((vs , n) , A) , D) , rec))
    (eval n vs)
    (eval D vs)

{- Value introduction -}
eval `tt vs = tt
eval `true vs = true
eval `false vs = false
eval `zero vs = zero
eval (`suc n) vs = suc (eval n vs)
eval (`λ f) vs = λ v → eval f (vs , v)
eval (a `, b) vs = eval a vs , eval b vs

{- Value elimination -}
eval (`var i) vs = lookup i vs
eval (`elim⊥ P x) vs = elim⊥ (eval x vs)
eval (`elimBool {ℓ} P pt pf b) vs =
  elimBool (λ v → ⟦ ℓ ∣ eval P (vs , v) ⟧)
    (eval pt vs)
    (eval pf vs)
    (eval b vs)
eval (`elimℕ {ℓ} P pz ps n) vs =
  elimℕ (λ v → ⟦ ℓ ∣ eval P (vs , v) ⟧)
    (eval pz vs)
    (λ n rec → eval ps ((vs , n) , rec))
    (eval n vs)
eval (f `$ a) vs = (eval f vs) (eval a vs)
eval (`proj₁ ab) vs = proj₁ (eval ab vs)
eval (`proj₂ ab) vs = proj₂ (eval ab vs)
eval (`des {ℓ} x) vs = des {ℓ} (eval x vs)

----------------------------------------------------------------------
