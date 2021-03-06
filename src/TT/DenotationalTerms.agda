open import TT.DenotationalTypes
module TT.DenotationalTerms where

----------------------------------------------------------------------

data Term : Set → Set₁
eval : {A : Set} → Term A → A

----------------------------------------------------------------------

data Term where
  {- Type introduction -}
  `⊥ `⊤ `Bool `ℕ `Desc `Type : ∀{ℓ} → Term (Type ℓ)
  `μ : ∀{ℓ}
    (D : Term (Desc ℓ))
    → Term (Type ℓ)
  `Π `Σ : ∀{ℓ}
    (A : Term (Type ℓ))
    (B : ⟦ ℓ ∣ eval A ⟧ → Term (Type ℓ))
    → Term (Type ℓ)
  `⟦_⟧ᵈ : ∀{ℓ}
    (D : Term (Desc ℓ))
    (X : Term (Type ℓ))
    → Term (Type ℓ)
  `⟦_⟧ : ∀{ℓ}
    (A : Term (Type ℓ))
    → Term (Type (suc ℓ))

  {- Type elimination -}
  `elimType : ∀{ℓ}
    (P : (n : ℕ) → Type n → Term (Type ℓ))
    (p⊥ : (n : ℕ) → Term ⟦ ℓ ∣ eval (P n `⊥) ⟧)
    (p⊤ : (n : ℕ) → Term ⟦ ℓ ∣ eval (P n `⊤) ⟧)
    (pBool : (n : ℕ) → Term ⟦ ℓ ∣ eval (P n `Bool) ⟧)
    (pℕ : (n : ℕ) → Term ⟦ ℓ ∣ eval (P n `ℕ) ⟧)
    (pDesc : (n : ℕ) → Term ⟦ ℓ ∣ eval (P n `Desc) ⟧)
    (pType : (n : ℕ) → Term ⟦ ℓ ∣ eval (P n `Type) ⟧)
    (pμ : (n : ℕ) (D : Desc n) → Term ⟦ ℓ ∣ eval (P n (`μ D)) ⟧)
    (pΠ : (n : ℕ) (A : Type n) (B : ⟦ n ∣ A ⟧ → Type n)
       (rec₁ : ⟦ ℓ ∣ eval (P n A) ⟧)
       (rec₂ : (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval (P n (B a)) ⟧)
       → Term ⟦ ℓ ∣ eval (P n (`Π A B)) ⟧)
    (pΣ : (n : ℕ) (A : Type n) (B : ⟦ n ∣ A ⟧ → Type n)
       (rec₁ : ⟦ ℓ ∣ eval (P n A) ⟧)
       (rec₂ : (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval (P n (B a)) ⟧)
       → Term ⟦ ℓ ∣ eval (P n (`Σ A B)) ⟧)
    (p⟦D⟧ᵈ : (n : ℕ) (D : Desc n) (X : Type n)
       (rec : ⟦ ℓ ∣ eval (P n X) ⟧)
       → Term ⟦ ℓ ∣ eval (P n (`⟦ D ⟧ᵈ X)) ⟧)
    (p⟦A⟧ : (n : ℕ) (A : Type n)
        (rec : ⟦ ℓ ∣ eval (P n A) ⟧)
        → Term ⟦ ℓ ∣ eval (P (suc n) `⟦ A ⟧) ⟧)
    (n : Term ℕ)
    (A : Term (Type (eval n)))
    → Term ⟦ ℓ ∣ eval (P (eval n) (eval A)) ⟧

  {- Desc introduction -}
  `⊤ᵈ `Xᵈ : ∀{ℓ} → Term (Desc ℓ)
  `Πᵈ `Σᵈ : ∀{ℓ}
    (A : Term (Type ℓ))
    (B : ⟦ ℓ ∣ eval A ⟧ → Term (Desc (suc ℓ)))
    → Term (Desc (suc ℓ))

  {- Desc elimination -}
  `elimDesc : ∀{ℓ}
    (P : (n : ℕ) → Desc n → Term (Type ℓ))
    → ((n : ℕ) → Term ⟦ ℓ ∣ eval (P n `⊤) ⟧)
    → ((n : ℕ) → Term ⟦ ℓ ∣ eval (P n `X) ⟧)
    → ((n : ℕ) (A : Type n) (D : ⟦ n ∣ A ⟧ → Desc (suc n))
       (rec : (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval (P (suc n) (D a)) ⟧)
       → Term ⟦ ℓ ∣ eval (P (suc n) (`Π A D)) ⟧)
    → ((n : ℕ) (A : Type n) (D : ⟦ n ∣ A ⟧ → Desc (suc n))
       (rec : (a : ⟦ n ∣ A ⟧) → ⟦ ℓ ∣ eval (P (suc n) (D a)) ⟧)
       → Term ⟦ ℓ ∣ eval (P (suc n) (`Σ A D)) ⟧)
    → (n : Term ℕ)
    (D : Term (Desc (eval n)))
    → Term ⟦ ℓ ∣ eval (P (eval n) (eval D)) ⟧

  {- Value introduction -}
  `tt : Term ⊤
  `true `false : Term Bool
  `zero : Term ℕ
  `suc : Term ℕ → Term ℕ
  `λ : ∀{A} {B : A → Set}
    (f : (a : A) → Term (B a))
    → Term ((a : A) → B a)
  _`,_ : ∀{A B}
    (a : Term A)
    (b : Term (B (eval a)))
    → Term (Σ A B)
  `con : ∀{ℓ D}
    (x : Term (⟦ ℓ ∣ D ⟧ᵈ (μ D)))
    → Term (μ D)

  {- Value elimination -}
  `elim⊥ : ∀{A}
    → Term ⊥
    → Term A
  `elimBool : ∀{ℓ}
    (P : Bool → Term (Type ℓ))
    (pt : Term ⟦ ℓ ∣ eval (P true) ⟧)
    (pf : Term ⟦ ℓ ∣ eval (P false) ⟧)
    (b : Term Bool)
    → Term ⟦ ℓ ∣ eval (P (eval b)) ⟧
  `elimℕ : ∀{ℓ}
    (P : ℕ → Term (Type ℓ))
    (pz : Term ⟦ ℓ ∣ eval (P zero) ⟧)
    (ps : (n : ℕ) → ⟦ ℓ ∣ eval (P n) ⟧ → Term ⟦ ℓ ∣ eval (P (suc n)) ⟧)
    (n : Term ℕ)
    → Term ⟦ ℓ ∣ eval (P (eval n)) ⟧
  `proj₁ : ∀{A B}
    (ab : Term (Σ A B))
    → Term A
  `proj₂ : ∀{A B}
    (ab : Term (Σ A B))
    → Term (B (proj₁ (eval ab)))
  _`$_ : ∀{A} {B : A → Set}
    (f : Term ((a : A) → B a))
    (a : Term A)
    → Term (B (eval a))
  `des : ∀{ℓ} {D : Desc ℓ}
    → (Term (μ D))
    → Term (⟦ ℓ ∣ D ⟧ᵈ (μ D))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ = `⊥
eval `⊤ = `⊤
eval `Bool = `Bool
eval `ℕ = `ℕ
eval `Desc = `Desc
eval `Type = `Type
eval (`Π A B) = `Π (eval A) (λ a → eval (B a))
eval (`Σ A B) = `Σ (eval A) (λ a → eval (B a))
eval (`μ D) = `μ (eval D)
eval (`⟦ D ⟧ᵈ X) = `⟦ eval D ⟧ᵈ (eval X)
eval `⟦ A ⟧ = `⟦ eval A ⟧

{- Type elimination -}
eval (`elimType {ℓ = ℓ} P p⊥ p⊤ pBool pℕ pDesc pType pμ pΠ pΣ p⟦D⟧ᵈ p⟦A⟧ n A) =
  elimType (λ n A → ⟦ ℓ ∣ eval (P n A) ⟧)
    (λ n → eval (p⊥ n))
    (λ n → eval (p⊤ n))
    (λ n → eval (pBool n))
    (λ n → eval (pℕ n))
    (λ n → eval (pDesc n))
    (λ n → eval (pType n))
    (λ n D → eval (pμ n D))
    (λ n A B rec₁ rec₂ → eval (pΠ n A B rec₁ rec₂))
    (λ n A B rec₁ rec₂ → eval (pΣ n A B rec₁ rec₂))
    (λ n D X rec → eval (p⟦D⟧ᵈ n D X rec))
    (λ n A rec → eval (p⟦A⟧ n A rec))
    (eval n)
    (eval A)

{- Desc introduction -}
eval `⊤ᵈ = `⊤
eval `Xᵈ = `X
eval (`Πᵈ A D) = `Π (eval A) (λ a → eval (D a))
eval (`Σᵈ A D) = `Σ (eval A) (λ a → eval (D a))

{- Desc elimination -}
eval (`elimDesc {ℓ = ℓ} P p⊤ pX pΠ pΣ n D) =
  elimDesc (λ n D → ⟦ ℓ ∣ eval (P n D) ⟧)
    (λ n → eval (p⊤ n)) (λ n → eval (pX n))
    (λ n A D rec → eval (pΠ n A D rec))
    (λ n A D rec → eval (pΣ n A D rec))
    (eval n)
    (eval D)

{- Value introduction -}
eval `tt = tt
eval `true = true
eval `false = false
eval `zero = zero
eval (`suc n) = suc (eval n)
eval (`λ f) = λ a → eval (f a)
eval (a `, b) = eval a , eval b
eval (`con x) = con (eval x)

{- Value elimination -}
eval (`elim⊥ bot) = elim⊥ (eval bot)
eval (`elimBool {ℓ = ℓ} P pt pf b) =
  elimBool (λ b → ⟦ ℓ ∣ eval (P b) ⟧)
    (eval pt) (eval pf) (eval b)
eval (`elimℕ {ℓ = ℓ} P pz ps n) =
  elimℕ (λ n → ⟦ ℓ ∣ eval (P n) ⟧)
    (eval pz) (λ n pn → eval (ps n pn)) (eval n)
eval (`proj₁ ab) = proj₁ (eval ab)
eval (`proj₂ ab) = proj₂ (eval ab)
eval (f `$ a) = (eval f) (eval a)
eval (`des {ℓ = ℓ} x) = des {ℓ = ℓ} (eval x)

----------------------------------------------------------------------
