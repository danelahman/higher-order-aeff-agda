open import AEff
open import EffectAnnotations
open import Types hiding (``)

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)

module Renamings where

-- SET OF RENAMINGS BETWEEN CONTEXTS

data Ren : Ctx → Ctx → Set where
  ! : {Γ' : Ctx} → Ren [] Γ'
  ⟨_,_⟩ : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → X ∈ Γ' → Ren (Γ ∷ X) Γ'
  π : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → Ren Γ (Γ' ∷ X)
  φ : {Γ Γ' : Ctx} → Ren Γ Γ' → Ren (Γ ■) (Γ' ■)
  η : {Γ : Ctx} → Ren (Γ ■) Γ
  μ : {Γ : Ctx} → Ren (Γ ■) (Γ ■ ■)
  _∘_ : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ'' 


-- RENAMING VARIABLES

ren-var : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → X ∈ Γ → X ∈ Γ'
ren-var ⟨ f , x ⟩ Hd =
  x
ren-var (π f) Hd =
  Tl-v (ren-var f Hd)
ren-var (g ∘ f) Hd =
  ren-var g (ren-var f Hd)
ren-var ⟨ f , x ⟩ (Tl-v y) =
  ren-var f y
ren-var (π f) (Tl-v x) =
  Tl-v (ren-var f (Tl-v x))
ren-var (g ∘ f) (Tl-v x) =
  ren-var g (ren-var f (Tl-v x))
ren-var (π f) (Tl-■ p x) =
  Tl-v (ren-var f (Tl-■ p x))
ren-var (φ f) (Tl-■ p x) =
  Tl-■ p (ren-var f x)
ren-var η (Tl-■ p x) =
  x
ren-var μ (Tl-■ p x) =
  Tl-■ p (Tl-■ p x)
ren-var (g ∘ f) (Tl-■ p x) = {!!}

{-

-- IDENTITY RENAMING

id-ren : {Γ : Ctx} → Ren Γ Γ 
id-ren {[]} = !
id-ren {Γ ∷ X} = ⟨ π id-ren , Hd ⟩
id-ren {Γ ■} = φ id-ren


-- WEAKENING OF RENAMINGS

ren-wk₁ : {Γ : Ctx} {X : VType} → Ren Γ (Γ ∷ X)
ren-wk₁ {[]} = !
ren-wk₁ {Γ ∷ X} = π ⟨ ren-wk₁ , Hd ⟩
ren-wk₁ {Γ ■} = π (φ id-ren)

ren-wk₂ : {Γ : Ctx} {X Y Z : VType} → Ren (Γ ∷ Y ∷ Z) (Γ ∷ X ∷ Y ∷ Z)
ren-wk₂ = ⟨ π ⟨ π ren-wk₁ , Hd ⟩ , Hd ⟩


-- CONGRUENCE OF RENAMINGS

ren-cong : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
ren-cong ! = ⟨ ! , Hd ⟩
ren-cong ⟨ f , x ⟩ = ⟨ π ⟨ f , x ⟩ , Hd ⟩
ren-cong (π f) = ⟨ π (π f) , Hd ⟩
ren-cong (φ f) = ⟨ π (φ f) , Hd ⟩
ren-cong η = ⟨ π η , Hd ⟩
ren-cong μ = ⟨ π μ , Hd ⟩


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  V-rename : {X : VType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
  V-rename f (` x) = ` ren-var f x
  V-rename f (`` c) = `` c
  V-rename f (ƛ M) = ƛ (M-rename (ren-cong f) M)
  V-rename f ⟨ V ⟩ = ⟨ V-rename f V ⟩
  V-rename f [ V ] = [ V-rename (φ f) V ]

  M-rename : {C : CType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢M⦂ C → Γ' ⊢M⦂ C
  M-rename f (return V) =
    return (V-rename f V)
  M-rename f (let= M `in N) =
    let= M-rename f M `in M-rename (ren-cong f) N
  M-rename f (letrec M `in N) =
    letrec M-rename (ren-cong (ren-cong f)) M `in M-rename (ren-cong f) N
  M-rename f (V · W) =
    V-rename f V · V-rename f W
  M-rename f (↑ op p V M) =
    ↑ op p (V-rename f V) (M-rename f M)
  M-rename f (↓ op V M) =
    ↓ op (V-rename f V) (M-rename f M)
  M-rename f (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ M-rename (ren-cong f) M `in M-rename (ren-cong f) N
  M-rename f (await V until M) =
    await (V-rename f V) until (M-rename (ren-cong f) M)
  M-rename f (unbox V `in M) =
    unbox (V-rename f V) `in (M-rename (ren-cong f) M)
  M-rename f (coerce p q M) =
    coerce p q (M-rename f M)


-- ACTION OF RENAMING ON WELL-TYPED PROCESSES

P-rename : {o : O} {PP : PType o} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢P⦂ PP → Γ' ⊢P⦂ PP
P-rename f (run M) =
  run (M-rename f M)
P-rename f (P ∥ Q) =
  P-rename f P ∥ P-rename f Q
P-rename f (↑ op p V P) =
  ↑ op p (V-rename f V) (P-rename f P)
P-rename f (↓ op V P) =
  ↓ op (V-rename f V) (P-rename f P)

-}


{-
-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ → X ∈ Γ'


-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

id-ren : {Γ : Ctx} → Ren Γ Γ 
id-ren {Γ} x = x

comp-ren : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ'' 
comp-ren f g x = f (g x)

exchange : {Γ : Ctx} {X Y : VType} → Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)
exchange Hd = Tl-v Hd
exchange (Tl-v Hd) = Hd
exchange (Tl-v (Tl-v x)) = Tl-v (Tl-v x)


-- WEAKENING OF RENAMINGS

ren-wk₁ : {Γ : Ctx} {X : VType} → Ren Γ (Γ ∷ X)
ren-wk₁ = Tl-v

ren-wk₂ : {Γ : Ctx} {X Y Z : VType} → Ren (Γ ∷ Y ∷ Z) (Γ ∷ X ∷ Y ∷ Z)
ren-wk₂ Hd = Hd
ren-wk₂ (Tl-v Hd) = Tl-v Hd
ren-wk₂ (Tl-v (Tl-v x)) = Tl-v (Tl-v (Tl-v x))


-- STRENGTHENING OF RENAMINGS

ren-str₁ : {Γ : Ctx} → Ren (Γ ■) Γ
ren-str₁ (Tl-■ p x) = x

ren-str₂ : {Γ : Ctx} → Ren (Γ ■) (Γ ■ ■)
ren-str₂ (Tl-■ p x) = Tl-■ p (Tl-■ p x)


-- CONGRUENCE OF RENAMINGS

ren-cong₁ : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
ren-cong₁ f Hd = Hd
ren-cong₁ f (Tl-v v) = Tl-v (f v)

ren-cong₂ : {Γ Γ' : Ctx} → Ren Γ Γ' → Ren (Γ ■) (Γ' ■)
ren-cong₂ f (Tl-■ p x) = Tl-■ p (f x)


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  V-rename : {X : VType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
  V-rename f (` x) = ` f x
  V-rename f (`` c) = `` c
  V-rename f (ƛ M) = ƛ (M-rename (ren-cong₁ f) M)
  V-rename f ⟨ V ⟩ = ⟨ V-rename f V ⟩
  V-rename f [ V ] = [ V-rename (ren-cong₂ f) V ]

  M-rename : {C : CType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢M⦂ C → Γ' ⊢M⦂ C
  M-rename f (return V) =
    return (V-rename f V)
  M-rename f (let= M `in N) =
    let= M-rename f M `in M-rename (ren-cong₁ f) N
  M-rename f (letrec M `in N) =
    letrec M-rename (ren-cong₁ (ren-cong₁ f)) M `in M-rename (ren-cong₁ f) N
  M-rename f (V · W) =
    V-rename f V · V-rename f W
  M-rename f (↑ op p V M) =
    ↑ op p (V-rename f V) (M-rename f M)
  M-rename f (↓ op V M) =
    ↓ op (V-rename f V) (M-rename f M)
  M-rename f (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ M-rename (ren-cong₁ f) M `in M-rename (ren-cong₁ f) N
  M-rename f (await V until M) =
    await (V-rename f V) until (M-rename (ren-cong₁ f) M)
  M-rename f (unbox V `in M) =
    unbox (V-rename f V) `in (M-rename (ren-cong₁ f) M)
  M-rename f (coerce p q M) =
    coerce p q (M-rename f M)


-- ACTION OF RENAMING ON WELL-TYPED PROCESSES

P-rename : {o : O} {PP : PType o} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢P⦂ PP → Γ' ⊢P⦂ PP
P-rename f (run M) =
  run (M-rename f M)
P-rename f (P ∥ Q) =
  P-rename f P ∥ P-rename f Q
P-rename f (↑ op p V P) =
  ↑ op p (V-rename f V) (P-rename f P)
P-rename f (↓ op V P) =
  ↓ op (V-rename f V) (P-rename f P)

-}
