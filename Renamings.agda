open import AEff
open import EffectAnnotations
open import Types hiding (``)

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)

module Renamings where

-- SET OF RENAMINGS BETWEEN CONTEXTS

data Ren : Ctx → Ctx → Set where

  ⟨_,_⟩ : {Γ Γ' : Ctx} {X : VType} →
          Ren Γ Γ' →
          X ∈ Γ' →
          --------------------------
          Ren (Γ ∷ X) Γ'
          
  ε     : {Γ' : Ctx} →
          ------------
          Ren [] Γ'
  
  π     : {Γ Γ' : Ctx} {X : VType} →
          Ren Γ Γ' →
          --------------------------
          Ren Γ (Γ' ∷ X)
  
  φ     : {Γ Γ' : Ctx} →
          Ren Γ Γ' →
          ----------------
          Ren (Γ ■) (Γ' ■)


-- RENAMING VARIABLES

ren-var : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → X ∈ Γ → X ∈ Γ'
ren-var ⟨ f , x ⟩ Hd =
  x
ren-var (π f) Hd =
  Tl-v (ren-var f Hd)
ren-var ⟨ f , x₁ ⟩ (Tl-v x) =
  ren-var f x
ren-var (π f) (Tl-v x) =
  Tl-v (ren-var f (Tl-v x))
ren-var (π f) (Tl-■ x x₁) =
  Tl-v (ren-var f (Tl-■ x x₁))
ren-var (φ f) (Tl-■ x x₁) =
  Tl-■ x (ren-var f x₁)


-- IDENTITY RENAMING

id-ren : {Γ : Ctx} → Ren Γ Γ 
id-ren {[]} =
  ε
id-ren {Γ ∷ X} =
  ⟨ π id-ren , Hd ⟩
id-ren {Γ ■} =
  φ id-ren


-- COMPOSITION OF RENAMINGS

comp-ren : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
comp-ren g ⟨ f , x ⟩ =
  ⟨ comp-ren g f , ren-var g x ⟩
comp-ren g ε =
  ε
comp-ren ⟨ g , x ⟩ (π f) =
  comp-ren g f
comp-ren (π g) (π f) =
  π (comp-ren g (π f))
comp-ren (π g) (φ f) =
  π (comp-ren g (φ f))
comp-ren (φ g) (φ f) =
  φ (comp-ren g f)


-- WEAKENING OF RENAMINGS

ren-wk₁ : {Γ : Ctx} {X : VType} → Ren Γ (Γ ∷ X)
ren-wk₁ {[]} =
  ε
ren-wk₁ {Γ ∷ X} =
  π ⟨ ren-wk₁ , Hd ⟩
ren-wk₁ {Γ ■} =
  π (φ id-ren)
  
ren-wk₂ : {Γ : Ctx} {X Y Z : VType} → Ren (Γ ∷ Y ∷ Z) (Γ ∷ X ∷ Y ∷ Z)
ren-wk₂ =
  ⟨ π ⟨ π ren-wk₁ , Hd ⟩ , Hd ⟩


-- CONGRUENCE OF RENAMINGS

ren-cong : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
ren-cong ε =
  ⟨ ε , Hd ⟩
ren-cong ⟨ f , x ⟩ =
  ⟨ π ⟨ f , x ⟩ , Hd ⟩
ren-cong (π f) =
  ⟨ π (π f) , Hd ⟩
ren-cong (φ f) =
  ⟨ π (φ f) , Hd ⟩


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  V-rename : {X : VType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
  V-rename f (` x) = ` ren-var f x
  V-rename f (´ c) = ´ c
  V-rename f (ƛ M) = ƛ (C-rename (ren-cong f) M)
  V-rename f ⟨ V ⟩ = ⟨ V-rename f V ⟩
  V-rename f (□ V) = □ (V-rename (φ f) V)

  C-rename : {C : CType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C
  C-rename f (return V) =
    return (V-rename f V)
  C-rename f (let= M `in N) =
    let= C-rename f M `in C-rename (ren-cong f) N
  C-rename f (letrec M `in N) =
    letrec C-rename (ren-cong (ren-cong f)) M `in C-rename (ren-cong f) N
  C-rename f (V · W) =
    V-rename f V · V-rename f W
  C-rename f (↑ op p V M) =
    ↑ op p (V-rename f V) (C-rename f M)
  C-rename f (↓ op V M) =
    ↓ op (V-rename f V) (C-rename f M)
  C-rename f (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ C-rename (ren-cong f) M `in C-rename (ren-cong f) N
  C-rename f (await V until M) =
    await (V-rename f V) until (C-rename (ren-cong f) M)
  C-rename f (unbox V `in M) =
    unbox (V-rename f V) `in (C-rename (ren-cong f) M)
  C-rename f (coerce p q M) =
    coerce p q (C-rename f M)


-- ACTION OF RENAMING ON WELL-TYPED PROCESSES

P-rename : {o : O} {PP : PType o} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢P⦂ PP → Γ' ⊢P⦂ PP
P-rename f (run M) =
  run (C-rename f M)
P-rename f (P ∥ Q) =
  P-rename f P ∥ P-rename f Q
P-rename f (↑ op p V P) =
  ↑ op p (V-rename f V) (P-rename f P)
P-rename f (↓ op V P) =
  ↓ op (V-rename f V) (P-rename f P)
