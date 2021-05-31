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

ren-var : {Γ Γ' : Ctx} {X : VType} →
          Ren Γ Γ' →
          X ∈ Γ →
          --------------------------
          X ∈ Γ'
          
ren-var ⟨ f , x ⟩ Hd =
  x
ren-var (π f) Hd =
  Tl-v (ren-var f Hd)
ren-var ⟨ f , y ⟩ (Tl-v x) =
  ren-var f x
ren-var (π f) (Tl-v x) =
  Tl-v (ren-var f (Tl-v x))
ren-var (π f) (Tl-■ p x) =
  Tl-v (ren-var f (Tl-■ p x))
ren-var (φ f) (Tl-■ p x) =
  Tl-■ p (ren-var f x)


-- IDENTITY RENAMING

ren-id : {Γ : Ctx} →
         -----------
         Ren Γ Γ
         
ren-id {[]} =
  ε
ren-id {Γ ∷ X} =
  ⟨ π ren-id , Hd ⟩
ren-id {Γ ■} =
  φ ren-id


-- EXCHANGE RENAMING

ren-exch : {Γ : Ctx} {X Y : VType} →
           ---------------------------
           Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)

ren-exch {Γ} = ⟨ ⟨ π (π ren-id) , Hd ⟩ , Tl-v Hd ⟩


-- COMPOSITION OF RENAMINGS

ren-comp : {Γ Γ' Γ'' : Ctx} →
           Ren Γ' Γ'' →
           Ren Γ Γ' →
           ------------------
           Ren Γ Γ''
           
ren-comp g ⟨ f , x ⟩ =
  ⟨ ren-comp g f , ren-var g x ⟩
ren-comp g ε =
  ε
ren-comp ⟨ g , x ⟩ (π f) =
  ren-comp g f
ren-comp (π g) (π f) =
  π (ren-comp g (π f))
ren-comp (π g) (φ f) =
  π (ren-comp g (φ f))
ren-comp (φ g) (φ f) =
  φ (ren-comp g f)


-- WEAKENING OF RENAMINGS

ren-wk : {Γ : Ctx} {X : VType} →
         -----------------------
         Ren Γ (Γ ∷ X)
         
ren-wk =
  π ren-id


-- CONGRUENCE OF RENAMINGS

ren-cong : {Γ Γ' : Ctx} {X : VType} →
           Ren Γ Γ' →
           --------------------------
           Ren (Γ ∷ X) (Γ' ∷ X)
           
ren-cong f =
  ⟨ π f , Hd ⟩


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  V-rename : {X : VType} {Γ Γ' : Ctx} →
             Ren Γ Γ' →
             Γ ⊢V⦂ X →
             --------------------------
             Γ' ⊢V⦂ X
             
  V-rename f (` x) =
    ` ren-var f x
  V-rename f (´ c) =
    ´ c
  V-rename f (ƛ M) =
    ƛ (C-rename (ren-cong f) M)
  V-rename f ⟨ V ⟩ =
    ⟨ V-rename f V ⟩
  V-rename f (□ V) =
    □ (V-rename (φ f) V)

  C-rename : {C : CType} {Γ Γ' : Ctx} →
             Ren Γ Γ' →
             Γ ⊢C⦂ C →
             --------------------------
             Γ' ⊢C⦂ C
  
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
  C-rename f (spawn M N) =
    spawn (C-rename (φ f) M) (C-rename f N)
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
