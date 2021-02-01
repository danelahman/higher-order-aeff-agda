open import Data.Empty

open import AEff
open import EffectAnnotations
open import Renamings
open import Types hiding (``)

open import Relation.Binary.PropositionalEquality hiding ([_])

module Substitutions where

{-
Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈-∷ Γ → Γ' ⊢V⦂ X
-}

-- PARALLEL SUBSTITUTIONS

data Sub : Ctx → Ctx → Set where

  ⟨_,_⟩ : {Γ Γ' : Ctx} {X : VType} →
          Sub Γ Γ' →
          Γ' ⊢V⦂ X →
          --------------------------
          Sub (Γ ∷ X) Γ'

  ε     : {Γ' : Ctx} →
          ------------
          Sub [] Γ'
          
  π     : {Γ Γ' : Ctx} {X : VType} →
          Sub Γ Γ' →
          --------------------------
          Sub Γ (Γ' ∷ X)
  
  φ     : {Γ Γ' : Ctx} →
          Sub Γ Γ' →
          ----------------
          Sub (Γ ■) (Γ' ■)


-- RENAMINGS AS SUBSTITUTIONS

sub-of-ren : {Γ Γ' : Ctx} → Ren Γ Γ' → Sub Γ Γ'
sub-of-ren ε =
  ε
sub-of-ren ⟨ f , x ⟩ =
  ⟨ sub-of-ren f , ` x ⟩
sub-of-ren (π f) =
  π (sub-of-ren f)
sub-of-ren (φ f) =
  φ (sub-of-ren f)


-- IDENTITY SUBSTITUTION

sub-id : {Γ : Ctx} → Sub Γ Γ
sub-id = sub-of-ren ren-id


-- SUBSTITUTION EXTENSION

_[_]s : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
s [ V ]s = ⟨ s , V ⟩


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift ⟨ s , x ⟩ =
  ⟨ π ⟨ s , x ⟩ , ` Hd ⟩
lift ε =
  ⟨ ε , ` Hd ⟩
lift (π s) =
  ⟨ π (π s) , ` Hd ⟩
lift (φ s) =
  ⟨ π (φ s) , ` Hd ⟩


-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

val-of-sub : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → X ∈ Γ → Γ' ⊢V⦂ X
val-of-sub ⟨ s , V ⟩ Hd =
  V
val-of-sub ⟨ s , V ⟩ (Tl-v x) =
  val-of-sub s x
val-of-sub (π s) x =
  V-rename ren-wk (val-of-sub s x)
val-of-sub (φ s) (Tl-■ p x) =
  ■-wk p (val-of-sub s x)

mutual

  infix 40 _[_]v
  infix 40 _[_]c

  sub-var : {Γ Γ' : Ctx} {X : VType} → X ∈ Γ → Sub Γ Γ' → Γ' ⊢V⦂ X
  sub-var Hd ⟨ s , V ⟩ =
    V
  sub-var Hd (π s) =
    V-rename ren-wk (val-of-sub s Hd)
  sub-var (Tl-v x) ⟨ s , V ⟩ =
    sub-var x s
  sub-var (Tl-v x) (π s) =
    V-rename ren-wk (val-of-sub s (Tl-v x))
  sub-var (Tl-■ p x) (π s) =
    V-rename ren-wk (val-of-sub s (Tl-■ p x))
  sub-var (Tl-■ p x) (φ s) =
    ■-wk p (val-of-sub s x)

  comp-sub : {Γ Γ' Γ'' : Ctx} → Sub Γ' Γ'' → Sub Γ Γ' → Sub Γ Γ''
  comp-sub t ⟨ s , V ⟩ =
    ⟨ comp-sub t s , V [ t ]v ⟩
  comp-sub t ε =
    ε
  comp-sub ⟨ t , x ⟩ (π s) =
    comp-sub t s
  comp-sub (π t) (π s) =
    π (comp-sub t (π s))
  comp-sub (π t) (φ s) =
    π (comp-sub t (φ s))
  comp-sub (φ t) (φ s) =
    φ (comp-sub t s)

  _[_]v : {Γ Γ' : Ctx} {X : VType} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]v =
    sub-var x s
  (´ c) [ s ]v =
    ´ c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]c)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩
  (□ V) [ s ]v =
    □ (V [ φ s ]v)

  _[_]c : {Γ Γ' : Ctx} {C : CType} → Γ ⊢C⦂ C → Sub Γ Γ'  → Γ' ⊢C⦂ C
  (return V) [ s ]c =
    return (V [ s ]v)
  (let= M `in N) [ s ]c =
    let= (M [ s ]c) `in (N [ lift s ]c)
  (letrec M `in N) [ s ]c =
    letrec M [ lift (lift s) ]c `in (N [ lift s ]c)
  (V · W) [ s ]c =
    (V [ s ]v) · (W [ s ]v)
  (↑ op p V M) [ s ]c =
    ↑ op p (V [ s ]v) (M [ s ]c)
  (↓ op V M) [ s ]c =
    ↓ op (V [ s ]v) (M [ s ]c)
  (promise op ∣ p ↦ M `in N) [ s ]c =
    promise op ∣ p ↦ (M [ lift s ]c) `in (N [ lift s ]c)
  (await V until M) [ s ]c =
    await (V [ s ]v) until (M [ lift s ]c)
  (unbox V `in M) [ s ]c =
    unbox (V [ s ]v) `in (M [ lift s ]c)
  (coerce p q M) [ s ]c =
    coerce p q (M [ s ]c)


-- ACTION OF SUBSTITUTION ON WELL-TYPED PROCESSES

infix 40 _[_]p

_[_]p : {Γ Γ' : Ctx} {o : O} {PP : PType o} → Γ ⊢P⦂ PP → Sub Γ Γ' → Γ' ⊢P⦂ PP
(run M) [ s ]p =
  run (M [ s ]c)
(P ∥ Q) [ s ]p =
  (P [ s ]p) ∥ (Q [ s ]p)
(↑ op p V P) [ s ]p =
  ↑ op p (V [ s ]v) (P [ s ]p)
(↓ op V P) [ s ]p =
  ↓ op (V [ s ]v) (P [ s ]p)
