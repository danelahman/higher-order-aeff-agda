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

data _∈-∷_ (X : VType) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈-∷ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : VType} → X ∈-∷ Γ → X ∈-∷ (Γ ∷ Y)

∈-∷-∈ : {X : VType} {Γ : Ctx} → X ∈-∷ Γ → X ∈ Γ
∈-∷-∈ Hd = Hd
∈-∷-∈ (Tl x) = Tl-v (∈-∷-∈ x)

mutual

  data Sub : Ctx → Ctx → Set where
    sub : {Γ Γ' : Ctx} → ({X : VType} → X ∈-∷ Γ → Γ' ⊢V⦂ X) → Sub-■ Γ Γ' → Sub Γ Γ'

  data Sub-■ : Ctx → Ctx → Set where
    sub   : {Γ Γ' : Ctx} → Sub Γ Γ' → Sub-■ (Γ ■) (Γ' ■)
    empty : {Γ' : Ctx} → Sub-■ [] Γ'
    left  : {Γ Γ' : Ctx} {X : VType} → Sub-■ Γ Γ' → Sub-■ (Γ ∷ X) Γ'
    right : {Γ Γ' : Ctx} {Y : VType} → Sub-■ Γ Γ' → Sub-■ Γ (Γ' ∷ Y)


-- IDENTITY AND EXTENSION SUBSTITUTIONS

mutual

  id-subst : {Γ : Ctx} → Sub Γ Γ
  id-subst = sub (λ x → ` (∈-∷-∈ x)) id-subst-■

  id-subst-■ : {Γ : Ctx} → Sub-■ Γ Γ
  id-subst-■ {[]} = empty
  id-subst-■ {Γ ∷ X} = left (right id-subst-■)
  id-subst-■ {Γ ■} = sub id-subst


_[_]s : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(sub s₁ s₂) [ V ]s = sub (ext-aux s₁ V) (left s₂)

  where

  ext-aux : {Γ Γ' : Ctx} {X : VType}
          → ({Y : VType} → Y ∈-∷ Γ → Γ' ⊢V⦂ Y)
          → Γ' ⊢V⦂ X
          ----------------------------------------
          → {Y : VType} → Y ∈-∷ (Γ ∷ X) → Γ' ⊢V⦂ Y
      
  ext-aux s V Hd = V
  ext-aux s V (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift (sub s₁ s₂) = sub (lift-aux s₁) (left (right s₂))

  where

  lift-aux : {Γ Γ' : Ctx} {X : VType}
           → ({Y : VType} → Y ∈-∷ Γ → Γ' ⊢V⦂ Y)
           ----------------------------------------------
           → {Y : VType} → Y ∈-∷ (Γ ∷ X) → (Γ' ∷ X) ⊢V⦂ Y

  lift-aux s Hd = ` Hd
  lift-aux s (Tl x) = V-rename ren-wk₁ (s x)


lift-■ : {Γ Γ' : Ctx} → Sub Γ Γ' → Sub (Γ ■) (Γ' ■)
lift-■ s = sub (λ ()) (sub s)


-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

_[_,_]var : {Γ Γ' : Ctx} {X : VType} → X ∈ Γ → ({Y : VType} → Y ∈-∷ Γ → Γ' ⊢V⦂ Y) → Sub-■ Γ Γ' → Γ' ⊢V⦂ X
Hd [ s₁ , s₂ ]var = s₁ Hd
Tl-v x [ s₁ , s₂ ]var = x [ {!!} , {!!} ]var
Tl-■ p x [ s₁ , s₂ ]var = x [ {!!} , {!!} ]var


mutual

  infix 40 _[_]v
  infix 40 _[_]m

  _[_]v : {Γ Γ' : Ctx} {X : VType} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ sub s₁ s₂ ]v = {!!}
  (`` c) [ s ]v =
    `` c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]m)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩
  [ V ] [ s ]v =
    [ V [ lift-■ s ]v ]

  _[_]m : {Γ Γ' : Ctx} {C : CType} → Γ ⊢M⦂ C → Sub Γ Γ'  → Γ' ⊢M⦂ C
  (return V) [ s ]m =
    return (V [ s ]v)
  (let= M `in N) [ s ]m =
    let= (M [ s ]m) `in (N [ lift s ]m)
  (letrec M `in N) [ s ]m =
    letrec M [ lift (lift s) ]m `in (N [ lift s ]m)
  (V · W) [ s ]m =
    (V [ s ]v) · (W [ s ]v)
  (↑ op p V M) [ s ]m =
    ↑ op p (V [ s ]v) (M [ s ]m)
  (↓ op V M) [ s ]m =
    ↓ op (V [ s ]v) (M [ s ]m)
  (promise op ∣ p ↦ M `in N) [ s ]m =
    promise op ∣ p ↦ (M [ lift s ]m) `in (N [ lift s ]m)
  (await V until M) [ s ]m =
    await (V [ s ]v) until (M [ lift s ]m)
  (unbox V `in M) [ s ]m =
    unbox (V [ s ]v) `in (M [ lift s ]m)
  (coerce p q M) [ s ]m =
    coerce p q (M [ s ]m)



{-
-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : {Γ : Ctx} → Sub Γ Γ
id-subst x = ` x


_[_]s : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl-v x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl-v x) = V-rename ren-wk₁ (s x)


lift-■ : {Γ Γ' : Ctx} → Sub Γ Γ' → Sub (Γ ■) (Γ' ■)
lift-■ s (Tl-■ p x) = V-rename {!!} (s x)



-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  infix 40 _[_]v
  infix 40 _[_]m

  _[_]v : {Γ Γ' : Ctx} → {X : VType} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]v =
    s x
  (`` c) [ s ]v =
    `` c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]m)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩
  [ V ] [ s ]v =
    [ {!V [ s ]v!} ]

  _[_]m : {Γ Γ' : Ctx} → {C : CType} → Γ ⊢M⦂ C → Sub Γ Γ'  → Γ' ⊢M⦂ C
  (return V) [ s ]m =
    return (V [ s ]v)
  (let= M `in N) [ s ]m =
    let= (M [ s ]m) `in (N [ lift s ]m)
  (letrec M `in N) [ s ]m =
    letrec M [ lift (lift s) ]m `in (N [ lift s ]m)
  (V · W) [ s ]m =
    (V [ s ]v) · (W [ s ]v)
  (↑ op p V M) [ s ]m =
    ↑ op p (V [ s ]v) (M [ s ]m)
  (↓ op V M) [ s ]m =
    ↓ op (V [ s ]v) (M [ s ]m)
  (promise op ∣ p ↦ M `in N) [ s ]m =
    promise op ∣ p ↦ (M [ lift s ]m) `in (N [ lift s ]m)
  (await V until M) [ s ]m =
    await (V [ s ]v) until (M [ lift s ]m)
  (unbox V `in M) [ s ]m =
    {!!}
  (coerce p q M) [ s ]m =
    coerce p q (M [ s ]m)
-}

{-
-- ACTION OF SUBSTITUTION ON WELL-TYPED PROCESSES

infix 40 _[_]p

_[_]p : {Γ Γ' : Ctx} {o : O} {PP : PType o} → Γ ⊢P⦂ PP → Sub Γ Γ' → Γ' ⊢P⦂ PP
(run M) [ s ]p =
  run (M [ s ]m)
(P ∥ Q) [ s ]p =
  (P [ s ]p) ∥ (Q [ s ]p)
(↑ op p V P) [ s ]p =
  ↑ op p (V [ s ]v) (P [ s ]p)
(↓ op V P) [ s ]p =
  ↓ op (V [ s ]v) (P [ s ]p)

-}
