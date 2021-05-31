open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations
open import Types

module AEff where

-- ARITY ASSIGNMENT TO SIGNATURES OF SIGNALS, INTERRUPTS, AND BASE CONSTANTS

postulate payload : Σₛ → Σ VType (λ X → mobile X)     -- payload type assignment for signal and interrupt names

postulate Σ-base : Set             -- set of base constants
postulate ar-base : Σ-base → BType -- arity assignment to base constants


-- CONTEXTS

data Ctx : Set where
  []  : Ctx
  _∷_ : Ctx → VType → Ctx
  _■  : Ctx → Ctx

infixl 35 _∷_
infixl 35 _■

_++ₖ_ : Ctx → Ctx → Ctx
Γ ++ₖ [] = Γ
Γ ++ₖ (Γ' ∷ X) = (Γ ++ₖ Γ') ∷ X
Γ ++ₖ (Γ' ■) = (Γ ++ₖ Γ') ■

infixl 30 _++ₖ_

-- VARIABLES IN CONTEXTS (I.E., DE BRUIJN INDICES)

data _∈_ (X : VType) : Ctx → Set where
  Hd   : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl-v : {Γ : Ctx} {Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)
  Tl-■ : {Γ : Ctx} → mobile X → X ∈ Γ → X ∈ (Γ ■)


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where
  
    `_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ´_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ``(ar-base c)
          
    ƛ   : {X : VType}
          {C : CType} →
          Γ ∷ X ⊢C⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : VType} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩

    □   : {X : VType} →
          Γ ■ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ □ X

          
  infix 40 _·_

  data _⊢C⦂_ (Γ : Ctx) : CType → Set where

    return           : {X : VType}
                       {o : O}
                       {i : I} →
                       Γ ⊢V⦂ X →
                       -----------------
                       Γ ⊢C⦂ X ! (o , i)

    let=_`in_        : {X Y : VType}
                       {o : O}
                       {i : I} → 
                       Γ ⊢C⦂ X ! (o , i) →
                       Γ ∷ X ⊢C⦂ Y ! (o , i) →
                       -----------------------
                       Γ ⊢C⦂ Y ! (o , i)

    letrec_`in_      : {X : VType}
                       {C D : CType} →
                       Γ ∷ (X ⇒ C) ∷ X ⊢C⦂ C →
                       Γ ∷ (X ⇒ C) ⊢C⦂ D →
                       -----------------------
                       Γ ⊢C⦂ D

    _·_              : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ X ⇒ C →
                       Γ ⊢V⦂ X →
                       -------------
                       Γ ⊢C⦂ C

    ↑                : {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₛ) →
                       op ∈ₒ o →
                       Γ ⊢V⦂ proj₁ (payload op) →
                       Γ ⊢C⦂ X ! (o , i) →
                       --------------------------
                       Γ ⊢C⦂ X ! (o , i)

    ↓                : {X : VType}
                       {o : O}
                       {i : I}
                       (op : Σₛ) →
                       Γ ⊢V⦂ proj₁ (payload op) →
                       Γ ⊢C⦂ X ! (o , i) →
                       --------------------------
                       Γ ⊢C⦂ X ! op ↓ₑ (o , i)

    promise_∣_↦_`in_ : {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σₛ) →
                       lkpᵢ op i ≡ just (o' , i') →
                       Γ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o' , i') →
                       Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i) →
                       ----------------------------------------------
                       Γ ⊢C⦂ Y ! (o , i)

    await_until_     : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ ⟨ X ⟩ →
                       Γ ∷ X ⊢C⦂ C →
                       --------------
                       Γ ⊢C⦂ C

    unbox_`in_       : {X : VType}
                       {C : CType} →
                       Γ ⊢V⦂ □ X →
                       Γ ∷ X ⊢C⦂ C →
                       -------------
                       Γ ⊢C⦂ C

    spawn            : {C D : CType} →
                       Γ ■ ⊢C⦂ C →
                       Γ ⊢C⦂ D →
                       ---------------------
                       Γ ⊢C⦂ D

    coerce           : {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       o ⊑ₒ o' →
                       i ⊑ᵢ i' → 
                       Γ ⊢C⦂ X ! (o , i) →
                       -------------------
                       Γ ⊢C⦂ X ! (o' , i')
                        


-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_

data _⊢P⦂_ (Γ : Ctx) : {o : O} → PType o → Set where

  run     : {X : VType}
            {o : O}
            {i : I} →
            Γ ⊢C⦂ X ! (o , i) →
            -------------------
            Γ ⊢P⦂ X ‼ o , i

  _∥_     : {o o' : O}
            {PP : PType o} →
            {QQ : PType o'} → 
            Γ ⊢P⦂ PP →
            Γ ⊢P⦂ QQ →
            -----------------
            Γ ⊢P⦂ (PP ∥ QQ)

  ↑       : {o : O} →
            {PP : PType o}
            (op : Σₛ) →
            op ∈ₒ o →
            Γ ⊢V⦂ (proj₁ (payload op)) →
            Γ ⊢P⦂ PP →
            ----------------------------
            Γ ⊢P⦂ PP

  ↓       : {o : O}
            {PP : PType o}
            (op : Σₛ) →
            Γ ⊢V⦂ (proj₁ (payload op)) →
            Γ ⊢P⦂ PP →
            ----------------------------
            Γ ⊢P⦂ op ↓ₚ PP


-- ADMISSIBLE TYPING RULES

■-dup-var : {Γ Γ' : Ctx} {X : VType} →
            X ∈ (Γ ■ ++ₖ Γ') →
            --------------------------
            X ∈ (Γ ■ ■ ++ₖ Γ')

■-dup-var {Γ} {[]} (Tl-■ p x) =
  Tl-■ p (Tl-■ p x)
■-dup-var {Γ} {Γ' ∷ Y} Hd =
  Hd
■-dup-var {Γ} {Γ' ∷ Y} (Tl-v x) =
  Tl-v (■-dup-var x)
■-dup-var {Γ} {Γ' ■} (Tl-■ p x) =
  Tl-■ p (■-dup-var x)
            

mutual

  ■-dup-v : {Γ Γ' : Ctx} {X : VType} →
            (Γ ■ ++ₖ Γ') ⊢V⦂ X →
            --------------------------
            (Γ ■ ■ ++ₖ Γ') ⊢V⦂ X
          
  ■-dup-v (` x) =
    ` ■-dup-var x
  ■-dup-v (´ c) =
    ´ c
  ■-dup-v (ƛ M) =
    ƛ (■-dup-c M)
  ■-dup-v ⟨ V ⟩ =
    ⟨ ■-dup-v V ⟩
  ■-dup-v (□ V) =
    □ (■-dup-v {Γ' = _ ■} V)


  ■-dup-c : {Γ Γ' : Ctx} {C : CType} →
            (Γ ■ ++ₖ Γ') ⊢C⦂ C →
            --------------------------
            (Γ ■ ■ ++ₖ Γ') ⊢C⦂ C

  ■-dup-c (return V) =
    return (■-dup-v V)
  ■-dup-c (let= M `in N) =
    let= (■-dup-c M) `in (■-dup-c N)
  ■-dup-c (letrec M `in N) =
    letrec (■-dup-c M) `in (■-dup-c N)
  ■-dup-c (V · W) =
    (■-dup-v V) · (■-dup-v W)
  ■-dup-c (↑ op p V M) =
    ↑ op p (■-dup-v V) (■-dup-c M)
  ■-dup-c (↓ op V M) =
    ↓ op (■-dup-v V) (■-dup-c M)
  ■-dup-c (promise op ∣ x ↦ M `in N) =
    promise op ∣ x ↦ (■-dup-c M) `in (■-dup-c N)
  ■-dup-c (await V until M) =
    await (■-dup-v V) until (■-dup-c M)
  ■-dup-c (unbox V `in M) =
    unbox (■-dup-v V) `in (■-dup-c M)
  ■-dup-c (spawn M N) =
    spawn (■-dup-c {Γ' = _ ■} M) (■-dup-c N)
  ■-dup-c (coerce p q M) =
    coerce p q (■-dup-c M)
  

■-wk : {Γ : Ctx} {X : VType} →
       mobile X →
       Γ ⊢V⦂ X →
       -----------------------
       Γ ■ ⊢V⦂ X
       
■-wk p (` x) =
  ` Tl-■ p x
■-wk p (´ c) =
  ´ c
■-wk p (□ V) =
  □ (■-dup-v {_} {[]} V)


■-str-var : {Γ Γ' : Ctx} {X : VType} →
            X ∈ Γ ■ ++ₖ Γ' →
            --------------------------
            X ∈ Γ ++ₖ Γ'

■-str-var {Γ} {[]} (Tl-■ p x) =
  x
■-str-var {Γ} {Γ' ∷ Y} Hd =
  Hd
■-str-var {Γ} {Γ' ∷ Y} (Tl-v x) =
  Tl-v (■-str-var x)
■-str-var {Γ} {Γ' ■} (Tl-■ p x) =
  Tl-■ p (■-str-var x)


mutual

  ■-str-v : {Γ Γ' : Ctx} {X : VType} →
            Γ ■ ++ₖ Γ' ⊢V⦂ X →
            -----------------------
            Γ ++ₖ Γ' ⊢V⦂ X

  ■-str-v (` x) =
    ` ■-str-var x
  ■-str-v (´ c) =
    ´ c
  ■-str-v (ƛ M) =
    ƛ (■-str-c M)
  ■-str-v ⟨ V ⟩ =
    ⟨ ■-str-v V ⟩
  ■-str-v {Γ} {Γ'} (□ V) =
    □ (■-str-v {Γ' = _ ■} V)


  ■-str-c : {Γ Γ' : Ctx} {C : CType} →
            Γ ■ ++ₖ Γ' ⊢C⦂ C →
            -----------------------
            Γ ++ₖ Γ' ⊢C⦂ C

  ■-str-c (return V) =
    return (■-str-v V)
  ■-str-c (let= M `in N) =
    let= (■-str-c M) `in (■-str-c N)
  ■-str-c (letrec M `in N) =
    letrec (■-str-c M) `in (■-str-c N)
  ■-str-c (V · W) =
    (■-str-v V) · (■-str-v W)
  ■-str-c (↑ op p V M) =
    ↑ op p (■-str-v V) (■-str-c M)
  ■-str-c (↓ op V M) =
    ↓ op (■-str-v V) (■-str-c M)
  ■-str-c (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ (■-str-c M) `in (■-str-c N)
  ■-str-c (await V until M) =
    await (■-str-v V) until (■-str-c M)
  ■-str-c (unbox V `in M) =
    unbox (■-str-v V) `in (■-str-c M)
  ■-str-c (spawn M N) =
    spawn (■-str-c {Γ' = _ ■} M) (■-str-c N)
  ■-str-c (coerce p q M) =
    coerce p q (■-str-c M)

