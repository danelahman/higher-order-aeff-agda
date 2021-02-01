open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product

open import AEff
open import EffectAnnotations
open import Renamings
open import Substitutions renaming (⟨_,_⟩ to ⟨_,,_⟩)
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Preservation where


-- BINDING CONTEXTS

BCtx = List VType


-- WELL-TYPED EVALUATION CONTEXTS

data _⊢E[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]              : {C : CType} → 
                     -------------
                     Γ ⊢E[ [] ]⦂ C

  let=_`in_        : {Δ : BCtx}
                     {X Y : VType}
                     {o : O}
                     {i : I} →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     Γ ∷ X ⊢C⦂ Y ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ Y ! (o , i)

  ↑                : {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I} →
                     (op : Σₛ) →
                     op ∈ₒ o →
                     Γ ⊢V⦂ proj₁ (payload op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     --------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o , i)

  ↓                : {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I}
                     (op : Σₛ) →
                     Γ ⊢V⦂ proj₁ (payload op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ---------------------------
                     Γ ⊢E[ Δ ]⦂ X ! op ↓ₑ (o , i)

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σₛ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢E[ Δ ]⦂ Y ! (o , i) →
                     ----------------------------------------------
                     Γ ⊢E[ X ∷ₗ Δ ]⦂ Y ! (o , i)

  coerce           : {Δ : BCtx}
                     {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o' , i')


-- MERGING AN ORDINARY CONTEXT AND A BINDING CONTEXT

infix 30 _⋈_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ [] = Γ
Γ ⋈ (X ∷ₗ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED EVALUATION CONTEXT

hole-ty-e : {Γ : Ctx} {Δ : BCtx} {C : CType} → Γ ⊢E[ Δ ]⦂ C → CType
hole-ty-e {_} {_} {C} [-] =
  C
hole-ty-e (let= E `in M) =
  hole-ty-e E
hole-ty-e (↑ op p V E) =
  hole-ty-e E
hole-ty-e (↓ op V E) =
  hole-ty-e E
hole-ty-e (promise op ∣ p ↦ M `in E) =
  hole-ty-e E
hole-ty-e (coerce p q E) =
  hole-ty-e E


-- FILLING A WELL-TYPED EVALUATION CONTEXT

{- LEMMA 3.5 -}

infix 30 _[_]

_[_] : {Γ : Ctx} {Δ : BCtx} {C : CType} → (E : Γ ⊢E[ Δ ]⦂ C) → Γ ⋈ Δ ⊢C⦂ (hole-ty-e E) → Γ ⊢C⦂ C
[-] [ M ] =
  M
(let= E `in N) [ M ] =
  let= (E [ M ]) `in N
↑ op p V E [ M ] =
  ↑ op p V (E [ M ])
↓ op V E [ M ] =
  ↓ op V (E [ M ])
(promise op ∣ p ↦ N `in E) [ M ] =
  promise op ∣ p ↦ N `in (E [ M ])
coerce p q E [ M ] =
  coerce p q (E [ M ])


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {X : VType} →
                 mobile X →
                 X ∈ Γ ⋈ Δ →
                 --------------------------------------
                 X ∈ Γ
                 
strengthen-var [] p x = x
strengthen-var (y ∷ₗ Δ) p x with strengthen-var Δ p x
... | Tl-v z = z


strengthen-■-var : {Γ : Ctx} → (Γ' : Ctx) →
                   (Δ : BCtx) → {X : VType} →
                   X ∈ (Γ ⋈ Δ) ■ ++ₖ Γ' →
                   --------------------------
                   X ∈ Γ ■ ++ₖ Γ'

strengthen-■-var Γ' [] x = x
strengthen-■-var [] (y ∷ₗ Δ) x with strengthen-■-var [] Δ x
... | Tl-■ p (Tl-v z) = Tl-■ p z
strengthen-■-var (Γ' ∷ Z) (y ∷ₗ Δ) Hd = Hd
strengthen-■-var (Γ' ∷ Z) (y ∷ₗ Δ) (Tl-v x) with strengthen-■-var Γ' (y ∷ₗ Δ) x
... | q = Tl-v q
strengthen-■-var (Γ' ■) (y ∷ₗ Δ) (Tl-■ p x) with strengthen-■-var Γ' (y ∷ₗ Δ) x
... | q = Tl-■ p q


mutual 
  strengthen-■-v : {Γ Γ' : Ctx} {Δ : BCtx} {X : VType} →
                   (Γ ⋈ Δ) ■ ++ₖ Γ' ⊢V⦂ X →
                   -------------------------------------
                   Γ ■ ++ₖ Γ' ⊢V⦂ X
                 
  strengthen-■-v {_} {Γ'} {Δ} (` x) =
    ` strengthen-■-var Γ' Δ x
  strengthen-■-v (´ c) =
    ´ c
  strengthen-■-v {Γ} {Γ'} {Δ} (ƛ M) = ƛ (strengthen-■-c {Γ} {Γ' ∷ _} {Δ} M)
  strengthen-■-v {Γ} {Γ'} {Δ} ⟨ V ⟩ =
    ⟨ strengthen-■-v {Γ} {Γ'} {Δ} V ⟩
  strengthen-■-v {Γ} {Γ'} {Δ} (□ V) =
    □ (strengthen-■-v {Γ} {Γ' ■} {Δ} V)


  strengthen-■-c : {Γ Γ' : Ctx} {Δ : BCtx} {C : CType} →
                   (Γ ⋈ Δ) ■ ++ₖ Γ' ⊢C⦂ C →
                   -------------------------------------
                   Γ ■ ++ₖ Γ' ⊢C⦂ C

  strengthen-■-c {Γ} {Γ'} {Δ} (return V) =
    return (strengthen-■-v {Γ} {Γ'} {Δ} V)
  strengthen-■-c {Γ} {Γ'} {Δ} (let= M `in N) =
    let= (strengthen-■-c {Γ} {Γ'} {Δ} M) `in (strengthen-■-c {Γ} {Γ' ∷ _} {Δ} N)
  strengthen-■-c {Γ} {Γ'} {Δ} (letrec M `in N) =
    letrec (strengthen-■-c {Γ} {Γ' ∷ (_ ⇒ _) ∷ _} {Δ} M) `in (strengthen-■-c {Γ} {Γ' ∷ (_ ⇒ _)} {Δ} N)
  strengthen-■-c {Γ} {Γ'} {Δ} (V · W) =
    (strengthen-■-v {Γ} {Γ'} {Δ} V) · (strengthen-■-v {Γ} {Γ'} {Δ} W)
  strengthen-■-c {Γ} {Γ'} {Δ} (↑ op p V M) =
    ↑ op p (strengthen-■-v {Γ} {Γ'} {Δ} V) (strengthen-■-c {Γ} {Γ'} {Δ} M)
  strengthen-■-c {Γ} {Γ'} {Δ} (↓ op V M) =
    ↓ op (strengthen-■-v {Γ} {Γ'} {Δ} V) (strengthen-■-c {Γ} {Γ'} {Δ} M)
  strengthen-■-c {Γ} {Γ'} {Δ} (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ (strengthen-■-c {Γ} {Γ' ∷ proj₁ (payload op)} {Δ} M) `in (strengthen-■-c {Γ} {Γ' ∷ ⟨ _ ⟩} {Δ} N)
  strengthen-■-c {Γ} {Γ'} {Δ} (await V until N) =
    await (strengthen-■-v {Γ} {Γ'} {Δ} V) until (strengthen-■-c {Γ} {Γ' ∷ _} {Δ} N)
  strengthen-■-c {Γ} {Γ'} {Δ} (unbox V `in N) =
    unbox (strengthen-■-v {Γ} {Γ'} {Δ} V) `in (strengthen-■-c {Γ} {Γ' ∷ _} {Δ} N)
  strengthen-■-c {Γ} {Γ'} {Δ} (coerce p q M) =
    coerce p q (strengthen-■-c {Γ} {Γ'} {Δ} M)


strengthen-val : {Γ : Ctx} {Δ : BCtx} {X : VType} →
                 mobile X →
                 Γ ⋈ Δ ⊢V⦂ X →
                 ----------------------------------
                 Γ ⊢V⦂ X
                 
strengthen-val {_} {Δ} p (` x) =
  ` strengthen-var Δ p x
strengthen-val p (´ c) =
  ´ c
strengthen-val {Γ} {Δ} p (□ V) =
  □ (strengthen-■-v {Γ} {[]} {Δ} V)


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

infix 10 _↝_

data _↝_ {Γ : Ctx} : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

  -- COMPUTATIONAL RULES

  apply           : {X : VType}
                    {C : CType} →
                    (M : Γ ∷ X ⊢C⦂ C) →
                    (V : Γ ⊢V⦂ X) →
                    ----------------------
                    (ƛ M) · V
                    ↝
                    M [ sub-id [ V ]s ]c

  let-return      : {X Y : VType}
                    {o : O}
                    {i : I} → 
                    (V : Γ ⊢V⦂ X) →
                    (N : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                    -----------------------------
                    let= (return V) `in N
                    ↝
                    N [ sub-id [ V ]s ]c

  let-↑           : {X Y : VType}
                    {o : O}
                    {i : I}
                    {op : Σₛ} →
                    (p : op ∈ₒ o) →
                    (V : Γ ⊢V⦂ proj₁ (payload op)) →
                    (M : Γ ⊢C⦂ X ! (o , i)) →
                    (N : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                    -----------------------------
                    let= (↑ op p V M) `in N
                    ↝
                    ↑ op p V (let= M `in N)

  let-promise     : {X Y Z : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ} →
                    (p : lkpᵢ op i ≡ just (o' , i')) →
                    (M₁ : Γ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                    (M₂ : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                    (N : Γ ∷ Y ⊢C⦂ Z ! (o , i)) →
                    ----------------------------------------------------------------------
                    let= (promise op ∣ p ↦ M₁ `in M₂) `in N
                    ↝
                    (promise op ∣ p ↦ M₁ `in (let= M₂ `in (C-rename (ren-cong ren-wk) N)))

  letrec-unfold   : {X : VType}
                    {C D : CType}
                    (M : Γ ∷ (X ⇒ C) ∷ X ⊢C⦂ C) →
                    (N : Γ ∷ (X ⇒ C) ⊢C⦂ D) →
                    -------------------------------------------------------------------------------------------------
                    (letrec M `in N)
                    ↝
                    N [ sub-id [ ƛ (letrec (C-rename (ren-cong (ren-cong ren-wk)) M) `in (C-rename ren-exch M)) ]s ]c

  promise-↑       : {X Y : VType}
                    {o o' : O}
                    {i i' : I}
                    {op op' : Σₛ} →
                    (p : lkpᵢ op i ≡ just (o' , i')) →
                    (q : op' ∈ₒ o) →
                    (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ proj₁ (payload op')) → 
                    (M : Γ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                    -----------------------------------------------------------------------------------------
                    (promise op ∣ p ↦ M `in (↑ op' q V N))
                    ↝
                    ↑ op' q (strengthen-val {Δ = X ∷ₗ []} (proj₂ (payload op')) V) (promise op ∣ p ↦ M `in N)

  ↓-return        : {X : VType}
                    {o : O}
                    {i : I}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ proj₁ (payload op)) →
                    (W : Γ ⊢V⦂ X) →
                    ----------------------------------------------------------------
                    ↓ {o = o} {i = i} op V (return W)
                    ↝
                    return {o = proj₁ (op ↓ₑ (o , i))} {i = proj₂ (op ↓ₑ (o , i))} W

  ↓-↑             : {X : VType}
                    {o : O}
                    {i : I}
                    {op : Σₛ}
                    {op' : Σₛ} →
                    (p : op' ∈ₒ o) →
                    (V : Γ ⊢V⦂ proj₁ (payload op)) →
                    (W : Γ ⊢V⦂ proj₁ (payload op')) →
                    (M : Γ ⊢C⦂ X ! (o , i)) →
                    --------------------------------
                    ↓ op V (↑ op' p W M)
                    ↝
                    ↑ op' (↓ₑ-⊑ₒ op' p) W (↓ op V M)

  ↓-promise-op    : {X Y : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ} →
                    (p : lkpᵢ op i ≡ just (o' , i')) →
                    (V : Γ ⊢V⦂ proj₁ (payload op)) → 
                    (M : Γ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                    ---------------------------------------------------------------------------------------------------------
                    ↓ op V (promise op ∣ p ↦ M `in N )
                    ↝
                    (let= (coerce (↓ₑ-⊑ₒ-o' {o} p) (↓ₑ-⊑ₒ-i' {o} p) (M [ sub-id [ V ]s ]c)) `in (↓ op (V-rename ren-wk V) N))

  ↓-promise-op'   : {X Y : VType}
                    {o o' : O}
                    {i i' : I}
                    {op op' : Σₛ} →
                    (p : ¬ op ≡ op') →
                    (q : lkpᵢ op' i ≡ just (o' , i')) →
                    (V : Γ ⊢V⦂ proj₁ (payload op)) → 
                    (M : Γ ∷ proj₁ (payload op') ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                    ------------------------------------------------------------------------------------------
                    ↓ op V (promise op' ∣ q ↦ M `in N )
                    ↝
                    promise_∣_↦_`in_ {o' = proj₁ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)}
                                     {i' = proj₁ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q))}
                                     op'
                                     (proj₁ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q))))
                                     (coerce (proj₁ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)))))
                                             (proj₂ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)))))
                                             M)
                                     (↓ op (V-rename ren-wk V) N)

  await-promise   : {X : VType}
                    {C : CType} → 
                    (V : Γ ⊢V⦂ X) → 
                    (M : Γ ∷ X ⊢C⦂ C) →
                    --------------------
                    await ⟨ V ⟩ until M
                    ↝
                    M [ sub-id [ V ]s ]c

  box-unbox       : {X : VType}
                    {C : CType} →
                    (V : Γ ■ ⊢V⦂ X) →
                    (M : Γ ∷ X ⊢C⦂ C) →
                    -------------------
                    unbox (□ V) `in M
                    ↝
                    M [ ⟨ sub-id ,, ■-str-v {Γ' = []} V ⟩ ]c

  -- EVALUATION CONTEXT RULE

  context         : {Δ : BCtx}
                    {C : CType} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) →
                    {M N : Γ ⋈ Δ ⊢C⦂ (hole-ty-e E)} →
                    M ↝ N →
                    -------------------------------
                    E [ M ] ↝ E [ N ]

  -- COERCION RULES
  -- (THE RESULT OF WORKING WITH WELL-TYPED SYNTAX AND MAKING SUBSUMPTION INTO AN EXPLICIT COERCION)

  coerce-return   : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'} → 
                    (V : Γ ⊢V⦂ X) →
                    --------------------------------
                    coerce p q (return V) ↝ return V

  coerce-↑        : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'}
                    {op : Σₛ} → 
                    (r : op ∈ₒ o) →
                    (V : Γ ⊢V⦂ proj₁ (payload op)) →
                    (M : Γ ⊢C⦂ X ! (o , i)) →
                    -------------------------------
                    coerce p q (↑ op r V M)
                    ↝
                    ↑ op (p op r) V (coerce p q M)

  coerce-promise  : {X Y : VType}
                    {o o' o'' : O}
                    {i i' i'' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'}
                    {op : Σₛ} →
                    (r : lkpᵢ op i ≡ just (o'' , i''))
                    (M : Γ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o'' , i'')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                    ------------------------------------------------------------------
                    coerce p q (promise op ∣ r ↦ M `in N)
                    ↝
                    promise_∣_↦_`in_ {o' = lkpᵢ-nextₒ q r}
                                     {i' = lkpᵢ-nextᵢ q r}
                                     op
                                     (lkpᵢ-next-eq q r)
                                     (coerce (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M)
                                     (coerce p q N)


