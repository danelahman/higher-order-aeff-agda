open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import EffectAnnotations
open import Preservation
open import Progress
open import Renamings
open import Substitutions renaming (⟨_,_⟩ to ⟨_,,_⟩)
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Finality where


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

mutual

  infix 10 _↝↝_

  data _↝↝_ {Γ : Ctx} : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    -- COMPUTATIONAL RULES

    apply           : {X : VType}
                      {C : CType} →
                      (M : Γ ∷ X ⊢C⦂ C) →
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      (ƛ M) · V
                      ↝↝
                      M [ sub-id [ V ]s ]c

    let-return      : {X Y : VType}
                      {o : O}
                      {i : I} → 
                      (V : Γ ⊢V⦂ X) →
                      (N : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                      -----------------------------
                      let= (return V) `in N
                      ↝↝
                      N [ sub-id [ V ]s ]c

    let-↑           : {X Y : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (p : op ∈ₒ o) →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) →
                      (M : Γ ⊢C⦂ X ! (o , i)) →
                      (N : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                      --------------------------------
                      let= (↑ op p V M) `in N
                      ↝↝
                      ↑ op p V (let= M `in N)

    let-promise     : {X Y Z : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (M₁ : Γ ∷ proj₁ (payload op) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (M₂ : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      (N : Γ ∷ Y ⊢C⦂ Z ! (o , i)) →
                      ---------------------------------------------------------------------------------------------------------
                      let= (promise op ∣ p ↦ M₁ `in M₂) `in N
                      ↝↝
                      (promise op ∣ p ↦ M₁ `in (let= M₂ `in (C-rename (ren-cong ren-wk) N)))

    let-spawn       : {X Y : VType}
                      {C : CType}
                      {o : O}
                      {i : I} → 
                      (M : Γ ■ ⊢C⦂ C) → 
                      (N : Γ ⊢C⦂ X ! (o , i)) →
                      (K : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                      ---------------------------------------
                      let= (spawn M N) `in K
                      ↝↝
                      spawn M (let= N `in K)

    letrec-unfold   : {X : VType}
                      {C D : CType}
                      (M : Γ ∷ (X ⇒ C) ∷ X ⊢C⦂ C) →
                      (N : Γ ∷ (X ⇒ C) ⊢C⦂ D) →
                      ---------------------------------------------------------------------------------------------
                      (letrec M `in N)
                      ↝↝
                      N [ sub-id [ ƛ (letrec C-rename (ren-cong (ren-cong ren-wk)) M `in C-rename ren-exch M) ]s ]c

    promise-↑       : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (q : op' ∈ₒ o) →
                      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ proj₁ (payload op')) → 
                      (M : Γ ∷ proj₁ (payload op) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      --------------------------------------------------------------------------------------------------------
                      (promise op ∣ p ↦ M `in (↑ op' q V N))
                      ↝↝
                      ↑ op' q (strengthen-val {Δ = X ∷ₗ []} (proj₂ (payload op')) V) (promise op ∣ p ↦ M `in N)

    promise-spawn   : {X Y : VType}
                      {C : CType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (M : Γ ∷ proj₁ (payload op) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ■ ⊢C⦂ C) → 
                      (K : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      ---------------------------------------------------------------------------------------------------------
                      (promise op ∣ p ↦ M `in (spawn N K))
                      ↝↝
                      spawn (strengthen-■-c {Γ' = []} {Δ = X ∷ₗ []} N) (promise op ∣ p ↦ M `in K)

    ↓-return        : {X : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) →
                      (W : Γ ⊢V⦂ X) →
                      ----------------------------------------------------------------
                      ↓ {o = o} {i = i} op V (return W)
                      ↝↝
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
                      ---------------------------------
                      ↓ op V (↑ op' p W M)
                      ↝↝
                      ↑ op' (↓ₑ-⊑ₒ op' p) W (↓ op V M)


    ↓-promise-op    : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) → 
                      (M : Γ ∷ proj₁ (payload op) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      --------------------------------------------------------------------------------------------------------------------------------------------------------
                      ↓ op V (promise op ∣ p ↦ M `in N )
                      ↝↝
                      (let= (coerce (⊑ₒ-trans (proj₁ (⊑-proj p (proj₂ (proj₂ (⊑-just p))))) (↓ₑ-⊑ₒ-o' {o = o} (proj₂ (proj₂ (⊑-just p)))))
                                    (⊑ᵢ-trans (proj₂ (⊑-proj p (proj₂ (proj₂ (⊑-just p))))) (↓ₑ-⊑ₒ-i' {o = o} (proj₂ (proj₂ (⊑-just p)))))
                                    (M [ (sub-id [ V ]s)
                                       [ ƛ (promise op ∣ subst (λ oi → (o' , i') ⊑ oi) (sym ite-≡) ⊑-refl ↦ C-rename (ren-cong (ren-cong ren-wk)) M `in return (` Hd)) ]s ]c))
                       `in (↓ op (V-rename ren-wk V) N))

    ↓-promise-op'   : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₛ} →
                      (p : ¬ op ≡ op') →
                      (q : (o' , i') ⊑ lkpᵢ op' i) →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) → 
                      (M : Γ ∷ proj₁ (payload op') ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op' ↦ just (o' , i') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      -----------------------------------------------------------------------------------------------------------
                      ↓ op V (promise op' ∣ q ↦ M `in N )
                      ↝↝
                      promise op' ∣ (lkpᵢ-↓ₑ-neq-⊑ {o = o} {i = i} p q) ↦ M `in ↓ op (V-rename ren-wk V) N                                     

    ↓-spawn         : {X : VType}
                      {C : CType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) →
                      (M : Γ ■ ⊢C⦂ C) →
                      (N : Γ ⊢C⦂ X ! (o , i)) →
                      --------------------------------
                      ↓ op V (spawn M N)
                      ↝↝
                      spawn M (↓ op V N)

    await-promise   : {X : VType}
                      {C : CType} → 
                      (V : Γ ⊢V⦂ X) → 
                      (M : Γ ∷ X ⊢C⦂ C) →
                      --------------------
                      await ⟨ V ⟩ until M
                      ↝↝
                      M [ sub-id [ V ]s ]c

    box-unbox       : {X : VType}
                      {C : CType} →
                      (V : Γ ■ ⊢V⦂ X) →
                      (M : Γ ∷ X ⊢C⦂ C) →
                      ----------------------------------------
                      unbox (□ V) `in M
                      ↝↝
                      M [ ⟨ sub-id ,, ■-str-v {Γ' = []} V ⟩ ]c


    -- INLINED EVALUATION CONTEXT RULES

    context-let      : {X Y : VType}
                       {o : O}
                       {i : I} → 
                       {M M' : Γ ⊢C⦂ X ! (o , i)} →
                       {N : Γ ∷ X ⊢C⦂ Y ! (o , i)} →
                       M ↝↝ M' → 
                       -----------------------------
                       let= M `in N
                       ↝↝
                       let= M' `in N

    context-↑        : {X : VType}
                       {o : O}
                       {i : I}
                       {op : Σₛ}
                       {p : op ∈ₒ o}
                       {V : Γ ⊢V⦂ proj₁ (payload op)}
                       {M N : Γ ⊢C⦂ X ! (o , i)} →
                       M ↝↝ N →
                       ---------------------------
                       ↑ op p V M
                       ↝↝
                       ↑ op p V N

    context-↓        : {X : VType}
                       {o : O}
                       {i : I}
                       {op : Σₛ}
                       {V : Γ ⊢V⦂ proj₁ (payload op)}
                       {M N : Γ ⊢C⦂ X ! (o , i)} →
                       M ↝↝ N →
                       ------------------------------
                       ↓ op V M
                       ↝↝
                       ↓ op V N

    context-promise : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      {r : (o' , i') ⊑ lkpᵢ op i}
                      {M : Γ ∷ proj₁ (payload op) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o' , i')} →
                      {N N' : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)} →
                      N ↝↝ N' →
                      --------------------------------------------------------------------------------------------------------
                      promise op ∣ r ↦ M `in N
                      ↝↝
                      promise op ∣ r ↦ M `in N'

    context-spawn   : {C D : CType}
                      {M : Γ ■ ⊢C⦂ C}
                      {N N' : Γ ⊢C⦂ D} →
                      N ↝↝ N' →
                      ------------------
                      spawn M N
                      ↝↝
                      spawn M N'

    context-coerce  : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      {M N : Γ ⊢C⦂ X ! (o , i)} →
                      M ↝↝ N →
                      ---------------------------
                      coerce p q M
                      ↝↝
                      coerce p q N

    -- COERCION RULES

    coerce-return   : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      (V : Γ ⊢V⦂ X) →
                      --------------------------------
                      coerce p q (return V) ↝↝ return V

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
                      ↝↝
                      ↑ op (p op r) V (coerce p q M)

    coerce-promise  : {X Y : VType}
                      {o o' o'' : O}
                      {i i' i'' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'}
                      {op : Σₛ} →
                      (r : (o'' , i'') ⊑ lkpᵢ op i )
                      (M : Γ ∷ proj₁ (payload op) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o'' , i'') ]ᵢ))) ⊢C⦂ ⟨ X ⟩ ! (o'' , i'')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      -------------------------------------------------------------------------------------------------------------
                      coerce p q (promise op ∣ r ↦ M `in N)
                      ↝↝
                      promise_∣_↦_`in_ op (subst (λ oi → (o'' , i'') ⊑ oi) (sym (lkpᵢ-next-eq q (proj₂ (proj₂ (⊑-just r)))))
                                            (⊑-trans r (proj₂ (proj₂ (⊑-just r))) (
                                              (lkpᵢ-next-⊑ₒ q (proj₂ (proj₂ (⊑-just r)))) ,
                                              (lkpᵢ-next-⊑ᵢ q (proj₂ (proj₂ (⊑-just r)))))))
                                          M
                                          (coerce p q N)

    coerce-spawn   : {X : VType}
                     {C : CType}
                     {o o' : O}
                     {i i' : I}
                     {p : o ⊑ₒ o'}
                     {q : i ⊑ᵢ i'} →
                     (M : Γ ■ ⊢C⦂ C) →
                     (N : Γ ⊢C⦂ X ! (o , i)) → 
                     -------------------------
                     coerce p q (spawn M N)
                     ↝↝
                     spawn M (coerce p q N)


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

↝↝-to-↝ : {Γ : Ctx}
          {C : CType}
          {M N : Γ ⊢C⦂ C} → 
          M ↝↝ N →
          -----------------
          M ↝ N

↝↝-to-↝ (apply M V) =
  apply M V
↝↝-to-↝ (let-return V N) =
  let-return V N
↝↝-to-↝ (let-↑ p V M N) =
  let-↑ p V M N
↝↝-to-↝ (let-promise p M₁ M₂ N) =
  let-promise p M₁ M₂ N
↝↝-to-↝ (let-spawn M N K) =
  let-spawn M N K
↝↝-to-↝ (letrec-unfold M N) =
  letrec-unfold M N
↝↝-to-↝ (promise-↑ p q V M N) =
  promise-↑ p q V M N
↝↝-to-↝ (promise-spawn p M N K) =
  promise-spawn p M N K
↝↝-to-↝ (↓-return V W) =
  ↓-return V W
↝↝-to-↝ (↓-↑ p V W M) =
  ↓-↑ p V W M
↝↝-to-↝ (↓-promise-op p V M N) =
  ↓-promise-op p V M N
↝↝-to-↝ (↓-promise-op' p q V M N) =
  ↓-promise-op' p q V M N
↝↝-to-↝ (↓-spawn V M N) =
  ↓-spawn V M N
↝↝-to-↝ (await-promise V M) =
  await-promise V M
↝↝-to-↝ (box-unbox V M) =
  box-unbox V M
↝↝-to-↝ (context-let r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-↑ r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-↓ r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-promise r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-spawn r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-coerce r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (coerce-return V) =
  coerce-return V
↝↝-to-↝ (coerce-↑ p V M) =
  coerce-↑ p V M
↝↝-to-↝ (coerce-promise p M N) =
  coerce-promise p M N
↝↝-to-↝ (coerce-spawn M N) =
  coerce-spawn M N


mutual
  ↝-context-to-↝↝ : {Γ : Ctx}
                    {Δ : BCtx}
                    {C : CType} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) → 
                    {M N : (Γ ⋈ Δ) ⊢C⦂ hole-ty-e E} → 
                    M ↝ N →
                    ---------------------------------
                    E [ M ] ↝↝ E [ N ]

  ↝-context-to-↝↝ [-] r =
    ↝-to-↝↝ r
  ↝-context-to-↝↝ (let= E `in x) r =
    context-let (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (↑ op p V E) r =
    context-↑ (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (↓ op V E) r =
    context-↓ (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (promise op ∣ p ↦ M `in E) r =
    context-promise (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (spawn M E) r =
    context-spawn (↝-context-to-↝↝ E r) 
  ↝-context-to-↝↝ (coerce p q E) r =
    context-coerce (↝-context-to-↝↝ E r)
  
 
  ↝-to-↝↝ : {Γ : Ctx}
            {C : CType}
            {M N : Γ ⊢C⦂ C} → 
            M ↝ N →
            -----------------
            M ↝↝ N

  ↝-to-↝↝ (apply M V) =
    apply M V
  ↝-to-↝↝ (let-return V N) =
    let-return V N
  ↝-to-↝↝ (let-↑ p V M N) =
    let-↑ p V M N
  ↝-to-↝↝ (let-promise p M₁ M₂ N) =
    let-promise p M₁ M₂ N
  ↝-to-↝↝ (let-spawn M N K) =
    let-spawn M N K
  ↝-to-↝↝ (letrec-unfold M N) =
    letrec-unfold M N
  ↝-to-↝↝ (promise-↑ p q V M N) =
    promise-↑ p q V M N
  ↝-to-↝↝ (promise-spawn p M N K) =
    promise-spawn p M N K
  ↝-to-↝↝ (↓-return V W) =
    ↓-return V W
  ↝-to-↝↝ (↓-↑ p V W M) =
    ↓-↑ p V W M
  ↝-to-↝↝ (↓-promise-op p V M N) =
    ↓-promise-op p V M N
  ↝-to-↝↝ (↓-promise-op' p q V M N) =
    ↓-promise-op' p q V M N
  ↝-to-↝↝ (↓-spawn V M N) =
    ↓-spawn V M N
  ↝-to-↝↝ (await-promise V M) =
    await-promise V M
  ↝-to-↝↝ (box-unbox V M) =
    box-unbox V M
  ↝-to-↝↝ (context E r) =
    ↝-context-to-↝↝ E r
  ↝-to-↝↝ (coerce-return V) =
    coerce-return V
  ↝-to-↝↝ (coerce-↑ p V M) =
    coerce-↑ p V M
  ↝-to-↝↝ (coerce-promise p M N) =
    coerce-promise p M N
  ↝-to-↝↝ (coerce-spawn M N) =
    coerce-spawn M N


-- FINALITY OF RESULT FORMS

run-invert-let : {Γ : MCtx}
                 {X Y : VType}
                 {o : O}
                 {i : I}
                 {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ X ! (o , i)}
                 {N : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢C⦂ Y ! (o , i)} →
                 RunResult⟨ Γ ∣ let= M `in N ⟩ →
                 -------------------------------------
                 RunResult⟨ Γ ∣ M ⟩

run-invert-let (awaiting (let-in R)) =
  awaiting R


run-invert-↓ : {Γ : MCtx}
               {X : VType}
               {o : O}
               {i : I}
               {op : Σₛ}
               {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ proj₁ (payload op)}
               {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ X ! (o , i)} →
               RunResult⟨ Γ ∣ ↓ op V M ⟩ → 
               -----------------------------------
               RunResult⟨ Γ ∣ M ⟩

run-invert-↓ (awaiting (interrupt await)) =
  awaiting await
run-invert-↓ (awaiting (interrupt (let-in R))) =
  awaiting (let-in R)
run-invert-↓ (awaiting (interrupt (interrupt R))) =
  awaiting (interrupt R)
run-invert-↓ (awaiting (interrupt (coerce R))) =
  awaiting (coerce R)


run-invert-promise : {Γ : MCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I}
                     {op : Σₛ}
                     {p : (o' , i') ⊑ lkpᵢ op i}
                     {M : (⟨⟨ Γ ⟩⟩ ∷ proj₁ (payload op)) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ (⟨ X ⟩ ! (o' , i'))}
                     {N : (⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩) ⊢C⦂ (Y ! (o , i))} → 
                     RunResult⟨ Γ ∣ (promise op ∣ p ↦ M `in N) ⟩ →
                     ----------------------------------------------------------------------------------------------------------------
                     RunResult⟨ Γ ∺ X ∣ N ⟩

run-invert-promise (promise R) =
  R


run-invert-coerce : {Γ : MCtx}
                    {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'}
                    {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ X ! (o , i)} →
                    RunResult⟨ Γ ∣ coerce p q M ⟩ →
                    -------------------------------
                    RunResult⟨ Γ ∣ M ⟩

run-invert-coerce (awaiting (coerce R)) =
  awaiting R


run-apply-⊥ : {Γ : MCtx}
              {X : VType}
              {C : CType}
              {M : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢C⦂ C}
              {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X} →
              RunResult⟨ Γ ∣ ƛ M · V ⟩ →
              --------------------------
              ⊥

run-apply-⊥ (awaiting ())


run-↑-⊥ : {Γ : MCtx}
          {X : VType}
          {o : O}
          {i : I}
          {op : Σₛ}
          {p : op ∈ₒ o}
          {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ proj₁ (payload op)}
          {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ (X ! (o , i))} → 
          RunResult⟨ Γ ∣ ↑ op p V M ⟩ →
          --------------------------------
          ⊥
                 
run-↑-⊥ (awaiting ())


run-spawn-⊥ : {Γ : MCtx}
              {C D : CType}
              {M : ⟨⟨ Γ ⟩⟩ ■ ⊢C⦂ C}
              {N : ⟨⟨ Γ ⟩⟩ ⊢C⦂ D} →
              RunResult⟨ Γ ∣ spawn M N ⟩ →
              ----------------------------
              ⊥

run-spawn-⊥ (awaiting ())

              
run-let-return-⊥ : {Γ : MCtx}
                   {X Y : VType}
                   {o : O}
                   {i : I}
                   {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X}
                   {N : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢C⦂ (Y ! (o , i))} →
                   RunResult⟨ Γ ∣ let= return V `in N ⟩ →
                   --------------------------------------
                   ⊥

run-let-return-⊥ (awaiting (let-in ()))


run-let-promise-⊥ : {Γ : MCtx}
                    {X Y Z : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ}
                    {p : (o' , i') ⊑ lkpᵢ op i}
                    {M₁ : (⟨⟨ Γ ⟩⟩ ∷ proj₁ (payload op)) ∷ (𝟙 ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ⊢C⦂ (⟨ X ⟩ ! (o' , i'))}
                    {M₂ : (⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩) ⊢C⦂ (Y ! (o , i))}
                    {N  : (⟨⟨ Γ ⟩⟩ ∷ Y) ⊢C⦂ (Z ! (o , i))} →
                    RunResult⟨ Γ ∣ let= promise op ∣ p ↦ M₁ `in M₂ `in N ⟩ →
                    ------------------------------------------------------------------------------------------------------------------
                    ⊥

run-let-promise-⊥ (awaiting (let-in ()))


run-let-spawn-⊥ : {Γ : MCtx}
                  {X Y : VType}
                  {C : CType}
                  {o : O}
                  {i : I}
                  {M : ⟨⟨ Γ ⟩⟩ ■ ⊢C⦂ C}
                  {N : ⟨⟨ Γ ⟩⟩ ⊢C⦂ (X ! (o , i))}
                  {K  : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢C⦂ (Y ! (o , i))} →
                  RunResult⟨ Γ ∣ let= spawn M N `in K ⟩ →
                  ----------------------------------------------------------
                  ⊥

run-let-spawn-⊥ (awaiting (let-in ()))


run-finality-↝↝ : {Γ : MCtx}
                  {C : CType}
                  {M N : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C} → 
                  RunResult⟨ Γ ∣ M ⟩ →
                  M ↝↝ N →
                  -----------------------
                  ⊥

run-finality-↝↝ (awaiting ()) (apply M V)
run-finality-↝↝ R (let-return V N) =
  run-let-return-⊥ R
run-finality-↝↝ R (let-↑ p V M N) =
  run-↑-⊥ (run-invert-let R)
run-finality-↝↝ R (let-promise p M₁ M₂ N) =
  run-let-promise-⊥ R
run-finality-↝↝ R (let-spawn M N K) =
  run-let-spawn-⊥ R
run-finality-↝↝ (awaiting ()) (letrec-unfold M N)
run-finality-↝↝ (promise (awaiting ())) (promise-↑ p q V M N)
run-finality-↝↝ (promise (awaiting ())) (promise-spawn p M N K)
run-finality-↝↝ (awaiting (interrupt ())) (↓-return V W)
run-finality-↝↝ (awaiting (interrupt ())) (↓-↑ p V W M)
run-finality-↝↝ (awaiting (interrupt ())) (↓-promise-op p V M N)
run-finality-↝↝ (awaiting (interrupt ())) (↓-promise-op' p q V M N)
run-finality-↝↝ (awaiting (interrupt ())) (↓-spawn V M N)
run-finality-↝↝ (awaiting ()) (await-promise V M)
run-finality-↝↝ (awaiting ()) (box-unbox V M)
run-finality-↝↝ R (context-let r) =
  run-finality-↝↝ (run-invert-let R) r
run-finality-↝↝ R (context-↑ r) =
  run-↑-⊥ R
run-finality-↝↝ R (context-↓ r) =
  run-finality-↝↝ (run-invert-↓ R) r
run-finality-↝↝ R (context-promise r) =
  run-finality-↝↝ (run-invert-promise R) r
run-finality-↝↝ R (context-coerce r) =
  run-finality-↝↝ (run-invert-coerce R) r
run-finality-↝↝ (awaiting (coerce ())) (coerce-return V)
run-finality-↝↝ (awaiting (coerce ())) (coerce-↑ p V M)
run-finality-↝↝ (awaiting (coerce ())) (coerce-promise p M N)
run-finality-↝↝ (awaiting (coerce ())) (coerce-spawn M N)


comp-finality-↝↝ : {Γ : MCtx}
                   {C : CType}
                   {M N : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C} → 
                   CompResult⟨ Γ ∣ M ⟩ →
                   M ↝↝ N →
                   -----------------------
                   ⊥

comp-finality-↝↝ (comp R) r =
  run-finality-↝↝ R r
comp-finality-↝↝ (signal R) (context-↑ r) =
  comp-finality-↝↝ R r
comp-finality-↝↝ (spawn R) (context-spawn r) =
  comp-finality-↝↝ R r


comp-finality : {Γ : MCtx}
                {C : CType}
                {M N : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C} → 
                CompResult⟨ Γ ∣ M ⟩ →
                M ↝ N →
                -----------------------
                ⊥

comp-finality R r =
  comp-finality-↝↝ R (↝-to-↝↝ r)


