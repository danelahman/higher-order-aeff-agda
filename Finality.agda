open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
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

    let-promise     : {X Y Z S : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (M₁ : Γ ∷ proj₁ (payload op) ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (V : Γ ⊢V⦂ S) → 
                      (M₂ : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      (N : Γ ∷ Y ⊢C⦂ Z ! (o , i)) →
                      ---------------------------------------------------------------------------------------------------------
                      let= (promise op ∣ p ↦ M₁ at V `in M₂) `in N
                      ↝↝
                      (promise op ∣ p ↦ M₁ at V `in (let= M₂ `in (C-rename (ren-cong ren-wk) N)))

    let-await       : {X Y Z : VType}
                      {o : O}
                      {i : I} →
                      (V : Γ ⊢V⦂ ⟨ X ⟩) →
                      (M : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                      (N : Γ ∷ Y ⊢C⦂ Z ! (o , i)) → 
                      -------------------------------------------------------
                      let= (await V until M) `in N
                      ↝↝
                      await V until (let= M `in C-rename (ren-cong ren-wk) N)

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

    promise-↑       : {X Y S : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (q : op' ∈ₒ o) →
                      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ proj₁ (payload op')) → 
                      (M : Γ ∷ proj₁ (payload op) ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (W : Γ ⊢V⦂ S) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      -------------------------------------------------------------------------------------------------------------
                      (promise op ∣ p ↦ M at W `in (↑ op' q V N))
                      ↝↝
                      ↑ op' q (strengthen-val {Δ = X ∷ₗ []} (proj₂ (payload op')) V) (promise op ∣ p ↦ M at W `in N)

    promise-spawn   : {X Y S : VType}
                      {C : CType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (M : Γ ∷ proj₁ (payload op) ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (V : Γ ⊢V⦂ S) →
                      (N : Γ ∷ ⟨ X ⟩ ■ ⊢C⦂ C) → 
                      (K : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      ---------------------------------------------------------------------------------------------------------
                      (promise op ∣ p ↦ M at V `in (spawn N K))
                      ↝↝
                      spawn (strengthen-■-c {Γ' = []} {Δ = X ∷ₗ []} N) (promise op ∣ p ↦ M at V `in K)

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


    ↓-promise-op    : {X Y S : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : (o' , i') ⊑ lkpᵢ op i) →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) → 
                      (M : Γ ∷ proj₁ (payload op) ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (W : Γ ⊢V⦂ S) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      --------------------------------------------------------------------------------------------------------------------------------------------------------
                      ↓ op V (promise op ∣ p ↦ M at W `in N )
                      ↝↝
                      (let= (coerce (⊑ₒ-trans (proj₁ (⊑-proj p (proj₂ (proj₂ (⊑-just p))))) (↓ₑ-⊑ₒ-o' {o = o} (proj₂ (proj₂ (⊑-just p)))))
                                    (⊑ᵢ-trans (proj₂ (⊑-proj p (proj₂ (proj₂ (⊑-just p))))) (↓ₑ-⊑ₒ-i' {o = o} (proj₂ (proj₂ (⊑-just p)))))
                                    (M [ sub-id
                                         [ V ]s
                                         [ ƛ (promise op ∣ subst (λ oi → (o' , i') ⊑ oi) (sym ite-≡) ⊑-refl
                                                         ↦ C-rename (ren-cong (ren-cong (ren-cong ren-wk))) M
                                                         at ` Hd
                                                         `in return (` Hd)) ]s
                                         [ W ]s ]c))
                                    --(M [ (sub-id [ V ]s)
                                    --   [ ƛ (promise op ∣ subst (λ oi → (o' , i') ⊑ oi) (sym ite-≡) ⊑-refl ↦ C-rename (ren-cong (ren-cong ren-wk)) M `in return (` Hd)) ]s ]c))
                       `in (↓ op (V-rename ren-wk V) N))

    ↓-promise-op'   : {X Y S : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₛ} →
                      (p : ¬ op ≡ op') →
                      (q : (o' , i') ⊑ lkpᵢ op' i) →
                      (V : Γ ⊢V⦂ proj₁ (payload op)) → 
                      (M : Γ ∷ proj₁ (payload op') ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op' ↦ just (o' , i') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o' , i')) →
                      (W : Γ ⊢V⦂ S) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      ---------------------------------------------------------------------------------------------------------------
                      ↓ op V (promise op' ∣ q ↦ M at W `in N )
                      ↝↝
                      promise op' ∣ (lkpᵢ-↓ₑ-neq-⊑ {o = o} {i = i} p q) ↦ M at W `in ↓ op (V-rename ren-wk V) N                                     

    ↓-await        : {X Y : VType}
                     {o : O}
                     {i : I}
                     {op : Σₛ} →
                     (V : Γ ⊢V⦂ proj₁ (payload op)) →
                     (W : Γ ⊢V⦂ ⟨ X ⟩) →
                     (M : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                     ------------------------------------------
                     ↓ op V (await W until M)
                     ↝↝
                     await W until (↓ op (V-rename ren-wk V) M)

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

    context-promise : {X Y S : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      {r : (o' , i') ⊑ lkpᵢ op i}
                      {M : Γ ∷ proj₁ (payload op) ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o' , i') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o' , i')} →
                      {V : Γ ⊢V⦂ S} →
                      {N N' : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)} →
                      N ↝↝ N' →
                      -------------------------------------------------------------------------------------------------------------
                      promise op ∣ r ↦ M at V `in N
                      ↝↝
                      promise op ∣ r ↦ M at V `in N'

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

    coerce-promise  : {X Y S : VType}
                      {o o' o'' : O}
                      {i i' i'' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'}
                      {op : Σₛ} →
                      (r : (o'' , i'') ⊑ lkpᵢ op i )
                      (M : Γ ∷ proj₁ (payload op) ∷ (S ⇒ (⟨ X ⟩ ! (∅ₒ , ∅ᵢ [ op ↦ just (o'' , i'') ]ᵢ))) ∷ S ⊢C⦂ ⟨ X ⟩ ! (o'' , i'')) →
                      (V : Γ ⊢V⦂ S) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)) →
                      -------------------------------------------------------------------------------------------------------------
                      coerce p q (promise op ∣ r ↦ M at V `in N)
                      ↝↝
                      promise_∣_↦_at_`in_ op (subst (λ oi → (o'' , i'') ⊑ oi) (sym (lkpᵢ-next-eq q (proj₂ (proj₂ (⊑-just r)))))
                                               (⊑-trans r (proj₂ (proj₂ (⊑-just r))) (
                                                 (lkpᵢ-next-⊑ₒ q (proj₂ (proj₂ (⊑-just r)))) ,
                                                 (lkpᵢ-next-⊑ᵢ q (proj₂ (proj₂ (⊑-just r)))))))
                                             M
                                             V
                                             (coerce p q N)

    coerce-await   : {X Y : VType}
                     {o o' : O}
                     {i i' : I}
                     {p : o ⊑ₒ o'}
                     {q : i ⊑ᵢ i'} →
                     (V : Γ ⊢V⦂ ⟨ X ⟩) →
                     (M : Γ ∷ X ⊢C⦂ Y ! (o , i)) →
                     -----------------------------
                     coerce p q (await V until M)
                     ↝↝
                     await V until (coerce p q M)

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
↝↝-to-↝ (let-promise p M₁ V M₂ N) =
  let-promise p M₁ V M₂ N
↝↝-to-↝ (let-await V M N) =
  let-await V M N
↝↝-to-↝ (let-spawn M N K) =
  let-spawn M N K
↝↝-to-↝ (promise-↑ p q V M W N) =
  promise-↑ p q V M W N
↝↝-to-↝ (promise-spawn p M V N K) =
  promise-spawn p M V N K
↝↝-to-↝ (↓-return V W) =
  ↓-return V W
↝↝-to-↝ (↓-↑ p V W M) =
  ↓-↑ p V W M
↝↝-to-↝ (↓-promise-op p V M W N) =
  ↓-promise-op p V M W N
↝↝-to-↝ (↓-promise-op' p q V M W N) =
  ↓-promise-op' p q V M W N
↝↝-to-↝ (↓-await V W M) =
  ↓-await V W M
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
↝↝-to-↝ (coerce-promise p M V N) =
  coerce-promise p M V N
↝↝-to-↝ (coerce-await V M) =
  coerce-await V M
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
  ↝-context-to-↝↝ (promise op ∣ p ↦ M at V `in E) r =
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
  ↝-to-↝↝ (let-promise p M₁ V M₂ N) =
    let-promise p M₁ V M₂ N
  ↝-to-↝↝ (let-await V M N) =
    let-await V M N
  ↝-to-↝↝ (let-spawn M N K) =
    let-spawn M N K
  ↝-to-↝↝ (promise-↑ p q V M W N) =
    promise-↑ p q V M W N
  ↝-to-↝↝ (promise-spawn p M V N K) =
    promise-spawn p M V N K
  ↝-to-↝↝ (↓-return V W) =
    ↓-return V W
  ↝-to-↝↝ (↓-↑ p V W M) =
    ↓-↑ p V W M
  ↝-to-↝↝ (↓-promise-op p V M W N) =
    ↓-promise-op p V M W N
  ↝-to-↝↝ (↓-promise-op' p q V M W N) =
    ↓-promise-op' p q V M W N
  ↝-to-↝↝ (↓-await V W M) =
    ↓-await V W M
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
  ↝-to-↝↝ (coerce-promise p M V N) =
    coerce-promise p M V N
  ↝-to-↝↝ (coerce-await V M) =
    coerce-await V M
  ↝-to-↝↝ (coerce-spawn M N) =
    coerce-spawn M N


-- FINALITY OF RESULT FORMS

run-finality-↝↝ : {Γ : MCtx}
                  {C : CType}
                  {M N : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C} → 
                  RunResult⟨ Γ ∣ M ⟩ →
                  M ↝↝ N →
                  -----------------------
                  ⊥

run-finality-↝↝ (promise ()) (promise-↑ p q V M W N)
run-finality-↝↝ (promise ()) (promise-spawn p M V N K)
run-finality-↝↝ (promise R) (context-promise r) =
  run-finality-↝↝ R r


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



