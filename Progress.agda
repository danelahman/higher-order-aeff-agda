open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import EffectAnnotations
open import Preservation
open import Renamings
open import Substitutions renaming (⟨_,_⟩ to ⟨_,,_⟩)
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Progress where

-- MOBILE CONTEXTS (CONSIST OF ONLY VARIABLE BINDINGS)

data MCtx : Set where
  [] : MCtx
  _∺_ : MCtx → VType → MCtx


-- WRAPPING PROMISES AROUND A MOBILE CONTEXT

⟨⟨_⟩⟩ : MCtx → Ctx
⟨⟨ [] ⟩⟩ = []
⟨⟨ Γ ∺ X ⟩⟩ = ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩


-- RESULTS

data RunResult⟨_∣_⟩ (Γ : MCtx) : {C : CType} → ⟨⟨ Γ ⟩⟩ ⊢C⦂ C → Set where

  return   : {X : VType}
             {o : O}
             {i : I}
             (V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X) →
             ------------------------------------------
             RunResult⟨ Γ ∣ return {o = o} {i = i} V ⟩

  promise  : {X Y : VType}
             {o o' : O}
             {i i' : I}
             {op : Σₛ}
             {p : lkpᵢ op i ≡ just (o' , i')}
             {M : ⟨⟨ Γ ⟩⟩ ∷ proj₁ (payload op) ⊢C⦂ ⟨ X ⟩ ! (o' , i')}
             {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢C⦂ Y ! (o , i)} →
             RunResult⟨ Γ ∺ X ∣ N ⟩ →
             ----------------------------------------------------
             RunResult⟨ Γ ∣ promise op ∣ p ↦ M `in N ⟩

  awaiting : {C : CType}
             {Y : VType}
             {y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩}
             {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C} → 
             y ⧗ M →
             ---------------------
             RunResult⟨ Γ ∣ M ⟩

data CompResult⟨_∣_⟩ (Γ : MCtx) : {C : CType} → ⟨⟨ Γ ⟩⟩ ⊢C⦂ C → Set where

  comp   : {C : CType}
           {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C} →
           RunResult⟨ Γ ∣ M ⟩ →
           ---------------------
           CompResult⟨ Γ ∣ M ⟩

  signal : {X : VType}
           {o : O}
           {i : I}
           {op : Σₛ}
           {p : op ∈ₒ o}
           {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ proj₁ (payload op)}
           {M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ X ! (o , i)} →
           CompResult⟨ Γ ∣ M ⟩ →
           --------------------------------
           CompResult⟨ Γ ∣ ↑ op p V M ⟩


-- PROGRESS THEOREM FOR PROMISE-OPEN COMPUTATIONS

□-not-in-mctx : {Γ : MCtx} {X : VType} → □ X ∈ ⟨⟨ Γ ⟩⟩ → ⊥
□-not-in-mctx {Γ ∺ Y} (Tl-v x) =
  □-not-in-mctx x


⇒-not-in-mctx : {Γ : MCtx} {X : VType} {C : CType} → X ⇒ C ∈ ⟨⟨ Γ ⟩⟩ → ⊥
⇒-not-in-mctx {Γ ∺ Y} (Tl-v x) =
  ⇒-not-in-mctx x

{- THEOREM 3.3 -}  

progress : {Γ : MCtx}
           {C : CType} →
           (M : ⟨⟨ Γ ⟩⟩ ⊢C⦂ C) →
           -------------------------------
           (Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⊢C⦂ C ] (M ↝ N)
            ⊎
            CompResult⟨ Γ ∣ M ⟩)

progress (return V) =
  inj₂ (comp (return V))
progress (let= M `in N) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (let= [-] `in N) r)
... | inj₂ (comp (return V)) =
  inj₁ (_ , let-return V N)
... | inj₂ (comp (promise {_} {_} {_} {_} {_} {_} {_} {p} {M'} {M''} R)) =
  inj₁ (_ , let-promise p M' M'' N)
... | inj₂ (comp (awaiting R)) =
  inj₂ (comp (awaiting (let-in R)))
... | inj₂ (signal {_} {_} {_} {_} {p} {V} {M'} R) =
  inj₁ (_ , let-↑ p V M' N)
progress (letrec M `in N) =
  inj₁ (_ , letrec-unfold M N)
progress ((` x) · W) with ⇒-not-in-mctx x
... | ()
progress (ƛ M · W) =
  inj₁ (_ , apply M W)
progress (↑ op p V M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (↑ op p V [-]) r)
... | inj₂ R =
  inj₂ (signal R)
progress (↓ op V M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (↓ op V [-]) r)
... | inj₂ (comp (return W)) =
  inj₁ (_ , (↓-return V W))
... | inj₂ (comp (awaiting R)) =
  inj₂ (comp (awaiting (interrupt R)))
... | inj₂ (signal {X} {o} {i} {op'} {p} {W} {M'} R) =
  inj₁ (_ , (↓-↑ p V W M'))
... | inj₂ (comp (promise {_} {_} {_} {_} {_} {_} {op'} {p} {M'} {M''} R)) with decₛ op op'
... | yes refl =
  inj₁ (_ , ↓-promise-op p V M' M'')
... | no ¬q =
  inj₁ (_ , ↓-promise-op' ¬q p V M' M'')
progress (promise op ∣ p ↦ M `in N) with progress N
... | inj₁ (M' , r) =
  inj₁ (_ , context (promise op ∣ p ↦ M `in [-]) r)
... | inj₂ (comp R) =
  inj₂ (comp (promise R))
... | inj₂ (signal {_} {_} {_} {_} {q} {V} {M'} R) =
  inj₁ (_ , promise-↑ p q V M M')
progress (await ` x until M) =
  inj₂ (comp (awaiting await))
progress (await ⟨ V ⟩ until M) =
  inj₁ (_ , await-promise V M)
progress (unbox ` x `in M) with □-not-in-mctx x
... | ()
progress (unbox (□ V) `in M) =
  inj₁ (M [ ⟨ sub-of-ren ren-id ,, ■-str-v {Γ' = []} V ⟩ ]c , box-unbox V M)
progress (coerce p q M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (coerce p q [-]) r)
... | inj₂ (comp (return V)) =
  inj₁ (_ , coerce-return V)
... | inj₂ (comp (promise {_} {_} {_} {_} {_} {_} {op'} {r} {M'} {M''} R)) =
  inj₁ (_ , coerce-promise r M' M'')
... | inj₂ (comp (awaiting R)) =
  inj₂ (comp (awaiting (coerce R)))
... | inj₂ (signal {_} {_} {_} {_} {r} {V} {M'} R) =
  inj₁ (_ , coerce-↑ r V M')


-- PROGRESS THEOREM FOR CLOSED COMPUTATIONS

{- COROLLARY 3.4 -}

closed-progress : {C : CType} →
                  (M : [] ⊢C⦂ C) →
                  --------------------------
                  (Σ[ N ∈ [] ⊢C⦂ C ] (M ↝ N)
                   ⊎
                   CompResult⟨ [] ∣ M ⟩)

closed-progress M =
  progress M

