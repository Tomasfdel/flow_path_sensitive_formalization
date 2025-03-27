module Semantic.WellFormed {n} where

open import Data.Fin
  renaming (_≟_ to _≟f_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Semantic.Memory {n}
open import Semantic.Semantic {n}
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}

-- A memory being well-formed relative to an active set means that it has
-- enough room to fit all variable subindices specified in the active set.
wellFormed : Memoryₜ → 𝒜 → Set
wellFormed mₜ A = ∀ x → lookup A x <ₙ length (lookup mₜ x)

-- A statement and memory being well-formed relative to an active set
-- means that all memory states executing the statement are well-formed.
data wellFormedStm : ASTStmS → Memoryₜ → 𝒜 → Set where
  SkipWF : {mₜ : Memoryₜ} {A : 𝒜}
    → wellFormed mₜ A
    → wellFormedStm Skip mₜ A
  AssignWF : {v : Fin n} {e : ASTExpS} {mₜ : Memoryₜ} {A : 𝒜}
    → wellFormed mₜ A
    → wellFormedStm (v := e) mₜ A
  AssignBrWF : {v : Fin n} {e : ASTExpS} {mₜ : Memoryₜ} {A : 𝒜}  
    → wellFormed mₜ (proj₂ (transStm ⟦ v := e ⟧ A))
    → wellFormedStm ⟦ v := e ⟧ mₜ A
  SeqWF : {s₁ s₂ : ASTStmS} {mₜ : Memoryₜ} {A : 𝒜}
    → wellFormedStm s₁ mₜ A
    → wellFormedStm s₂ mₜ (proj₂ (transStm s₁ A))
    → wellFormedStm (Seq s₁ s₂) mₜ A
  IfWF : {cond : ASTExpS} {sT sF : ASTStmS} {mₜ : Memoryₜ} {A : 𝒜}
    → wellFormed mₜ (proj₂ (transStm (If cond sT sF) A))
    → wellFormedStm sT mₜ A
    → wellFormedStm sF mₜ A
    → wellFormedStm (If cond sT sF) mₜ A
  WhileWF : {cond : ASTExpS} {s : ASTStmS} {mₜ : Memoryₜ} {A : 𝒜}
    → wellFormed mₜ (merge𝒜 A (proj₂ (transStm s A)))
    → wellFormedStm s mₜ (merge𝒜 A (proj₂ (transStm s A)))
    → wellFormedStm (While cond s) mₜ A

-- Auxiliary property: Updating a value of a list does not change its length.
lengthUpdateL=lengthL : (list : List ℕ) → (index : ℕ) → (value : ℕ) 
  → length (safeListUpdate list index value) ≡ length list
lengthUpdateL=lengthL [] _ _ = refl
lengthUpdateL=lengthL (_ ∷ _) zero _ = refl
lengthUpdateL=lengthL (_ ∷ xs) (suc index) value = cong suc (lengthUpdateL=lengthL xs index value)

wellFormed-trans : {s : ASTStm} {mₜ mₜ' : Memoryₜ} {A : 𝒜} 
  → wellFormed mₜ A 
  → ⟨ s , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ' A
wellFormed-trans wFmₜA Skipₜ = wFmₜA
wellFormed-trans {_} {mₜ} {mₜ'} {A} wFmₜA (Assignₜ {_} {x , index} {e}) varName with varName ≟f x
...   | yes vN=x = let lmₜ'x=lUmₜx : lookup mₜ' x ≡ safeListUpdate (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)
                       lmₜ'x=lUmₜx = lookupx∘changex x mₜ
                       lenlUmₜx=lenlmₜx : length (safeListUpdate (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)) ≡ length (lookup mₜ x)
                       lenlUmₜx=lenlmₜx = lengthUpdateL=lengthL (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)
                       lenlmₜ'x=lenlmₜx : length (lookup mₜ' x) ≡ length (lookup mₜ x)
                       lenlmₜ'x=lenlmₜx = trans (cong length lmₜ'x=lUmₜx) lenlUmₜx=lenlmₜx
                       lenlmₜ'vN=lenlmₜvN : length (lookup mₜ' varName) ≡ length (lookup mₜ varName)
                       lenlmₜ'vN=lenlmₜvN = subst (λ v → length (lookup mₜ' v) ≡ length (lookup mₜ v)) (sym vN=x) lenlmₜ'x=lenlmₜx
                    in subst (λ v → lookup A varName <ₙ v) (sym lenlmₜ'vN=lenlmₜvN) (wFmₜA varName)
...   | no vN<>x = let lmₜ'vN=lmₜvN : lookup mₜ' varName ≡ lookup mₜ varName
                       lmₜ'vN=lmₜvN = lookupy∘changex x varName mₜ vN<>x
                    in subst (λ v → lookup A varName <ₙ length v) (sym lmₜ'vN=lmₜvN) (wFmₜA varName)
wellFormed-trans {A = A} wFmₜA (Seqₜ d d') = 
  wellFormed-trans {A = A} (wellFormed-trans {A = A} wFmₜA d) d'
wellFormed-trans {A = A} wFmₜA (IfTₜ _ _ d) = wellFormed-trans {A = A} wFmₜA d
wellFormed-trans {A = A} wFmₜA (IfFₜ _ d) = wellFormed-trans {A = A} wFmₜA d
wellFormed-trans {A = A} wFmₜA (WhileTₜ _ _ d d') = 
  wellFormed-trans {A = A} (wellFormed-trans {A = A} wFmₜA d) d'
wellFormed-trans wFmₜA (WhileFₜ _) = wFmₜA

wellFormedStm-trans : {s : ASTStmS} {sₜ : ASTStm} {mₜ mₜ' : Memoryₜ} {A : 𝒜}
  → wellFormedStm s mₜ A
  → ⟨ sₜ , mₜ ⟩⇓ₜ mₜ'
  → wellFormedStm s mₜ' A
wellFormedStm-trans {A = A} (SkipWF wFmₜA) d = 
  SkipWF (wellFormed-trans {A = A} wFmₜA d)
wellFormedStm-trans {A = A} (AssignWF wFmₜA) d = 
  AssignWF (wellFormed-trans {A = A} wFmₜA d)
wellFormedStm-trans (AssignBrWF {v} {e} {_} {A} wFmₜA') d = 
  AssignBrWF (wellFormed-trans {A = proj₂ (transStm ⟦ v := e ⟧ A)} wFmₜA' d)
wellFormedStm-trans (SeqWF wFs₁mₜA wFs₂mₜA) d = 
  SeqWF (wellFormedStm-trans wFs₁mₜA d) 
        (wellFormedStm-trans wFs₂mₜA d) 
wellFormedStm-trans (IfWF {cond} {sT} {sF} {_} {A} wFmₜA' wFsTmₜA wFsFmₜA) d = 
  IfWF (wellFormed-trans {A = proj₂ (transStm (If cond sT sF) A)} wFmₜA' d) 
       (wellFormedStm-trans wFsTmₜA d) 
       (wellFormedStm-trans wFsFmₜA d) 
wellFormedStm-trans (WhileWF {s = s} {A = A} wFmₜA' wFsmₜA') d = 
  WhileWF (wellFormed-trans {A = merge𝒜 A (proj₂ (transStm s A))} wFmₜA' d) 
          (wellFormedStm-trans wFsmₜA' d) 