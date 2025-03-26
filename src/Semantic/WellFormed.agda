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

wellFormed : Memoryₜ → 𝒜 → Set
wellFormed mₜ a = ∀ x → lookup a x <ₙ length (lookup mₜ x)

data wellFormedStm : ASTStmS → Memoryₜ → 𝒜 → Set where
  SkipWF : {m : Memoryₜ} {a : 𝒜}
    → wellFormed m a
    → wellFormedStm Skip m a
  SeqWF : {s s' : ASTStmS} {m : Memoryₜ} {a : 𝒜}
    → wellFormedStm s m a
    → wellFormedStm s' m (proj₂ (transStm s a))
    → wellFormedStm (Seq s s') m a
  AssignWF : {v : Fin n} {e : ASTExpS} {m : Memoryₜ} {a : 𝒜}
    → wellFormed m a
    → wellFormedStm (v := e) m a
  AssignBrWF : {v : Fin n} {e : ASTExpS} {m : Memoryₜ} {a : 𝒜}  
    → wellFormed m (proj₂ (transStm ⟦ v := e ⟧ a))
    → wellFormedStm ⟦ v := e ⟧ m a
  IfWF : {e : ASTExpS} {s s' : ASTStmS} {m : Memoryₜ} {a : 𝒜}
    → wellFormed m (proj₂ (transStm (If0 e s s') a))
    → wellFormedStm s m a
    → wellFormedStm s' m a
    → wellFormedStm (If0 e s s') m a
  WhileWF : {e : ASTExpS} {s : ASTStmS} {m : Memoryₜ} {a : 𝒜}
    → wellFormed m (merge𝒜 a (proj₂ (transStm s a)))
    → wellFormedStm s m (merge𝒜 a (proj₂ (transStm s a)))
    → wellFormedStm (While e s) m a

lengthUpdateL=lengthL : (list : List ℕ) → (index : ℕ) → (value : ℕ) 
  → length (safeListUpdate list index value) ≡ length list
lengthUpdateL=lengthL [] _ _ = refl
lengthUpdateL=lengthL (x ∷ xs) zero _ = refl
lengthUpdateL=lengthL (x ∷ xs) (suc index) value = cong suc (lengthUpdateL=lengthL xs index value)

wellFormed-trans : {s : ASTStm} {mₜ mₜ' : Memoryₜ} {a : 𝒜} 
  → wellFormed mₜ a 
  → ⟨ s , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ' a
wellFormed-trans wFmₜa Skipₜ = wFmₜa
wellFormed-trans {_} {mₜ} {mₜ'} {a} wFmₜa (Assignₜ {_} {x , index} {e}) varName with varName ≟f x
...   | yes vN=x = let -- lookup mt' x == (safeListUpdate ...)
                       lmₜ'x=lUmₜx = lookupx∘changex x mₜ
                       -- length (safeListUpdate (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)) ≡ length (lookup mₜ x)
                       lenlUmₜx=lenlmₜ'x = lengthUpdateL=lengthL (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)
                       -- length (lookup (mₜ [ x ]≔ v) x) ≡ length (lookup mₜ x)
                       lenlmₜ'x=lenlmₜx = trans (cong length lmₜ'x=lUmₜx) lenlUmₜx=lenlmₜ'x
                       -- length (lookup (mₜ [ varName ]≔ v) varName) ≡ length (lookup mₜ varName)
                       lenlmₜ'vN=lenlmₜvN = subst (\v → length (lookup mₜ' v) ≡ length (lookup mₜ v)) (sym vN=x) lenlmₜ'x=lenlmₜx
                    in subst (\v → lookup a varName <ₙ v) (sym lenlmₜ'vN=lenlmₜvN) (wFmₜa varName)
...   | no vN<>x = subst (\v → lookup a varName <ₙ length v) (sym (lookupy∘changex x varName mₜ vN<>x)) (wFmₜa varName)
wellFormed-trans {_} {_} {_} {a} wFmₜa (Seqₜ d d') = 
  wellFormed-trans {_} {_} {_} {a} (wellFormed-trans {_} {_} {_} {a} wFmₜa d) d'
wellFormed-trans {_} {_} {_} {a} wFmₜa (IfTₜ _ _ d) = wellFormed-trans {_} {_} {_} {a} wFmₜa d
wellFormed-trans {_} {_} {_} {a} wFmₜa (IfFₜ _ d) = wellFormed-trans {_} {_} {_} {a} wFmₜa d
wellFormed-trans {_} {_} {_} {a} wFmₜa (WhileTₜ _ _ d d') = 
  wellFormed-trans {_} {_} {_} {a} (wellFormed-trans {_} {_} {_} {a} wFmₜa d) d'
wellFormed-trans wFmₜa (WhileFₜ _) = wFmₜa

wellFormedStmTransitive : {s : ASTStmS} {sₜ : ASTStm} {m m' : Memoryₜ} {a : 𝒜}
  → wellFormedStm s m a
  → ⟨ sₜ , m ⟩⇓ₜ m'
  → wellFormedStm s m' a
wellFormedStmTransitive {_} {_} {_} {_} {a} (SkipWF wFmₜa) d = 
  SkipWF (wellFormed-trans {_} {_} {_} {a} wFmₜa d)
wellFormedStmTransitive {_} {_} {_} {_} {a} (AssignWF wFmₜa) d = 
  AssignWF (wellFormed-trans {_} {_} {_} {a} wFmₜa d)
wellFormedStmTransitive (AssignBrWF {v} {e} {_} {a} wFmₜa') d = 
  AssignBrWF (wellFormed-trans {_} {_} {_} {proj₂ (transStm ⟦ v := e ⟧ a)} wFmₜa' d)
wellFormedStmTransitive (SeqWF wFsmₜa wFs'mₜa) d = 
  SeqWF (wellFormedStmTransitive wFsmₜa d) 
        (wellFormedStmTransitive wFs'mₜa d) 
wellFormedStmTransitive (IfWF {e} {s} {s'} {_} {a} wFmₜa' wFsmₜa wFs'mₜa) d = 
  IfWF (wellFormed-trans {_} {_} {_} {proj₂ (transStm (If0 e s s') a)} wFmₜa' d) 
       (wellFormedStmTransitive wFsmₜa d) 
       (wellFormedStmTransitive wFs'mₜa d) 
wellFormedStmTransitive (WhileWF {e} {s} {_} {a} wFmₜa' wFsmₜa') d = 
  WhileWF (wellFormed-trans {_} {_} {_} {merge𝒜 a (proj₂ (transStm s a))} wFmₜa' d) 
          (wellFormedStmTransitive wFsmₜa' d) 