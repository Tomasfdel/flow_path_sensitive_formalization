module Semantic.Correctness {n} where

open import Data.Empty
open import Data.Fin
  renaming (_≟_ to _≟f_)
open import Data.List
  hiding (lookup)
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Semantic.CorrectnessLemmas {n}
open import Semantic.Memory {n}
open import Semantic.Semantic {n}
open import Semantic.WellFormed {n}
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}

-- CORRECTNESS PROOF
-- Correctness of the program transformation for the While case.
whileCorrectness : {e : ASTExpS} {s : ASTStmS} {e' : ASTExp} {s' : ASTStm} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {A A₁ A₂ : 𝒜}
  → ⟨ While e s , m ⟩⇓ m'
  → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
  → e' ≡ transExp e A₁
  → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
  → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
  → A₂ ≡ proj₂ (transStm s A₁)
  → wellFormedStm (While e s) mₜ A
  → m ==ₘ mₜ - A₁
  → m' ==ₘ mₜ' - A₁

-- Correctness of the program transformation.
correctness : {s : ASTStmS} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {active : 𝒜}
  → ⟨ s , m ⟩⇓ m'
  → ⟨ proj₁ (transStm s active) , mₜ ⟩⇓ₜ mₜ'
  → wellFormedStm s mₜ active
  → m ==ₘ mₜ - active
  → m' ==ₘ mₜ' - (proj₂ (transStm s active))

-- TODO(minor): Rewrite this using a let and type explanations for the difficult terms like I did in AssignmentId.
-- Ceci dice que hay un formato en Agda que me puede permitir simplificar estas igualdades por transitividad.
correctness s@{x := e} {m} {.(m [ x ↦ ⟦ e ⟧ₑ m ])} {mₜ} {.(mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  Assign
  Assignₜ
  (AssignWF wFmₜa)
  meq varName with varName ≟f x
...              | yes vN=x = trans 
                                -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v'
                                (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v
                                  (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === lookup (m [ varName ]≔ ⟦ e ⟧ₑ m) varName
                                    (sym (cong (λ y → lookup (m [ y ]≔ ⟦ e ⟧ₑ m) varName) vN=x))
                                  -- lookup (m [ varName ]≔ v) varName ≡ v
                                    (lookupx∘changex varName m)
                                  )
                                  -- v === v'
                                  (expEquality {e} {m} {mₜ} meq refl refl)
                                ) 
                                -- v' === lookup (mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ) varName
                                (trans 
                                  -- v' === lookupOrDefault activeVar (lookup (mₜ [ varName ]≔ (safeListUpdate (lookup mₜ varName) activeVar v)) varName)
                                  (sym (lookupₜx∘changeₜx varName mₜ (wFmₜa varName)))
                                  -- lookupOrDefault activeVar (lookup (mₜ [ varName ]≔ (safeListUpdate (lookup mₜ varName) activeVar v)) varName)
                                  -- ===
                                  -- lookupOrDefault activeVar (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (lookup a x) v)) varName)
                                  (cong (λ y → lookupOrDefault (lookup a varName) (lookup (mₜ [ y , lookup a y ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ) varName)) vN=x)
                                )
...              | no vN!=x = trans 
                                (trans 
                                  (lookupy∘changex x varName m vN!=x)
                                  (meq varName)
                                ) 
                                (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))

-- TODO(minor): Same as above, rewrite this using a let and type explanations.
correctness s@{⟦ x := e ⟧} {m} {.(m [ x ↦ ⟦ e ⟧ₑ m ])} {mₜ} {mₜ'} {a} 
  AssignBr 
  Assignₜ 
  (AssignBrWF wFmₜa')
  meq varName with varName ≟f x
...              | yes vN=x = trans 
                                -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v'
                                (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v
                                  (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === lookup (m [ varName ]≔ ⟦ e ⟧ₑ m) varName
                                    (sym (cong (λ y → lookup (m [ y ]≔ ⟦ e ⟧ₑ m) varName) vN=x))
                                  -- lookup (m [ varName ]≔ v) varName ≡ v
                                    (lookupx∘changex varName m)
                                  )
                                  -- v === v'
                                  (expEquality {e} {m} {mₜ} meq refl refl)
                                )
                                -- v' ≡ lookupₜ mₜ' a' varName
                                (sym (trans
                                  -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) varName) (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')) varName)
                                  -- ===
                                  -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                  (trans
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) varName) (lookup (mₜ [ x , suc (lookup a x) ↦ v' ]ₜ) varName)
                                    -- ===
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    (trans 
                                      (cong (λ y → lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) y) (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (suc (lookup a x)) (⟦ transExp e a ⟧ₜ mₜ))) y)) vN=x)
                                      (cong (λ y → lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) y) (lookupx∘changex x mₜ))
                                    )
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    -- ===
                                    -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    (cong (λ y → lookupOrDefault y (safeListUpdate (lookup mₜ x) (suc (lookup a x)) (⟦ transExp e a ⟧ₜ mₜ))) (lookupx∘changex x a))
                                  )
                                  -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v') ≡ v'
                                  (listLookupx∘listUpdatex (suc (lookup a x)) (lookup mₜ x) (subst (λ y → y <ₙ length (lookup mₜ x)) (lookupx∘changex x a) (wFmₜa' x)))
                                ))
...              | no vN!=x = trans 
                                -- lookup m' varName ≡ lookupₜ mₜ active varName
                                (trans 
                                  -- lookup m' varName ≡ lookup m varName
                                  (lookupy∘changex x varName m vN!=x)
                                  -- lookup m varName ≡ lookupₜ mₜ active varName
                                  (meq varName)
                                )
                                -- lookupₜ mₜ active varName ≡ lookupₜ mₜ' active' varName
                                (trans
                                  -- lookupₜ mₜ a varName ≡ lookupₜ mₜ' a varName
                                  (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))
                                  -- lookupₜ mₜ' a varName ≡ lookupₜ mₜ' a' varName
                                  (cong (λ y → lookupOrDefault y (lookup mₜ' varName)) (sym (lookupy∘changex x varName a vN!=x)))  
                                )

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {.sT} {.sF} em=v v<>0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {v'} {sT'} {sF'} em'=v' v'<>0 (Seqₜ {m1} {m2} {m3} d' d''))
  (IfWF wFmₜa' wFsTmₜa _)
  meq = 
    let aT = proj₂ (transStm sT a)
        aF = proj₂ (transStm sF a)
        a' = merge𝒜 aT aF
        m1=mt1a' = correctness {sT} {m} {m'} {mₜ} {m2} {a} d d' wFsTmₜa meq 
        mt1a'=mt2a'' = :=𝒜-memEq {aT} {a'} d'' (wellFormed-trans {_} {_} {_} {a'} wFmₜa' d')
      in ==ₘ-trans {m'} {m2} {mₜ'} {aT} {a'} m1=mt1a' mt1a'=mt2a''

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {_} {_} em=v v<>0 d) 
  (IfFₜ em'=0 d') 
  _
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {v} {0} {a} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfF em=0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {_} {v} {_} {_} em'=v v<>0 d') 
  _
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {0} {v} {a} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a}
  (IfF {.m} {.m'} {.cond} {.sT} {.sF} em=0 d) 
  (IfFₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {sT'} {sF'} em'=0 (Seqₜ {m1} {m2} {m3} d' d''))
  (IfWF wFmₜa' _ wFsTmₜa)
  meq = 
    let aT = proj₂ (transStm sT a)
        aF = proj₂ (transStm sF a)
        a' = merge𝒜 aT aF
        m1=mt1a' = correctness {sF} {m} {m'} {mₜ} {m2} {a} d d' wFsTmₜa meq
        mt1a'=mt2a'' = :=𝒜-memEq {aF} {a'} d'' (wellFormed-trans {_} {_} {_} {a'} wFmₜa' d')
      in ==ₘ-trans {m'} {m2} {mₜ'} {aF} {a'} m1=mt1a' mt1a'=mt2a''

correctness {While cond s} {m} {m'} {mₜ} {mₜ'} {active} d 
  (Seqₜ {.mₜ} {mₜ1} {.mₜ'} dₜ dₜ') 
  wF@(WhileWF wFmₜa₁ _)
  meq = 
    let A₁ = merge𝒜 active (proj₂ (transStm s active))
        mtA=mt1A1 = :=𝒜-memEq {active} {A₁} {mₜ} {mₜ1} dₜ wFmₜa₁
     in whileCorrectness d dₜ' refl refl refl refl (wellFormedStmTransitive wF dₜ) (==ₘ-trans {m} {mₜ} {mₜ1} {active} {A₁} meq mtA=mt1A1)

correctness {Seq s s₁} {m} {m'} {mₜ} {mₜ'} {a} 
  (Seq {.m} {m2} {.m'} d d₁) 
  (Seqₜ {.mₜ} {mt2} {.mₜ'} d' d'') 
  (SeqWF wFsmₜa wFs₁mₜa')
  meq = 
    let h1 = correctness {s} {m} {m2} {mₜ} {mt2} d d' wFsmₜa meq
        wFs₁mₜ2a' = wellFormedStmTransitive wFs₁mₜa' d'
     in correctness d₁ d'' wFs₁mₜ2a' h1

correctness {Skip} {m} {.m} {mₜ} {.mₜ} {a} Skip Skipₜ _ meq = meq

-- whileCorrectness : {e : ASTExpS} {s : ASTStmS} {e' : ASTExp} {s' : ASTStm} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {A A₁ A₂ : 𝒜}
--   → ⟨ While e s , m ⟩⇓ m'
--   → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
--   → e' ≡ transExp e A₁
--   → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
--   → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
--   → A₂ ≡ proj₂ (transStm s A₁)
--   → wellFormedStm (While e s) mₜ A
--   → m ==ₘ mₜ - A₁
--   → m' ==ₘ mₜ' - A₁

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileF em=0) 
  (WhileFₜ em'=0) 
  refl refl refl refl _
  meq = meq

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileF em=0) 
  (WhileTₜ {_} {_} {_} {_} {v} {_} em'=v v<>0 _ _)
  refl refl refl refl _
  meq = 
    let em=em' = expEquality {e} {m} {_} {0} {v} {_} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileT {.m} {_} {_} {.e} {v} {_} em=v v<>0 _ _) 
  (WhileFₜ em'=0) 
  refl refl refl refl _
  meq = 
    let em=em' = expEquality {e} {m} {_} {v} {0} {_} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileT {.m} {m1} {.m'} {.e} {_} {.s} _ _ d d') 
  (WhileTₜ {.mₜ} {mₜ2} {.mₜ'} {cond'} {_} {s'} _ _ dₜ@(Seqₜ {.mₜ} {mₜ1} {.mₜ2} dₜ' dₜ'') dₜ''')
  refl refl refl refl
  wF@(WhileWF wFmₜa₁ wFsmₜA₁)
  meq = 
    let -- m1 ==ₘ mₜ1 - A2
        h = correctness {s} {m} {m1} {mₜ} {mₜ1} {A₁} d dₜ' wFsmₜA₁ meq
        -- mt1 - A2 ==ₘₜ mt2 - A1
        mt1A2=mt2A1 = :=𝒜-memEq {A₂} {A₁} {mₜ1} {mₜ2} dₜ'' (wellFormed-trans {_} {_} {_} {A₁} wFmₜa₁ dₜ')
        -- m' ==ₘ mₜ' - A1
     in whileCorrectness d' dₜ''' refl refl refl refl (wellFormedStmTransitive wF dₜ) (==ₘ-trans {m1} {mₜ1} {mₜ2} {A₂} {A₁} h mt1A2=mt2A1)
