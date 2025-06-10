module Semantic.CorrectnessLemmas {n} where

open import Data.Fin
  hiding (_+_ ; pred)
open import Data.Fin.Properties
  hiding (≤∧≢⇒<)
open import Data.Nat 
  renaming (_≟_ to _≟ₙ_ ; _<_ to _<ₙ_ ; _≤_ to _≤ₙ_ )
open import Data.Nat.Properties
  hiding (<⇒≢ )
open import Data.Product 
open import Data.Vec.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Semantic.Memory {n}
open import Semantic.Semantic {n}
open import Semantic.WellFormed {n}
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}

-- LEMMA 3 OF THE CORRECTNESS PROOF
-- Semantic equality of an expression and its transformed counterpart.
expEquality : {e : ASTExpS} {m : Memory} {mₜ : Memoryₜ} {v v' : ℕ} {A : 𝒜}
  → m ==ₘ mₜ - A
  → ⟦ e ⟧ₑ m ≡ v 
  → ⟦ transExp e A ⟧ₜ mₜ ≡ v' 
  → v ≡ v' 
expEquality {IntVal _} _ refl refl = refl
expEquality {Var v} m=mₜ refl refl = m=mₜ v
expEquality {Add exp₁ exp₂} m=mₜ refl refl = 
  let expEq₁ = expEquality {exp₁} m=mₜ refl refl
      expEq₂ = expEquality {exp₂} m=mₜ refl refl
   in cong₂ _+_ expEq₁ expEq₂

-- LEMMA 4 OF THE CORRECTNESS PROOF
-- Equality of lookups of a variable in two memories after the active set assignment
-- for that variable has been executed. 
𝒜memEqPostVar : {currVar : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {A A' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ 𝒜assignAux currVar cV<n A' A , mₜ ⟩⇓ₜ mₜ'
  → currVar <ₙ toℕ varName
  → lookup mₜ varName ≡ lookup mₜ' varName
𝒜memEqPostVar {zero} {_} {z<n} {A} {A'} _ _ with lookup A' (fromℕ< z<n) ≟ₙ lookup A (fromℕ< z<n)
𝒜memEqPostVar {zero} Skipₜ _                                  | yes _ = refl
𝒜memEqPostVar {zero} {varName} {z<n} {_} {_} {mₜ} Assignₜ z<vN | no _ =
  let toNz=0 : toℕ (fromℕ< z<n) ≡ 0
      toNz=0 = toℕ-fromℕ< z<n
      toNz<toNvN : toℕ (fromℕ< z<n) <ₙ toℕ varName
      toNz<toNvN = subst (λ x → x <ₙ toℕ varName) (sym toNz=0) z<vN
      z<vN : (fromℕ< z<n) < varName
      z<vN = toℕ-cancel-< toNz<toNvN
      vN<>z : varName ≢  (fromℕ< z<n)
      vN<>z = ≢-sym (<⇒≢  z<vN)
   in sym (lookupy∘changex (fromℕ< z<n) varName mₜ vN<>z)
𝒜memEqPostVar {suc currVar'} {_} {cV<n} {A} {A'} _ _ with lookup A' (fromℕ< cV<n) ≟ₙ lookup A (fromℕ< cV<n)
𝒜memEqPostVar {suc _} (Seqₜ Skipₜ d) cV<vN    | yes _ = 𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
𝒜memEqPostVar {suc currVar'} {varName} {cV<n} {_} {_} {mₜ} {mₜ'} (Seqₜ {.mₜ} {mₜ1} {.mₜ'} Assignₜ d) cV<vN | no _ = 
  let toNcV=cV : toℕ (fromℕ< cV<n) ≡ suc currVar'
      toNcV=cV = toℕ-fromℕ< cV<n
      toNcV<toNvN : toℕ (fromℕ< cV<n) <ₙ toℕ varName
      toNcV<toNvN = subst (λ x → x <ₙ toℕ varName) (sym toNcV=cV) cV<vN
      fNcV<vN : (fromℕ< cV<n) < varName
      fNcV<vN = toℕ-cancel-< toNcV<toNvN
      vN<>fNcV : varName ≢  (fromℕ< cV<n)
      vN<>fNcV = ≢-sym (<⇒≢  fNcV<vN)
      lmₜvN=lmₜ1vN : lookup mₜ varName ≡ lookup mₜ1 varName
      lmₜvN=lmₜ1vN = sym (lookupy∘changex (fromℕ< cV<n) varName mₜ vN<>fNcV)
      lmₜ1vN=lmₜ'vN : lookup mₜ1 varName ≡ lookup mₜ' varName
      lmₜ1vN=lmₜ'vN = 𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
   in trans lmₜvN=lmₜ1vN lmₜ1vN=lmₜ'vN  

-- Equality of lookups of a variable in two memories before the active set assignment
-- for that variable has been executed. 
𝒜memEqPreVar : {currVar : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {A A' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ 𝒜assignAux currVar cV<n A' A , mₜ ⟩⇓ₜ mₜ'
  → toℕ varName ≤ₙ currVar
  → wellFormed mₜ A'
  → lookupₜ mₜ A varName ≡ lookupₜ mₜ' A' varName
𝒜memEqPreVar {zero} {zero} {_} {A} {A'} _ _ _ with lookup A' zero ≟ₙ lookup A zero
𝒜memEqPreVar {zero} {zero} {mₜ = mₜ} Skipₜ _ _              | yes lA'z=lAz = 
  cong (λ x → lookupOrDefault x (lookup mₜ zero)) (sym lA'z=lAz)
𝒜memEqPreVar {zero} {zero} {A' = A'} {mₜ = mₜ} Assignₜ _ wFmₜA' | no _ = 
  sym (lookupₜx∘changeₜx {n} {_} {lookup A' zero} zero mₜ (wFmₜA' zero))
𝒜memEqPreVar currVar@{suc _} {varName} {cV<n} {A} {A'} _ _ _ with toℕ varName ≟ₙ currVar | lookup A' (fromℕ< cV<n) ≟ₙ lookup A (fromℕ< cV<n)
𝒜memEqPreVar {suc currVar'} {varName} {cV<n} {A} {A'} {mₜ} {mₜ'} (Seqₜ Skipₜ d) _ _ | yes vN=cV | yes lA'cV=lAcV = 
  let lmₜvN=lmₜ'vN : lookup mₜ varName ≡ lookup mₜ' varName
      lmₜvN=lmₜ'vN = 𝒜memEqPostVar d (subst (λ x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      vN=cV : varName ≡ fromℕ< cV<n
      vN=cV = toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n)))
      lA'vN=lAvN : lookup A' varName ≡ lookup A varName
      lA'vN=lAvN = subst (λ x → lookup A' x ≡ lookup A x) (sym vN=cV) lA'cV=lAcV
   in cong₂ (λ x y → lookupOrDefault x y) (sym lA'vN=lAvN) lmₜvN=lmₜ'vN
𝒜memEqPreVar {suc currVar'} {varName} {cV<n} {A} {A'} {mₜ} {mₜ'} (Seqₜ {.mₜ} {mₜ1} {.mₜ'} Assignₜ d) _ wFmₜA' | yes vN=cV | no _ = 
  let finCurrVar = fromℕ< cV<n
      lmₜ1vN=lmₜ'vN : lookup mₜ1 varName ≡ lookup mₜ' varName
      lmₜ1vN=lmₜ'vN = 𝒜memEqPostVar d (subst (λ x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      lmₜ1A'cV=lmₜAcV : lookupₜ mₜ1 A' finCurrVar ≡ lookupₜ mₜ A finCurrVar
      lmₜ1A'cV=lmₜAcV = lookupₜx∘changeₜx {n} {_} {lookup A' finCurrVar} finCurrVar mₜ (wFmₜA' finCurrVar)
      cV=vN : fromℕ< cV<n ≡ varName
      cV=vN = sym (toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n))))
      lmₜAvN=lmₜ1A'vN : lookupₜ mₜ A varName ≡ lookupₜ mₜ1 A' varName
      lmₜAvN=lmₜ1A'vN = subst (λ x → lookupₜ mₜ A x ≡ lookupₜ mₜ1 A' x) cV=vN (sym lmₜ1A'cV=lmₜAcV)
   in subst (λ x → lookupₜ mₜ A varName ≡ lookupOrDefault (lookup A' varName) x) lmₜ1vN=lmₜ'vN lmₜAvN=lmₜ1A'vN
𝒜memEqPreVar {suc _} (Seqₜ Skipₜ d) vN≤cV wFmₜA' | no vN<>cV | yes _ = 
  𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV)) wFmₜA'
𝒜memEqPreVar currVar@{suc _} {varName} {cV<n} {A} {A'} {mₜ} {mₜ'} (Seqₜ {.mₜ} {mₜ1} {.mₜ'} assign@Assignₜ d) vN≤cV wFmₜA' | no vN<>cV | no _ =
  let vN<>fromN<cV : varName ≢  fromℕ< cV<n
      vN<>fromN<cV = (λ vN=fromN<cV → vN<>cV (subst (λ x → toℕ x ≡ currVar) (sym vN=fromN<cV) (toℕ-fromℕ< cV<n))) 
      lmₜ1AvN=lmₜAvN : lookupₜ mₜ1 A varName ≡ lookupₜ mₜ A varName
      lmₜ1AvN=lmₜAvN = lookupₜy∘changeₜx (fromℕ< cV<n) varName mₜ vN<>fromN<cV
      lmₜ1AvN=lmₜ'A'vN : lookupₜ mₜ1 A varName ≡ lookupₜ mₜ' A' varName
      lmₜ1AvN=lmₜ'A'vN = 𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV)) (wellFormed-trans {A = A'} wFmₜA' assign)
   in trans (sym lmₜ1AvN=lmₜAvN) lmₜ1AvN=lmₜ'A'vN

-- Memory equality after executing an active set assignment.
:=𝒜-memEq : {A A' : 𝒜} {mₜ mₜ' : Memoryₜ} 
  → ⟨ A' :=𝒜 A , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ A'
  → mₜ - A ==ₘₜ mₜ' - A'
:=𝒜-memEq d wFmₜA' varName with n ≟ₙ zero 
...                           | no n<>0 = let n' , n'+1=n = 0<n=>n'+1=n (n≢0⇒n>0 n<>0)
                                              n-1=n : pred n ≡ pred (suc n')
                                              n-1=n = (cong pred (sym n'+1=n))
                                              vN≤n-1 : toℕ varName ≤ₙ pred n
                                              vN≤n-1 = (toℕ≤pred[n] varName)
                                           in 𝒜memEqPreVar d (subst (λ x → toℕ varName ≤ₙ x) n-1=n vN≤n-1) wFmₜA'
:=𝒜-memEq {[]} {[]} Skipₜ _ _ | yes _ = refl
