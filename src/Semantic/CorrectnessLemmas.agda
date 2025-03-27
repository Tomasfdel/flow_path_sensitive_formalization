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
-- Semantic equality of expression and its transformed counterpart.
expEquality : {e : ASTExpS} {m : Memory} {mₜ : Memoryₜ} {v v' : ℕ} {active : 𝒜}
  → m ==ₘ mₜ - active
  → ⟦ e ⟧ₑ m ≡ v 
  → ⟦ transExp e active ⟧ₜ mₜ ≡ v' 
  → v ≡ v' 
expEquality {IntVal n} {m} {mₜ} {.(⟦ IntVal n ⟧ₑ m)} {.(⟦ transExp (IntVal n) a ⟧ₜ mₜ)} {a} _ refl refl = refl
expEquality {Var x} {m} {mₜ} {.(⟦ Var x ⟧ₑ m)} {.(⟦ transExp (Var x) a ⟧ₜ mₜ)} {a} m=mt refl refl = m=mt x
expEquality {Add e1 e2} {m} {mₜ} {.(⟦ Add e1 e2 ⟧ₑ m)} {.(⟦ transExp (Add e1 e2) a ⟧ₜ mₜ)} {a} m=mt refl refl = 
  let expEq1 = expEquality {e1} {m} {mₜ} {⟦ e1 ⟧ₑ m} {⟦ transExp e1 a ⟧ₜ mₜ} {a} m=mt refl refl
      expEq2 = expEquality {e2} {m} {mₜ} {⟦ e2 ⟧ₑ m} {⟦ transExp e2 a ⟧ₜ mₜ} {a} m=mt refl refl
   in cong₂ _+_ expEq1 expEq2

-- LEMMA 4 OF THE CORRECTNESS PROOF
-- Equality of lookups of a variable in two memories after the active set assignment
-- for that variable has been executed. 
𝒜memEqPostVar : {currVar : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {a a' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ 𝒜assignAux currVar cV<n a a' , mₜ ⟩⇓ₜ mₜ'
  → currVar <ₙ toℕ varName
  → lookup mₜ varName ≡ lookup mₜ' varName

𝒜memEqPostVar {zero} {varName} {z<n} {a} {a'} {_} {_} _ _ with lookup a (fromℕ< z<n) ≟ₙ lookup a' (fromℕ< z<n)
𝒜memEqPostVar {zero} {varName} {_} {a} {a'} {mₜ} {.mₜ} Skipₜ _        | yes _ = refl
𝒜memEqPostVar {zero} {varName} {z<n} {a} {a'} {mₜ} {mₜ'} Assignₜ z<vN | no _ =
  let -- toℕ (fromℕ< z<n) ≡ 0
      toNz=0 = toℕ-fromℕ< z<n
      -- toℕ (fromℕ< z<n) <ₙ toℕ varName
      toNz<toNvN = subst (\x → x <ₙ toℕ varName) (sym toNz=0) z<vN
      -- (fromℕ< z<n) < varName
      z<vN = toℕ-cancel-< toNz<toNvN
      -- vN ≢  (fromℕ< z<n)
      vN<>z = ≢-sym (<⇒≢  z<vN)
   in sym (lookupy∘changex (fromℕ< z<n) varName mₜ vN<>z)

𝒜memEqPostVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {_} {_} _ _ with lookup a (fromℕ< cV<n) ≟ₙ lookup a' (fromℕ< cV<n)
𝒜memEqPostVar currVar@{suc currVar'} {varName} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) cV<vN    | yes _ = 
  𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
𝒜memEqPostVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {mₜ} {mₜ'} (Seqₜ Assignₜ d) cV<vN | no _ = 
  let -- toℕ (fromℕ< cV<n) ≡ currVar
      toNcV=cV = toℕ-fromℕ< cV<n
      -- toℕ (fromℕ< cV<n) <ₙ toℕ varName
      toNcV<toNvN = subst (\x → x <ₙ toℕ varName) (sym toNcV=cV) cV<vN
      -- (fromℕ< cV<n) < varName
      fNcV<vN = toℕ-cancel-< toNcV<toNvN
      -- varName ≢  (fromℕ< cV<n)
      vN<>fNcV = ≢-sym (<⇒≢  fNcV<vN)
      -- lookup mₜ varName ≡ lookup mₜ1 varName
      lmtvN=lmt1vN = sym (lookupy∘changex (fromℕ< cV<n) varName mₜ vN<>fNcV)
      -- lookup mₜ1 varName ≡ lookup mₜ' varName
      lmt1vN=lmt'vN = 𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
   in trans lmtvN=lmt1vN lmt1vN=lmt'vN  

-- Equality of lookups of a variable in two memories before the active set assignment
-- for that variable has been executed. 
𝒜memEqPreVar : {currVar : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {a a' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ 𝒜assignAux currVar cV<n a a' , mₜ ⟩⇓ₜ mₜ'
  → toℕ varName ≤ₙ currVar
  → wellFormed mₜ a
  → lookupₜ mₜ a' varName ≡ lookupₜ mₜ' a varName
𝒜memEqPreVar {zero} {zero} {_} {a} {a'} {_} {_} _ _ _ with lookup a zero ≟ₙ lookup a' zero
𝒜memEqPreVar {zero} {zero} {_} {_} {_} {mₜ} {.mₜ} Skipₜ _ _   | yes laz=la'z = 
  cong (\x → lookupOrDefault x (lookup mₜ zero)) (sym laz=la'z)
𝒜memEqPreVar {zero} {zero} {_} {a} {a'} {mₜ} {_} Assignₜ _ wFmₜa | no _ = 
  sym (lookupₜx∘changeₜx {n} {_} {lookup a zero} zero mₜ (wFmₜa zero))
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {_} {_} _ _ _ with toℕ varName ≟ₙ currVar | lookup a (fromℕ< cV<n) ≟ₙ lookup a' (fromℕ< cV<n)
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {_} {_} (Seqₜ Skipₜ d) _ _                     | yes vN=cV | yes lacV=la'cV = 
  let lmtvN=lmt'vN = 𝒜memEqPostVar d (subst (\x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      -- varName ≡ fromℕ< cV<n
      vN=cV = toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n)))
      lavN=la'vN = subst (\x → lookup a x ≡ lookup a' x) (sym vN=cV) lacV=la'cV
   in cong₂ (\x y → lookupOrDefault x y) (sym lavN=la'vN) lmtvN=lmt'vN
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {mₜ} {mₜ'} (Seqₜ {.mₜ} {mₜ1} {.mₜ'} Assignₜ d) _ wFmₜa | yes vN=cV | no _ = 
  let finCurrVar = fromℕ< cV<n
      -- lookup mt1 varName = lookup mt' varName
      lmt1vN=lmt'vN = 𝒜memEqPostVar d (subst (\x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      -- lookupOrDefault (lookup a finCurrVar) (lookup mt1 finCurrVar) == lookupOrDefault (lookup a' finCurrVar) (lookup mt finCurrVar)
      lamt1cV=la'mtcV = lookupₜx∘changeₜx {n} {_} {lookup a finCurrVar} finCurrVar mₜ (wFmₜa finCurrVar)
      -- fromℕ< cV<n ≡ varName
      cV=vN = sym (toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n))))
      -- lookupOrDefault (lookup a varName) (lookup mt1 varName) == lookupOrDefault (lookup a' varName) (lookup mt varName)
      lamt1vN=la'mtvN = subst (\x → lookupₜ mₜ a' x ≡ lookupₜ mₜ1 a x) cV=vN (sym lamt1cV=la'mtcV)
   in subst (\x → lookupₜ mₜ a' varName ≡ lookupOrDefault (lookup a varName) x) lmt1vN=lmt'vN lamt1vN=la'mtvN
𝒜memEqPreVar currVar@{suc currVar'} {varName} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) vN≤cV wFmₜa                     | no vN<>cV | yes _ = 
  𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV)) wFmₜa
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {mₜ} {mₜ'} (Seqₜ assign@Assignₜ d) vN≤cV wFmₜa               | no vN<>cV | no _ =
  let -- varName <> fromℕ< cV<n
      vN<>fromN<cV = (\vN=fromN<cV → vN<>cV (subst (\x → toℕ x ≡ currVar) (sym vN=fromN<cV) (toℕ-fromℕ< cV<n))) 
      -- lookupₜ mₜ1 a' varName ≡ lookupₜ mₜ a' varName
      lmt1a'vN=lmta'vN = lookupₜy∘changeₜx (fromℕ< cV<n) varName mₜ vN<>fromN<cV
      -- lookupₜ mₜ1 a' varName ≡ lookupₜ mₜ' a varName
      lmt1a'vN=lmt'avN = 𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV)) (wellFormed-trans {_} {_} {_} {a} wFmₜa assign)
   in trans (sym lmt1a'vN=lmta'vN) lmt1a'vN=lmt'avN

-- Memory equality after executing an active set assignment.
:=𝒜-memEq : {a a' : 𝒜} {mₜ mₜ' : Memoryₜ} 
  → ⟨ a' :=𝒜 a , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ a'
  → mₜ - a ==ₘₜ mₜ' - a'
:=𝒜-memEq {a} {a'} {mₜ} {mₜ'} d wFmₜa varName with n ≟ₙ zero 
...                                        | no n<>0 = let n' , n=sn' = 0<n=>n=sn' (n≢0⇒n>0 n<>0)
                                                        in 𝒜memEqPreVar d (subst (\x → toℕ varName ≤ₙ x) (cong pred n=sn') (toℕ≤pred[n] varName)) wFmₜa
:=𝒜-memEq {[]} {[]} {mₜ} {.mₜ} Skipₜ _ varName | yes _ = refl
