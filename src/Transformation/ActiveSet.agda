module Transformation.ActiveSet {n} where

open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin 
  hiding (_≟_ ; _+_)
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties
open import Data.Product 
open import Data.Vec.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}

-- Active Sets.
-- Using a vector to represent a Fin n → ℕ mapping.
𝒜 : Set _
𝒜 = Vec ℕ n

𝒜varCount : {m : ℕ} → Vec ℕ m → ℕ
𝒜varCount [] = 0
𝒜varCount (h1 ∷ t1) = suc h1 + 𝒜varCount t1

-- Active sets merge function from Figure 5 of the paper.
merge𝒜 : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
merge𝒜 [] [] = []
merge𝒜 (h1 ∷ t1) (h2 ∷ t2) =
   (if h1 == h2 then h1 else (suc (h1 ⊔ h2))) ∷ (merge𝒜 t1 t2)

activeSetVarAssignment : Fin n → 𝒜 → 𝒜 → ASTStm
activeSetVarAssignment hInd a a' with lookup a hInd ≟ lookup a' hInd 
...                             | yes _ = SKIP
...                             | no _  = ASSIGN (hInd , (lookup a hInd)) (VAR (hInd , (lookup a' hInd)))

assignActiveSetAux : (m : ℕ) → m <ₙ n → 𝒜 → 𝒜 → ASTStm
assignActiveSetAux zero z<n a a' = activeSetVarAssignment (fromℕ< z<n) a a'
assignActiveSetAux m@(suc m') m<n a a' = 
  let m'<n = <-pred (m<n⇒m<1+n m<n)
   in SEQ (activeSetVarAssignment (fromℕ< m<n) a a') 
          (assignActiveSetAux m' m'<n a a')

0<n=>n=sn' : {m : ℕ} → zero <ₙ m → Σ[ m' ∈ ℕ ] (m ≡ suc m')
0<n=>n=sn' (s≤s {zero} {n'} z≤n) = n' , refl

-- := definition for active sets from Figure 4 of the paper.
_:=𝒜_ : 𝒜 → 𝒜 → ASTStm
a :=𝒜 a' with n ≟ zero 
...    | no n<>0 = let n' , n=sn' = 0<n=>n=sn' (n≢0⇒n>0 n<>0)
                    in assignActiveSetAux n' (subst (\x → n' <ₙ x) (sym n=sn') (n<1+n n')) a a'
...    | yes _ = SKIP
