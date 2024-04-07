module NonRepeatingCollection where

open import Data.List.Base

-- TODO: Dummy implementation until I finish liveness analysis. 
-- Then I should try to implement it with AVLs or something else.

NonRepeatingCollection : (A : Set) → Set _
NonRepeatingCollection A = List A

-- hasElem : {A : Set} → A → NonRepeatingCollection A → Bool
-- hasElem _ [] = false
-- hasElem elem (elem ∷ xs) = true
-- hasElem elem (_ ∷ xs) = hasElem elem xs

listToNRC : {A : Set} → List A → NonRepeatingCollection A
-- listToNRC = foldr (\elem nrc → if hasElem elem nrc then nrc else elem ∷ nrc) []
listToNRC x = x

NRCtoList : {A : Set} → NonRepeatingCollection A → List A
NRCtoList x = x

unionNRC : {A : Set} → NonRepeatingCollection A → NonRepeatingCollection A → NonRepeatingCollection A
unionNRC nrc1 nrc2 = listToNRC (NRCtoList nrc1 ++ NRCtoList nrc2)

differenceNRC : {A : Set} → NonRepeatingCollection A → NonRepeatingCollection A → NonRepeatingCollection A
differenceNRC nrc1 nrc2 = nrc1
