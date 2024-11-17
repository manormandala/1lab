<!--
```agda
{-# OPTIONS --no-require-unique-meta-solutions #-}
open import Cat.Prelude
open import Cat.Displayed.Base
open import Data.List
open import Data.Nat
```
-->

```agda
module Cat.Instances.GridSchema where

ghd2 : Nat → List Nat → Nat
ghd2 x [] = suc x
ghd2 x (_ ∷ xs) = x

ghd : List Nat → Nat
ghd [] = 0
ghd (x ∷ xs) = ghd2 x xs

gtl : List Nat → List Nat
gtl [] = []
gtl (x ∷ xs) = xs

gcons : Nat → List Nat → List Nat
gcons x (x₁ ∷ xs) = x ∷ x₁ ∷ xs
gcons zero [] = []
gcons (suc x) [] = x ∷ []
{-# INJECTIVE_FOR_INFERENCE gcons #-}

gcons→gtl : ∀ {x xs} → gtl (gcons x xs) ≡ xs
gcons→gtl {x} {x₁ ∷ xs} = refl
gcons→gtl {zero} {[]} = refl
gcons→gtl {suc x} {[]} = refl
{-# REWRITE gcons→gtl #-}

gcons→ghd : ∀ {x xs} → ghd (gcons x xs) ≡ x
gcons→ghd {x} {x₁ ∷ xs} = refl
gcons→ghd {zero} {[]} = refl
gcons→ghd {suc x} {[]} = refl
{-# REWRITE gcons→ghd #-}

gcons-suc-helper : Nat → List Nat → Nat
gcons-suc-helper x [] = x
gcons-suc-helper x (_ ∷ _) = suc x

gcons-suc : Nat → List Nat → List Nat
gcons-suc x xs = gcons-suc-helper x xs ∷ xs

gcons-suc-nontrivial : ∀ {x xs} → gcons (suc x) xs ≡ gcons-suc x xs
gcons-suc-nontrivial {x} {[]} = refl
gcons-suc-nontrivial {x} {_ ∷ _} = refl
{-# REWRITE gcons-suc-nontrivial #-}

gcons→ghd2 : ∀ {x xs} → ghd2 (gcons-suc-helper x xs) xs ≡ suc x
gcons→ghd2 {x} {[]} = refl
gcons→ghd2 {x} {_ ∷ _} = refl
{-# REWRITE gcons→ghd2 #-}

gcons-re : ∀ {ns} → gcons (ghd ns) (gtl ns) ≡ ns
gcons-re {[]} = refl
gcons-re {x ∷ []} = refl
gcons-re {x ∷ x₁ ∷ ns} = refl
{-# REWRITE gcons-re #-}

gcons2 : Nat → Nat → List Nat → List Nat
gcons2 x y ys = gcons x (gcons y ys)

gcons3 : Nat → Nat → Nat → List Nat → List Nat
gcons3 x y z zs = gcons x (gcons2 y z zs)

data _≤'_ (n : Nat) : Nat → Type where
  n≤'n : n ≤' n
  n≤'Sm : ∀ {m} → n ≤' m → n ≤' suc m

≤'-trans : ∀ {i j k : Nat} → i ≤' j → j ≤' k → i ≤' k
≤'-trans i≤j n≤'n = i≤j
≤'-trans i≤j (n≤'Sm j≤k) = n≤'Sm (≤'-trans i≤j j≤k)

data Connection' : Nat → Nat → Type where
  cnil' : Connection' 0 0
  csnoc' : ∀ {i j i'} → Connection' i j → i ≤' i' → Connection' i' (suc j)
    
c-id : ∀ {i} → Connection' i i
c-id {zero} = cnil'
c-id {suc i} = csnoc' c-id (n≤'Sm n≤'n)

measure-≤' : ∀ {i j j'} → j ≤' j' → Connection' i j' → Nat
measure-≤' {i = i} (n≤'n) c = i
measure-≤' (n≤'Sm j≤j') (csnoc' c x) = measure-≤' j≤j' c

take-≤' : ∀ {i j j'} (j≤j' : j ≤' j') (c : Connection' i j') → measure-≤' j≤j' c ≤' i
take-≤' n≤'n c = n≤'n
take-≤' (n≤'Sm j≤j') (csnoc' c i'≤i) = ≤'-trans (take-≤' j≤j' c) i'≤i

drop-≤' : ∀ {i j j'} (j≤j' : j ≤' j') (c : Connection' i j') → Connection' (measure-≤' j≤j' c) j
drop-≤' n≤'n c = c
drop-≤' (n≤'Sm j≤j') (csnoc' c i'≤i) = drop-≤' j≤j' c

_c-∘_ : ∀ {i j k} → Connection' j k → Connection' i j → Connection' i k
_c-∘_ {i} {j} {k} cnil' cnil' = cnil'
_c-∘_ {i} {j} {k} (csnoc' f x) g = csnoc' (f c-∘ drop-≤' x g) (take-≤' x g)  

mutual
  data GridSchema : List Nat → Type

  data Connection : ∀ {ns} (i : Nat) → GridSchema (gcons i (gtl ns)) → GridSchema ns → Type

  target : ∀ {ns} → GridSchema ns → GridSchema (gtl ns)

  cstrip : ∀ {ns i} {x : GridSchema (gcons i (gtl ns))} {y : GridSchema ns} → Connection i x y → Connection' i (ghd ns)

  gsdrop-width : ∀ {i i' ns} → i ≤' i' → GridSchema (gcons i' ns) → Nat
  gsdrop : ∀ {i i' ns} (i≤i' : i ≤' i') (x : GridSchema (gcons i' ns)) → GridSchema (gcons2 i (gsdrop-width i≤i' x) (gtl ns))
  unfurl : ∀ {i i' ns} (i≤i' : i ≤' i') (x : GridSchema (gcons i' ns)) → Connection' (gsdrop-width i≤i' x) (ghd ns)
  connection-preserves-target : ∀ {ns i} {x : GridSchema (gcons i (gtl ns))} {y : GridSchema ns} → Connection i x y → target x ≡ target y 
  
  data GridSchema where
    pt : GridSchema []
    nonpt : ∀ {n ns} → GridSchema (n ∷ ns) → GridSchema (gcons 0 (n ∷ ns))
    snoc : ∀ {n i ns} (xs : GridSchema (gcons2 n i (gtl ns))) (x : GridSchema ns) → Connection i (target xs) x → GridSchema (gcons (suc n) ns)

  data Connection where
    cnil : ∀ {ns} {x y : GridSchema (gcons 0 ns)} → x ≡ y → Connection 0 x y
    csnoc : ∀ {ns i j i'} (i≤i' : i ≤' i') {x : GridSchema (gcons i' ns)} {y : GridSchema (gcons2 j (gsdrop-width i≤i' x) (gtl ns))} {c : Connection (gsdrop-width i≤i' x) (target y) (target x)} → cstrip c ≡ unfurl i≤i' x → Connection i (gsdrop i≤i' x) y → Connection i' x (snoc y (target x) c)

  target pt = pt
  target (nonpt x) = x
  target (snoc xs x c) = x

  cstrip (cnil _) = cnil'
  cstrip (csnoc i≤i' _ c) = csnoc' (cstrip c) i≤i'

  gsdrop-width {ns = ns} n≤'n x = ghd ns
  -- gsdrop-width (n≤'Sm i≤i') (snoc xs x c) = gsdrop-width i≤i' xs
  gsdrop-width {ns = []} (n≤'Sm i≤i') (snoc xs x c) = gsdrop-width i≤i' xs
  gsdrop-width {ns = x₁ ∷ ns} (n≤'Sm i≤i') (snoc xs x c) = gsdrop-width i≤i' xs

  gsdrop n≤'n x = x
  gsdrop {ns = []} (n≤'Sm i≤i') (snoc xs x c) = gsdrop {ns = gcons _ []} i≤i' xs
  gsdrop {ns = x₁ ∷ ns} (n≤'Sm i≤i') (snoc xs x c) = gsdrop {ns = gcons _ ns} i≤i' xs

  unfurl n≤'n x = c-id
  unfurl {ns = []} (n≤'Sm i≤i') (snoc xs x c) = cstrip c c-∘ unfurl i≤i' xs
  unfurl {ns = x₁ ∷ ns} (n≤'Sm i≤i') (snoc xs x c) = cstrip c c-∘ unfurl i≤i' xs

  connection-preserves-target (cnil x) = ap target x
  connection-preserves-target (csnoc i≤i' x c) = refl

pt-unique : ∀ (x : GridSchema []) → x ≡ pt
pt-unique pt = refl

-- cnil≡ : ∀ {ns} {x y : GridSchema (gcons 0 ns)} → x ≡ y → Connection 0 x y
-- cnil≡ {x = x} p = subst (Connection 0 x) p cnil

line : (n : Nat) → GridSchema (gcons n [])
line zero = pt
line (suc n) = snoc (line n) pt (cnil {ns = []} (pt-unique (target (line n))))

diff : {n : Nat} (m : Nat) → n ≤' (m + n)
diff zero = n≤'n
diff (suc m) = n≤'Sm (diff m)

test : GridSchema (gcons2 2 2 [])
test = snoc (snoc (nonpt (line 3)) (line 3) (csnoc (diff 2) refl (csnoc (diff 0) refl (csnoc (diff 1) refl (cnil refl))))) (line 2) (csnoc (diff 1) refl (csnoc (diff 2) refl (cnil refl)))
```
