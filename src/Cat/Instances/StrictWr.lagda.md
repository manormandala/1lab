<!--
```agda
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Instances.StrictCat

import Cat.Reasoning
import Cat.Functor.Reasoning
import Cat.Strict as Strict
```
-->

```agda
module Cat.Instances.StrictWr where
```

<!--
```agda
open Displayed

private variable
  oc ℓc od ℓd : Level
  C : Precategory oc ℓc
  D : Precategory od ℓd

module _ (C : Precategory oc ℓc)
         (D : Precategory od ℓd)
         (d : ⌞ D ⌟)
         (F : Functor (C ^op) D)
         where

  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Cat.Functor.Reasoning F
```
-->

# The strict wreath product

In its full generality, this is basically a [[comma category]] with some $\op$s applied, but it comes into its own when the functor is into [[strict categories]] at which point it can be iterated.  In either case it is a discrete opfibration over C.

```agda
  Strict-wreath : Displayed C _ _
  Strict-wreath .Ob[_] c = D.Hom (F.₀ c) d
  Strict-wreath .Hom[_] f a b = a D.∘ F.₁ f ≡ b
  Strict-wreath .Hom[_]-set f a b = hlevel 2
  Strict-wreath .id' = D.elimr F.F-id
  Strict-wreath ._∘'_ p q = F.popl q ∙ p
  Strict-wreath .idr' _ = prop!
  Strict-wreath .idl' _ = prop!
  Strict-wreath .assoc' _ _ _ = prop!

  ≀-is-strict : Strict.is-strict C → Strict.is-strict (∫ Strict-wreath)
  ≀-is-strict str = Σ-is-hlevel 2 str (λ _ → hlevel 2)

_≀[_]_ : (D C : ⌞ Strict-cats od ℓd ⌟) (F : Functor (C .fst ^op) (Strict-cats od ℓd)) → ⌞ Strict-cats _ _ ⌟
D ≀[ C ] F = (∫ (Strict-wreath (C .fst) _ D F)) , ≀-is-strict (C .fst) (Strict-cats _ _) D F (C .snd)
```
