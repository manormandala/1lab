<!--
```agda
open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Instances.StrictCat

import Cat.Reasoning
import Cat.Strict as Strict
```
-->

```agda
module Cat.Instances.StrictWr where
```

<!--
```agda
open Precategory

private variable
  oc ℓc od ℓd : Level
  C : Precategory oc ℓc
  D : Precategory od ℓd

module _ (C : Precategory oc ℓc)
         (D : Precategory od ℓd)
         (d : D .Ob)
         (F : Functor (C ^op) D)
         where

  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Functor F
```
-->

# The strict wreath product

In its full generality, this is basically a comma category with some $\op$s applied, but it comes into its own when the functor is into strict categories at which point it can be iterated.

```agda
  record ≀-Obj : Type (oc ⊔ ℓd) where
    constructor _,_
    field
      obj : C.Ob
      tag : D.Hom (F.₀ obj) d

  open ≀-Obj public

  record ≀-Hom (a b : ≀-Obj) : Type (ℓc ⊔ ℓd) where
    constructor _,_
    no-eta-equality
    field
      map      : C.Hom (a .obj) (b .obj)
      commutes : a .tag D.∘ F.₁ map ≡ b .tag

  open ≀-Hom public
```
<!--
```agda
  ≀-Obj-path : ∀ {x y : ≀-Obj}
             → (p : x .obj ≡ y .obj)
             → PathP (λ i → D.Hom (F.₀ (p i)) d) (x .tag) (y .tag)
             → x ≡ y
  ≀-Obj-path p q i .obj = p i
  ≀-Obj-path p q i .tag = q i

  ≀-Hom-pathp : ∀ {a a' b b'} (p : a ≡ a') (q : b ≡ b')
                {x : ≀-Hom a b} {y : ≀-Hom a' b'}
              → PathP (λ i → C.Hom (p i .obj) (q i .obj)) (x .map) (y .map)
              → PathP (λ i → ≀-Hom (p i) (q i)) x y
  ≀-Hom-pathp p q {x} {y} r i .map = r i
  ≀-Hom-pathp p q {x} {y} r i .commutes =
    is-prop→pathp
      (λ i → D.Hom-set (F.F₀ (q i .obj)) d (p i .tag D.∘ F.₁ (r i)) (q i .tag))
      (x .commutes) (y .commutes) i

  ≀-Hom-path : ∀ {a b} {x y : ≀-Hom a b}
             → x .map ≡ y .map
             → x ≡ y
  ≀-Hom-path = ≀-Hom-pathp refl refl

  instance
    Extensional-≀-Hom
      : ∀ {a b ℓ} ⦃ sa : Extensional (C.Hom (a .obj) (b .obj)) ℓ ⦄
      → Extensional (≀-Hom a b) ℓ
    Extensional-≀-Hom ⦃ sa ⦄ = injection→extensional! ≀-Hom-path sa

  unquoteDecl H-Level-≀-Hom = declare-record-hlevel 2 H-Level-≀-Hom (quote ≀-Hom)
```
-->

```agda
  Strict-wreath : Precategory _ _
  Strict-wreath .Ob = ≀-Obj 
  Strict-wreath .Hom = ≀-Hom
  Strict-wreath .id .map = C.id
  Strict-wreath .id .commutes = D.elimr F.F-id
  Strict-wreath ._∘_ {X} {Y} {Z} f g = (f .map C.∘ g .map) , let open D in
    X .tag D.∘ F.₁ (f .map C.∘ g .map)       ≡⟨ refl⟩∘⟨ F.F-∘ (g .map) (f .map) ⟩
    X .tag D.∘ F.₁ (g .map) D.∘ F.₁ (f .map) ≡⟨ pulll (g .commutes) ⟩
    Y .tag D.∘ F.₁ (f .map)                  ≡⟨ f .commutes ⟩
    Z .tag                                   ∎ 
  Strict-wreath .idr f = ext (C.idr _)
  Strict-wreath .idl f = ext (C.idl _)
  Strict-wreath .assoc f g h = ext (C.assoc _ _ _)
  Strict-wreath .Hom-set _ _ = hlevel 2

  ≀-is-strict : Strict.is-strict C → Strict.is-strict Strict-wreath
  ≀-is-strict str x y p q i j .obj = str (x .obj) (y .obj) (ap ≀-Obj.obj p) (ap ≀-Obj.obj q) i j
  ≀-is-strict str x y p q i j .tag = is-set→squarep (λ i j → D.Hom-set (F.₀ (str (x .obj) (y .obj) (ap ≀-Obj.obj p) (ap ≀-Obj.obj q) i j)) d) (λ i → x .tag) (λ i → p i .tag) (λ i → q i .tag) (λ i → y .tag) i j

_≀[_]_ : (D C : Strict-cats od ℓd .Ob) (F : Functor (C .fst ^op) (Strict-cats od ℓd)) → Strict-cats _ _ .Ob
D ≀[ C ] F = (Strict-wreath (C .fst) _ D F) , ≀-is-strict (C .fst) (Strict-cats _ _) D F (C .snd)
```
