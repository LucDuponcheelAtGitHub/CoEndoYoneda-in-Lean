# Pointfree CoYoneda lemmas for endofunctors of functional categories, proved as a `Lean` theorem.

All comments are welcome at luc.duponcheel [at] gmail.com.

## `Lean`

All specifications, implementations, definitions and proofs are written using  `Lean`.

- specifications are encoded as `class`es,
- implementations are encoded as `instance`s,
- definitions are encoded as `def`s,
- proofs are encodes as `theorem`s.

My code is perhaps not the most idiomatic `Lean` code one can think of. It would be interesting
(and it is challenging) to convert it to more idiomatic `Lean` code.

The category theory `class`es are my own low-profile ones. It would be interesting to somehow use
the standard category theory `class`es.

The proofs of the `theorem`s are `calc` based equatiobal reasoning proofs. It would be
interesting to somehow use `simp` tactic based ones.

The last proofs cannot be simplified using functional extension because the argument used is not a
general one. It would be interesting to somehow use quotient extension.

`Lean` will be taken for granted and will not explicitly be mentioned any more.

## The relevance of the CoYoneda lemma for mathematics

The CoYoneda lemma is important in mathematics because it shows that an object in a category is
completely determined by the ways it morphs to other objects. This turns studying objects of
categories into studying sets of morphisms from those objects to other objects.

The CoYoneda lemma involves only three specifications

- category,
- functor,
- natural transformation,

and one category implementation

- the category of sets and functions.

The simplicity of the CoYoneda lemma does not imply in any way that the CoYoneda lemma is easy.

All functors involved are funtors to the category of sets and functions.

The CoYoneda lemma is pointful: it involves elements of sets.

In fact, as stated above, being pointful is the essence of the CoYoneda lemma, letting
mathematicians study objects through morphisms.

## The relevance of functional categories for programming

What are referred to as functional categories model, perhaps not surprisingly, functional
programming.

The objects of functional categories are types. 

The morphisms of functional categories are referred to as programs, more precisely as programs from
a type to a type.

Functions can, somehow, be used as effectfree programs. Functional categories may have programs,
most notably, programs that manipulate internal or external state, that are not such effectfree
functions.

Our CoYoneda lemma involves one more specific specification

- functional category,

one extra specification

- triple,

and one triple implementation

- the triple of global values (programs from the `Unit` type to another type).

The functors involved are endofunctors, and the natural transformations involved are endo natural
transformation,

Our CoYoneda lemma is pointfree: it only involves programs.

Just like, from a programming point of view, the pointful CoYoneda lemma is about the relationship
between natural transformations and values, our pointfree CoYoneda lemma is about the relationship
between natural transformations and global values (recall that global values are programs).

## `Category`, `Functor` and `NaturalTransformation`

To start with the following abbriviations are introduced

```
abbrev function t₀ t₁ := t₀ → t₁

abbrev unaryTypeConstructor := Type → Type

abbrev binaryTypeConstructor := Type → Type → Type
```

`function t₀ t₁` is used to distinguish it from `t₀ → t₁` that is used to declare or define the
members of the specification `class`es.

### `Category`

```
class Category
    (btc : binaryTypeConstructor)
  where
  -- declared
  ι {t : Type} :
    btc t t
  -- declared
  andThen {t₀ t₁ t₂ : Type} :
    btc t₀ t₁ → btc t₁ t₂ → btc t₀ t₂

export Category (ι andThen)

infixr:80 " ≫ " => andThen
```

The `Category` specification for a binary type constructor parameter `btc` declares members, `ι` and
`andThen`, and defines an `infixr` version, `≫`, of `andThen`.

#### `CategoryProperties`

```
class CategoryProperties
    (btc : binaryTypeConstructor)
    [Category btc]
  : Prop where

  category_left_identity
      {t₀ t₁ : Type}
      {btc_t₀_t₁ : btc t₀ t₁} :
    btc_t₀_t₁
      = ι ≫ btc_t₀_t₁

  category_right_identity
      {t₀ t₁ : Type}
      {btc_t₀_t₁ : btc t₀ t₁} :
    btc_t₀_t₁ ≫ ι
      = btc_t₀_t₁

  category_associativity
      {t₀ t₁ t₂ t₃ : Type}
      {btc_t₀_t₁ : btc t₀ t₁}
      {btc_t₁_t₂ : btc t₁ t₂}
      {btc_t₂_t₃ : btc t₂ t₃} :
    btc_t₀_t₁ ≫ (btc_t₁_t₂ ≫ btc_t₂_t₃)
      = (btc_t₀_t₁ ≫ btc_t₁_t₂) ≫ btc_t₂_t₃

export CategoryProperties (
  category_right_identity
  category_left_identity
  category_associativity
  )

attribute [simp]
  category_right_identity
  category_left_identity
  category_associativity
```

`CategoryProperties` defines properties `category_left_identity`, `category_right_identity` and
`category_associativity`.

#### `functionCategory`

```
instance functionCategory :
  Category function :=
    {
      ι {t : Type} :
        function t t :=
          id

      andThen {t₀ t₁ t₂ : Type} :
        function t₀ t₁ → function t₁ t₂ → function t₀ t₂ :=
          λ fun_t₀_t₁ fun_t₁_t₂ ↦ fun_t₁_t₂ ∘ fun_t₀_t₁
    }
```

`instance functionCategory` is an implementation of `class Category`.

Below are the `theorem`s proving the `CategoryProperties` properties.

```
@[simp] theorem functionCategory_left_identity
    {t₀ t₁ : Type}
    {fun_t₀_t₁ : function t₀ t₁} :

  ι ≫ fun_t₀_t₁
    = fun_t₀_t₁ := by
  simp[andThen, ι]

@[simp] theorem functionCategory_right_identity
    {t₀ t₁ : Type}
    {fun_t₀_t₁ : function t₀ t₁} :

  fun_t₀_t₁ ≫ ι
    = fun_t₀_t₁ := by
  simp[andThen, ι]

@[simp] theorem function_associativity
    {t₀ t₁ t₂ t₃ : Type}
    {fun_t₀_t₁ : function t₀ t₁}
    {fun_t₁_t₂ : function t₁ t₂}
    {fun_t₂_t₃ : function t₂ t₃} :

  (fun_t₂_t₃ ∘ fun_t₁_t₂) ∘ fun_t₀_t₁
    = fun_t₂_t₃ ∘ (fun_t₁_t₂ ∘ fun_t₀_t₁) := by
  rfl

@[simp] theorem functionCategory_associativity
    {t₀ t₁ t₂ t₃ : Type}
    {fun_t₀_t₁ : function t₀ t₁}
    {fun_t₁_t₂ : function t₁ t₂}
    {fun_t₂_t₃ : function t₂ t₃} :

  (fun_t₀_t₁ ≫ fun_t₁_t₂) ≫ fun_t₂_t₃
    = fun_t₀_t₁ ≫ (fun_t₁_t₂ ≫ fun_t₂_t₃) := by
  simp[andThen]
```

### `Functor`

```
class Functor
    (btc₀ : binaryTypeConstructor)
    (btc₁ : binaryTypeConstructor)
    (utc : unaryTypeConstructor)
  where
  -- declared
  φ {t₀ t₁ : Type} :
    function (btc₀ t₀ t₁) (btc₁ (utc t₀) (utc t₁))

export Functor (φ)
```

The `Functor` specification for a unary type constructor parameter `utc` declares member, `φ`.

#### `FunctorProperties`

```
class FunctorProperties
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    [Category btc₀]
    [Category btc₁]
    {utc : unaryTypeConstructor}
    (functor : Functor btc₀ btc₁ utc)
  : Prop where

  functor_identity
      {t : Type} :
    functor.φ ι
      = (ι : btc₁ (utc t) (utc t))

  functor_sequential_composition
      {t₀ t₁ t₂ : Type}
      {btc_t₀_t₁ : btc₀ t₀ t₁}
      {btc_t₁_t₂ : btc₀ t₁ t₂} :
    functor.φ btc_t₀_t₁ ≫ functor.φ btc_t₁_t₂
      = functor.φ (btc_t₀_t₁ ≫ btc_t₁_t₂)

export FunctorProperties (
  functor_identity
  functor_sequential_composition
)

attribute [simp]
  functor_identity
  functor_sequential_composition
```

`FunctorProperties` defines properties `functor_identity` and `functor_sequential_composition`.

#### `identityEndoFunctor` and `composedFunctor`

```
instance identityEndoFunctor
    {btc : binaryTypeConstructor}
    [Category btc] :
  Functor btc btc Id :=
    {
      φ {t₀ t₁ : Type} :
        function (btc t₀ t₁) (btc (Id t₀) (Id t₁)) :=
        id
    }

abbrev composedUnaryTypeConstructor
    (utc₀ : unaryTypeConstructor)
    (utc₁ : unaryTypeConstructor)
  : unaryTypeConstructor :=
    utc₁ ∘ utc₀

infixr:80 " ≻ " => composedUnaryTypeConstructor

instance composedFunctor
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    {btc₂ : binaryTypeConstructor}
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    (functor₀ : Functor btc₀ btc₁ utc₀)
    (functor₁ : Functor btc₁ btc₂ utc₁) :

  Functor btc₀ btc₂ (utc₀ ≻ utc₁) :=
    {
      φ {t₀ t₁ : Type} :
        function
          (btc₀ t₀ t₁)
          (btc₂ ((utc₀ ≻ utc₁) t₀) ((utc₀ ≻ utc₁) t₁)) :=
            functor₁.φ ∘ functor₀.φ
    }

infixr:80 " ⋙ " => composedFunctor
```

`instance identityEndoFunctor` and `instance composedFunctor` are implementations of
`class Functor`.

Below are the `theorem`s proving the `FunctorProperties` properties.

```
@[simp] theorem identityEndoFunctor_identity
    {btc : binaryTypeConstructor}
    [Category btc]
    {t : Type} :

  identityEndoFunctor.φ ι
    = (ι : btc (Id t) (Id t)) := by
  simp[identityEndoFunctor]

@[simp] theorem identityEndoFunctor_sequential_composition
    {btc : binaryTypeConstructor}
    [Category btc]
    {t₀ t₁ t₂ : Type}
    {btc_t₀_t₁ : btc t₀ t₁}
    {btc_t₁_t₂ : btc t₁ t₂} :

  identityEndoFunctor.φ (btc_t₀_t₁ ≫ btc_t₁_t₂)
    = identityEndoFunctor.φ btc_t₀_t₁ ≫
        identityEndoFunctor.φ btc_t₁_t₂ := by
  simp[φ]

@[simp] theorem composedFunctor_identity
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    {btc₂ : binaryTypeConstructor}
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    [Category btc₀]
    [Category btc₁]
    [Category btc₂]
    {functor₀ : Functor btc₀ btc₁ utc₀}
    {functor₁ : Functor btc₁ btc₂ utc₁}
    [FunctorProperties functor₀]
    [FunctorProperties functor₁]
    {t : Type} :

  (functor₀ ⋙ functor₁).φ ι =
    (ι : btc₂ ((utc₀ ≻ utc₁) t) ((utc₀ ≻ utc₁) t)) := by
  simp[composedFunctor]

@[simp] theorem composedFunctor_sequential_composition
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    {btc₂ : binaryTypeConstructor}
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    [Category btc₀]
    [Category btc₁]
    [Category btc₂]
    {functor₀ : Functor btc₀ btc₁ utc₀}
    {functor₁ : Functor btc₁ btc₂ utc₁}
    [FunctorProperties functor₀]
    [FunctorProperties functor₁]
    {t₀ t₁ t₂ : Type}
    {btc_t₀_t₁ : btc₀ t₀ t₁}
    {btc_t₁_t₂ : btc₀ t₁ t₂} :

  (functor₀ ⋙ functor₁).φ (btc_t₀_t₁ ≫ btc_t₁_t₂)
    = (functor₀ ⋙ functor₁).φ btc_t₀_t₁ ≫
        (functor₀ ⋙ functor₁).φ btc_t₁_t₂ := by
  simp[composedFunctor]
```

#### `coYonedaFunctorOf`

```
def coYonedaFunctorOf
    {btc : binaryTypeConstructor}
    [Category btc]
    (s : Type) :
  Functor btc function (btc s) :=
    {
      φ {t₀ t₁ : Type} :
        function
          (btc t₀ t₁)
          (function ((btc s) t₀) ((btc s) t₁)) :=
            λ btc_t₀_t₁ btc_s_t₀ ↦ btc_s_t₀ ≫ btc_t₀_t₁
    }
```

`def coYonedaFunctorOf` is an implementation of `class Functor`.

Below are the `theorem`s proving the `FunctorProperties` properties.

```
@[simp] theorem coYonedaFunctor_identity
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {s t₀ : Type} :

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
      coYonedaFunctor.φ

  cΥφ ι
    = (ι : function ((btc s) t₀) ((btc s) t₀)) :=

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
      coYonedaFunctor.φ

    calc

      cΥφ ι

    _   = λ btc_s_t₀ ↦ btc_s_t₀ ≫ ι
        := rfl

    _   = λ btc_s_t₀ ↦ btc_s_t₀
        := funext (λ _ ↦ category_right_identity)

    _   = (ι : function ((btc s) t₀) ((btc s) t₀))
        := rfl

@[simp] theorem coYonedaFunctor_sequential_composition
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {s t₀ t₁ t₂ : Type}
    {btc_t₀_t₁ : btc t₀ t₁}
    {btc_t₁_t₂ : btc t₁ t₂} :

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
      coYonedaFunctor.φ

  cΥφ (btc_t₀_t₁ ≫ btc_t₁_t₂)
    = cΥφ btc_t₀_t₁ ≫ cΥφ btc_t₁_t₂ :=

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
      coYonedaFunctor.φ

    calc

      cΥφ (btc_t₀_t₁ ≫ btc_t₁_t₂)

    _   = λ btc_s_t₀ ↦ btc_s_t₀ ≫ (btc_t₀_t₁ ≫ btc_t₁_t₂)
        := rfl

    _   = λ btc_s_t₀ ↦ (btc_s_t₀ ≫ btc_t₀_t₁) ≫ btc_t₁_t₂
        := funext (λ _ ↦ category_associativity)

    _   = cΥφ btc_t₀_t₁ ≫ cΥφ btc_t₁_t₂
        := rfl
```

### `NaturalTransformation`

```
class NaturalTransformation
    (btc₀ : binaryTypeConstructor)
    (btc₁ : binaryTypeConstructor)
    (utc₀ : unaryTypeConstructor)
    (utc₁ : unaryTypeConstructor)
  where
  -- decared
  τ {t : Type} : btc₁ (utc₀ t) (utc₁ t)
```

The `NaturalTransformation` specification declares member, `τ`.

#### `NaturalTransformationProperties`

```
class NaturalTransformationProperties
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    [Category btc₁]
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    (functor₀ : Functor btc₀ btc₁ utc₀)
    (functor₁ : Functor btc₀ btc₁ utc₁)
  : Prop where

  naturalTransformation_natural
      {t₀ t₁ : Type}
      {btc_t₀_t₁ : btc₀ t₀ t₁}
      {τ : {t : Type} → btc₁ (utc₀ t) (utc₁ t)} :
    functor₀.φ btc_t₀_t₁ ≫ τ
      = τ ≫ functor₁.φ btc_t₀_t₁

export NaturalTransformationProperties (
  naturalTransformation_natural
  )

attribute [simp]
  naturalTransformation_natural
```

`NaturalTransformationProperties` defines property `naturalTransformation_natural`.

#### `NaturalTransformationProperties` and `composedEndoNaturalTransformation`

```
abbrev EndoFunctor btc utc := Functor btc btc utc

abbrev EndoNaturalTransformation btc utc₀ utc₁ :=
  NaturalTransformation btc btc utc₀ utc₁

instance identityEndoNaturalTransformation
    {btc : binaryTypeConstructor}
    [Category btc]
    {utc : unaryTypeConstructor} :

  EndoNaturalTransformation btc utc utc :=
    {
      τ {t : Type} : btc (utc t) (utc t) :=
        ι
    }

instance composedEndoNaturalTransformation
    {btc : binaryTypeConstructor}
    [Category btc]
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    {utc₂ : unaryTypeConstructor}
    (endoNaturalTransformation₀ :
      EndoNaturalTransformation btc utc₀ utc₁)
    (endoNaturalTransformation₁ :
      EndoNaturalTransformation btc utc₁ utc₂) :

  EndoNaturalTransformation btc utc₀ utc₂ :=
    {
      τ {t : Type} : btc (utc₀ t) (utc₂ t) :=
        endoNaturalTransformation₀.τ ≫
          endoNaturalTransformation₁.τ
    }

 infixr:80 " ≻≻≻ " => composedEndoNaturalTransformation
```

`instance identityEndoNaturalTransformation` and `instance composedEndoNaturalTransformation` are
implementations of `class NaturalTransformation`.

Below are the `theorem`s proving the `NaturalTransformationProperties` properties.

```
@[simp] theorem identityEndoNaturalTransformation_natural
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    {functor : EndoFunctor btc utc}
    {t₀ t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  identityEndoNaturalTransformation.τ ≫
    functor.φ btc_t₀_t₁
    = functor.φ btc_t₀_t₁ ≫
        identityEndoNaturalTransformation.τ :=

  calc

    identityEndoNaturalTransformation.τ ≫
      functor.φ btc_t₀_t₁

  _   = ι ≫ functor.φ btc_t₀_t₁
        := congrArg
             (. ≫ functor.φ btc_t₀_t₁)
             rfl

  _   = functor.φ btc_t₀_t₁
        := Eq.symm category_left_identity

  _   = functor.φ btc_t₀_t₁ ≫ ι
        := Eq.symm category_right_identity

  _   = functor.φ btc_t₀_t₁ ≫
        identityEndoNaturalTransformation.τ
      := congrArg
           (functor.φ btc_t₀_t₁ ≫ .)
           rfl

@[simp] theorem composedEndoNaturalTransformation_natural
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    {utc₂ : unaryTypeConstructor}
    {functor₀ : EndoFunctor btc utc₀}
    {functor₁ : EndoFunctor btc utc₁}
    {functor₂ : EndoFunctor btc utc₂}
    {endoNaturalTransformation₀ :
      EndoNaturalTransformation btc utc₀ utc₁}
    {endoNaturalTransformation₁ :
      EndoNaturalTransformation btc utc₁ utc₂}
    [NaturalTransformationProperties functor₀ functor₁]
    [NaturalTransformationProperties functor₁ functor₂]
    {t₀ t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let composedEndoNaturalTransformation :=
    endoNaturalTransformation₀ ≻≻≻
      endoNaturalTransformation₁

  functor₀.φ btc_t₀_t₁ ≫
    composedEndoNaturalTransformation.τ
    = composedEndoNaturalTransformation.τ ≫
        functor₂.φ btc_t₀_t₁ :=

  let composedEndoNaturalTransformation :=
    endoNaturalTransformation₀ ≻≻≻
      endoNaturalTransformation₁

  calc
    functor₀.φ btc_t₀_t₁ ≫
      composedEndoNaturalTransformation.τ

  _   = functor₀.φ btc_t₀_t₁ ≫
          (endoNaturalTransformation₀.τ ≫
            endoNaturalTransformation₁.τ)
      := congrArg
           (functor₀.φ btc_t₀_t₁ ≫ .)
           rfl

  _   = (functor₀.φ btc_t₀_t₁ ≫
          endoNaturalTransformation₀.τ) ≫
            endoNaturalTransformation₁.τ
      := category_associativity

  _   = (endoNaturalTransformation₀.τ ≫
          functor₁.φ btc_t₀_t₁) ≫
            endoNaturalTransformation₁.τ
      := congrArg
           (. ≫ endoNaturalTransformation₁.τ)
           naturalTransformation_natural

  _   = endoNaturalTransformation₀.τ ≫
          (functor₁.φ btc_t₀_t₁ ≫
            endoNaturalTransformation₁.τ)
      := Eq.symm category_associativity

  _   = endoNaturalTransformation₀.τ ≫
          (endoNaturalTransformation₁.τ ≫
            functor₂.φ btc_t₀_t₁)
      := congrArg
           (endoNaturalTransformation₀.τ ≫ .)
           naturalTransformation_natural

  _   = (endoNaturalTransformation₀.τ ≫
          endoNaturalTransformation₁.τ) ≫
            functor₂.φ btc_t₀_t₁
      := category_associativity

  _   = composedEndoNaturalTransformation.τ ≫
        functor₂.φ btc_t₀_t₁
      := congrArg
           (. ≫ functor₂.φ btc_t₀_t₁)
           rfl
```

## `CoYoneda` lemmas

### `pointfulCoYonedaLemma1` and `coYonedaLemma1`

```
abbrev Transformation btc₀ btc₁ utc₀ utc₁ :=
  NaturalTransformation btc₀ btc₁ utc₀ utc₁

@[simp]theorem pointfulCoYonedaLemma1
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    {functionValuedFunctor : Functor btc function utc}
    {s : Type}
    {naturalTransformation :
      NaturalTransformation btc function (btc s) utc}
    [NaturalTransformationProperties
      (coYonedaFunctorOf s) functionValuedFunctor]
    {t : Type}
    {btc_s_t : (btc s) t} :

  let utc_s : utc s := naturalTransformation.τ ι

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ {t : Type} : (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let τ {t : Type} : (btc s) t → utc t :=
    naturalTransformation.τ

  let σ {t : Type}  : (btc s) t → utc t :=
    transformation.τ

  τ btc_s_t
    = σ btc_s_t :=

  let utc_s : utc s := naturalTransformation.τ ι

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ {t : Type} : (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let τ {t : Type} : (btc s) t → utc t :=
    naturalTransformation.τ

  let σ {t : Type}  : (btc s) t → utc t :=
    transformation.τ

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
      coYonedaFunctor.φ

  calc

    τ btc_s_t

  _   = τ (ι ≫ btc_s_t)
      := congrArg (τ .) category_left_identity

  _   = (cΥφ btc_s_t ≫ τ) ι
      := rfl

  _   = (τ ≫ φφ btc_s_t) ι
      :=
        congrArg
          ((. ι) : function (btc s s) (utc t) → utc t)
            naturalTransformation_natural

  _   = σ btc_s_t
      := rfl

theorem coYonedaLemma1
    {btc : binaryTypeConstructor}
    [Category btc]
    [Category btc]
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    {functionValuedFunctor : Functor btc function utc}
    {s : Type}
    {naturalTransformation :
      NaturalTransformation btc function (btc s) utc}
    [NaturalTransformationProperties
      (coYonedaFunctorOf s) functionValuedFunctor]
    {t : Type} :

  let utc_s : utc s := naturalTransformation.τ ι

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ {t : Type} : (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let τ : (btc s) t → utc t := naturalTransformation.τ

  let σ : (btc s) t → utc t := transformation.τ

  τ
    = σ :=

  let utc_s : utc s := naturalTransformation.τ ι

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ {t : Type} : (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let τ : (btc s) t → utc t := naturalTransformation.τ

  let σ : (btc s) t → utc t := transformation.τ

  calc

    τ
  _   = σ
      := funext λ _ ↦ pointfulCoYonedaLemma1
```

`pointfulCoYonedaLemma1`, and its companion `coYonedaLemma1`, prove that every
`naturalTransformation : NaturalTransformation btc function (btc s) utc` can be defined in terms of
`utc_s : utc s := naturalTransformation.τ ι`.

### `pointfulCoYonedaLemma2` and `coYonedaLemma2`

```
theorem pointfulCoYonedaLemma2
    {btc : binaryTypeConstructor}
    [Category btc]
    {category : Category btc}
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    {functionValuedFunctor : Functor btc function utc}
    [FunctorProperties functionValuedFunctor]
    {s : Type}
    {utc_s : utc s}
    {t₀ t₁ : Type}
    {btc_s_t₀ : (btc s) t₀}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
        coYonedaFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ {t : Type} : (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let σ {t : Type} : (btc s) t → utc t :=
    transformation.τ

  (σ ≫ φφ btc_t₀_t₁) btc_s_t₀
    = (cΥφ btc_t₀_t₁ ≫ σ) btc_s_t₀ :=

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
        coYonedaFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ {t : Type} : (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let σ {t : Type} : (btc s) t → utc t :=
    transformation.τ

  calc

    (σ ≫ φφ btc_t₀_t₁) btc_s_t₀

  _   = (φφ btc_s_t₀ ≫ φφ btc_t₀_t₁) utc_s
      := rfl

  _   = φφ (btc_s_t₀ ≫ btc_t₀_t₁) utc_s
      := congrArg
           ((. utc_s) :
             function (function (utc s) (utc t₁)) (utc t₁))
           functor_sequential_composition

  _   = (cΥφ btc_t₀_t₁ ≫ σ) btc_s_t₀
      := rfl

theorem coYonedaLemma2
    {btc : binaryTypeConstructor}
    [Category btc]
    {category : Category btc}
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    {functionValuedFunctor : Functor btc function utc}
    [FunctorProperties functionValuedFunctor]
    {s : Type}
    {utc_s : utc s}
    {t₀ t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
        coYonedaFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ : {t : Type} → (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let σ {t : Type} : (btc s) t → utc t :=
    transformation.τ

  σ ≫ φφ btc_t₀_t₁
    = cΥφ btc_t₀_t₁ ≫ σ
    :=

  let coYonedaFunctor : Functor btc function (btc s) :=
    coYonedaFunctorOf s

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
        coYonedaFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (btc t₀ t₁) (function (utc t₀) (utc t₁)) :=
      functionValuedFunctor.φ

  let transformation :
    Transformation btc function (btc s) utc :=
    {
      τ : {t : Type} → (btc s) t → utc t :=
        λ btc_s_t ↦
          φφ btc_s_t utc_s
    }

  let σ {t : Type} : (btc s) t → utc t :=
    transformation.τ

  calc

    σ ≫ φφ btc_t₀_t₁
  _   = cΥφ btc_t₀_t₁ ≫ σ
      := funext λ _ ↦ pointfulCoYonedaLemma2
```

`pointfulCoYonedaLemma2`, and its companion `coYonedaLemma2`, prove that every
`utc_s : utc s` can be used to define `transformation : Transformation btc function (btc s) utc`
that is a natural transformation.

### `Triple`

```
class Triple
    (btc : binaryTypeConstructor)
    (utc : unaryTypeConstructor)
  where
  -- declared
  tripleEndoFunctor :
    EndoFunctor btc utc
  -- declared
  neutralElementNaturalTransformation :
    EndoNaturalTransformation btc Id utc
  -- declared
  multiplicationNaturalTransformation :
    EndoNaturalTransformation btc (utc ≻ utc) utc

  -- defined
  τεφ {t₀ t₁ : Type} :
    btc t₀ t₁ → btc (utc t₀) (utc t₁) :=
     tripleEndoFunctor.φ
  -- defined
  ν {t : Type} :
    btc (Id t) (utc t) :=
     neutralElementNaturalTransformation.τ
  -- defined
  μ {t : Type} :
    btc ((utc ≻ utc) t) (utc t) :=
      multiplicationNaturalTransformation.τ
```

The `Triple` specification declares members, `tripleEndoFunctor`,
`neutralElementNaturalTransformation` and `multiplicationNaturalTransformation`, and, for
convenience, defines members `τεφ`, `ν` and `μ`.

#### `TripleProperties`

```
class TripleProperties
    {btc : binaryTypeConstructor}
    [Category btc]
    {utc : unaryTypeConstructor}
    (triple : Triple btc utc)
  : Prop where

  triple_left_identity
      {t : Type} :
    triple.ν ≫ triple.μ
      = (ι : btc (utc t) (utc t))

  triple_right_identity
      {t : Type} :
    triple.τεφ triple.ν ≫ triple.μ
      = (ι : btc (utc t) (utc t))

  triple_associativity
      {t : Type} :
    triple.τεφ triple.μ ≫ triple.μ
      = (triple.μ ≫ triple.μ :
          btc ((utc ≻ utc ≻ utc) t) (utc t))

export TripleProperties (
  triple_left_identity
  triple_right_identity
  triple_associativity
  )

attribute [simp]
  triple_left_identity
  triple_right_identity
  triple_associativity
```

`TripleProperties` defines properties `triple_left_identity`, `triple_right_identity` and
`triple_associativity`.

### `FunctionalCategory`

```
abbrev Global
  (btc : binaryTypeConstructor)
  (t : Type)
  := (btc Unit) t

class FunctionalCategory
    (btc : binaryTypeConstructor)
  extends Category btc
  where
  -- declared
  functionalFunctor : Functor function btc Id
  -- declared
  γμ {t : Type} :
    btc
      (((Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)
      ((Global btc ≻ Id) t)

export FunctionalCategory (functionalFunctor γμ)

def toGlobal
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    (t : Type) :
  function t ((Global btc) t) :=
    const Unit ≫ functionalFunctor.φ
```

The `FunctionalCategory` specification declares members, `tripleEndoFunctor` and `γμ`.

For convenience, also `toGlobal`, transforming values to morphisms, is defined. 

#### `coYonedaEndoFunctorOf`

```
def coYonedaEndoFunctorOf
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    (s : Type) :
  EndoFunctor btc (btc s ≻ Id) :=
    coYonedaFunctorOf s ⋙
      functionalFunctor
```

`def coYonedaEndoFunctorOf` is an implementation of `class Functor` because it is the composition of
two implementations of `class Functor`.

#### `globalTripleOf`

```
def globalTripleOf
    (btc : binaryTypeConstructor)
    [FunctionalCategory btc] :
  Triple btc (Global btc ≻ Id) :=
    {
        tripleEndoFunctor :
          EndoFunctor btc (Global btc ≻ Id) :=
            coYonedaEndoFunctorOf Unit
      ,
        neutralElementNaturalTransformation :
          EndoNaturalTransformation
              btc Id (Global btc ≻ Id) :=
          {
              τ {t : Type} :
                btc
                (Id t)
                ((Global btc ≻ Id) t) :=
                    functionalFunctor.φ (toGlobal t)
          }
      ,
        multiplicationNaturalTransformation :
          EndoNaturalTransformation
              btc
              ((Global btc ≻ Id) ≻ (Global btc ≻ Id))
              (Global btc ≻ Id) :=
            {
              τ {t : Type} :
                btc
                  (((Global btc ≻ Id) ≻
                    (Global btc ≻ Id)) t)
                  ((Global btc ≻ Id) t) :=
                  γμ
            }
    }
```

In what follows it is assumed that `def globalTripleOf` is an implementation of `class Triple`.

`tripleEndoFunctor` is an implementation of `class Functor` because `coYonedaEndoFunctorOf Unit` is
an implementations of `class Functor`. 

#### `FunctionalCategoryProperties`

```
class FunctionalCategoryProperties
    (btc : binaryTypeConstructor)
    [FunctionalCategory btc] : Prop
    extends CategoryProperties btc
  where

  νProperty
      {t : Type}
      {g_t_v : (Global btc) t} :

  let gₜ :
    function
      (Global btc t)
      ((Global btc) (Global btc t)) :=
        toGlobal (Global btc t)

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let γν {t : Type} :
    btc (Id t) ((Global btc ≻ Id) t) :=
       globalTriple.ν

  gₜ g_t_v
    = g_t_v ≫ γν

export FunctionalCategoryProperties (νProperty)

attribute [simp]
  νProperty
```

`FunctionalCategoryProperties` defines property `νProperty`.

#### `functionFunctionalCategory`

```
instance functionFunctionalCategory :
  FunctionalCategory function :=
    {
      functionalFunctor :
        Functor function function Id :=
        {
          φ {t₀ t₁ : Type} :
            function
              (function t₀ t₁)
              (function (Id t₀) (Id t₁)) :=
                id
        }

      γμ {t : Type} :
        function
          ((function Unit ≻ function Unit) t)
          ((function Unit) t) :=
            (. unit)
    }
```

`instance functionFunctionalCategory` is an implementation of `class FunctionalCategory`.

We leave the proof as an easy (somewhat tedious) exercise to the reader.

## `CoEndoYoneda` lemmas

### `pointfreeApplication`,  `pointfreeCoEndoYoneda` and `pointfreeGlobal`

```
@[simp] theorem pointfreeApplication
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctorProperties functionalCategory.functionalFunctor]
    {t₀ t₁ : Type}
    {fun_t₀_t₁ : function t₀ t₁}
    {val_t₀ : t₀} :

  let g₀ :
    function t₀ ((Global btc) t₀) :=
      toGlobal t₀

  let g₁ :
    function t₁ ((Global btc) t₁) :=
      toGlobal t₁

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalFunctor.φ

  g₀ val_t₀ ≫ φφ fun_t₀_t₁
    = g₁ (fun_t₀_t₁ val_t₀) :=

  let g₀ :
    function t₀ ((Global btc) t₀) :=
      toGlobal t₀

  let g₁ :
    function t₁ ((Global btc) t₁) :=
      toGlobal t₁

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  calc

    g₀ val_t₀ ≫ φφ fun_t₀_t₁

  _   = φφ (const Unit val_t₀) ≫ φφ fun_t₀_t₁
      := congrArg (. ≫ φφ fun_t₀_t₁) rfl

  _   = φφ (const Unit val_t₀ ≫ fun_t₀_t₁)
      := functor_sequential_composition

  _   = φφ (const Unit (fun_t₀_t₁ val_t₀))
      := congrArg (φφ .) rfl

  _   = g₁ (fun_t₀_t₁ val_t₀)
      := rfl
```

`pointfreeApplication` proves a pointfree version of function application.

In fact, it is more of a pointfree version of value binding, `>>=`, where
`val_t₀ >>= fun_t₀_t₁ = fun_t₀_t₁ val_t₀`.

```
@[simp] theorem pointfreeCoEndoYoneda
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctorProperties functionalCategory.functionalFunctor]
    (s : Type)
    {t₀ : Type}
    {btc_s_t₀ : (btc s) t₀}
    {t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let g₀ :
    function ((btc s) t₀) ((Global btc) ((btc s) t₀)) :=
      toGlobal ((btc s) t₀)

  let g₁ :
    function (btc s t₁) ((Global btc) (btc s t₁)) :=
      toGlobal (btc s t₁)

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctorOf s).φ

  g₁ (btc_s_t₀ ≫ btc_t₀_t₁)
    = g₀ btc_s_t₀ ≫ cΥεφ btc_t₀_t₁ :=

  let g₀ :
    function ((btc s) t₀) ((Global btc) ((btc s) t₀)) :=
      toGlobal ((btc s) t₀)

  let g₁ :
    function (btc s t₁) ((Global btc) (btc s t₁)) :=
      toGlobal (btc s t₁)

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let cΥφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((btc s) t₀) ((btc s) t₁)) :=
      (coYonedaFunctorOf s).φ

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctorOf s).φ

  calc

    g₁ (btc_s_t₀ ≫ btc_t₀_t₁)

  _   = g₀ btc_s_t₀ ≫ φφ (cΥφ btc_t₀_t₁)
      := Eq.symm pointfreeApplication

  _   = g₀ btc_s_t₀ ≫ cΥεφ btc_t₀_t₁
      := rfl
```

`pointfreeCoEndoYoneda` proves a pointfree version of the essence of the `coYonedaEndoFunctorOf`
definition.

```
@[simp] theorem pointfreeGlobal
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctorProperties functionalCategory.functionalFunctor]
    {t₀ : Type}
    {g_t₀ : (Global btc) t₀}
    {t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let g₀ :
    function
      ((Global btc) t₀)
      ((Global btc) ((Global btc) t₀)) :=
       toGlobal ((Global btc) t₀)

  let g₁ :
    function
      ((Global btc) t₁)
      ((Global btc) ((Global btc) t₁)) :=
        toGlobal ((Global btc) t₁)

  let γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((Global btc ≻ Id) t₀) ((Global btc ≻ Id) t₁)) :=
      (coYonedaEndoFunctorOf Unit).φ

  g₁ (g_t₀ ≫ btc_t₀_t₁)
    = g₀ g_t₀ ≫ γεφ btc_t₀_t₁ :=

  let g₀ :
    function
      ((Global btc) t₀)
      ((Global btc) ((Global btc) t₀)) :=
        toGlobal ((Global btc) t₀)

  let g₁ :
    function
      ((Global btc) t₁)
      ((Global btc) ((Global btc) t₁)) :=
        toGlobal ((Global btc) t₁)

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let cΥυφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (function ((Global btc) t₀) ((Global btc) t₁)) :=
      (coYonedaFunctorOf Unit).φ

  let γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((Global btc ≻ Id) t₀) ((Global btc ≻ Id) t₁)) :=
      (coYonedaEndoFunctorOf Unit).φ

  calc

    g₁ (g_t₀ ≫ btc_t₀_t₁)

  _   = g₀ g_t₀ ≫ φφ (cΥυφ btc_t₀_t₁)
      := Eq.symm pointfreeApplication

  _   = g₀ g_t₀ ≫ γεφ btc_t₀_t₁
      := rfl
```

`pointfreeGlobal` proves a specific version of the `pointfreeCoEndoYoneda`.

### `pointfreeCoEndoYonedaLemma1` and `pointfreeCoEndoYonedaLemma2`

```
abbrev EndoTransformation btc utc₀ utc₁ :=
  Transformation btc btc utc₀ utc₁

@[simp] theorem pointfreeCoEndoYonedaLemma1
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    {s : Type}
    {endoNaturalTransformation :
      EndoNaturalTransformation btc (btc s ≻ Id) utc}
    [NaturalTransformationProperties
      (coYonedaEndoFunctorOf s)
      (endoFunctor ⋙
        (globalTripleOf btc).tripleEndoFunctor)]
    {t : Type}
    {btc_s_t : (btc s) t} :

  let εφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc (utc t₀) (utc t₁)) :=
        endoFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let gₛₛ :
    function (btc s s) (Global btc (btc s s)) :=
      toGlobal (btc s s)

  let ι : btc s s := functionalCategory.ι

  let τ {t : Type} : btc ((btc s ≻ Id) t) (utc t) :=
    endoNaturalTransformation.τ

  let g_utc_s : (utc ≻ (Global btc ≻ Id)) s :=
    gₛₛ ι ≫ τ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_utc_s ≫ εφ .)
    }

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let γν {t : Type} :
    btc (Id t) ((Global btc ≻ Id) t) :=
      globalTriple.ν

  let gₛₜ :
    function ((btc s) t) (Global btc ((btc s) t)) :=
      toGlobal ((btc s) t)

  gₛₜ btc_s_t ≫ τ ≫ γν
    = gₛₜ btc_s_t ≫ σ :=

  let εφ {t u : Type} :
    function (btc t u) (btc (utc t) (utc u)) :=
      endoFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let gₛₛ :
    function (btc s s) (Global btc (btc s s)) :=
      toGlobal (btc s s)

  let ι : btc s s := functionalCategory.ι

  let τ {t : Type} : btc ((btc s ≻ Id) t) (utc t) :=
    endoNaturalTransformation.τ

  let g_utc_s : (utc ≻ (Global btc ≻ Id)) s :=
    gₛₛ ι ≫ τ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
        τ {t : Type} :
          btc
            ((btc s ≻ Id) t)
            ((utc ≻ (Global btc ≻ Id)) t) :=
              φφ (g_utc_s ≫ εφ .)
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
      endoTransformation.τ

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let coYonedaEndoFunctor (s : Type):
    EndoFunctor btc (btc s ≻ Id) :=
      coYonedaEndoFunctorOf s

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctor s).φ

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let γν {t : Type} :
    btc (Id t) ((Global btc ≻ Id) t) :=
      globalTriple.ν

  let composedEndoNaturalTransformation :
    EndoNaturalTransformation
      btc
      (btc s ≻ Id)
      (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            τ ≫ γν
    }

  let c_τ_ν {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
      composedEndoNaturalTransformation.τ

  let gₛ :
    function
      (Global btc (utc s))
      (Global btc (Global btc (utc s))) :=
      toGlobal (Global btc (utc s))

  let gₜ :
    function
      (Global btc (utc t))
      (Global btc (Global btc (utc t))) :=
      toGlobal (Global btc (utc t))

  let gₛₜ :
    function ((btc s) t) (Global btc ((btc s) t)) :=
      toGlobal ((btc s) t)

  calc

    gₛₜ btc_s_t ≫ τ ≫ γν

  _   = gₛₜ (ι ≫ btc_s_t) ≫ c_τ_ν
      := congrArg
            (gₛₜ . ≫ c_τ_ν)
            category_left_identity

  _   = (gₛₛ ι ≫ cΥεφ btc_s_t) ≫ c_τ_ν
      := congrArg
            (. ≫ c_τ_ν)
            (pointfreeCoEndoYoneda s)

  _   = gₛₛ ι ≫ (cΥεφ btc_s_t ≫ c_τ_ν)
      := Eq.symm category_associativity

  _   = gₛₛ ι ≫ (c_τ_ν ≫ c_εφ_γεφ btc_s_t)
      := congrArg
            (gₛₛ ι ≫ .)
            naturalTransformation_natural

  _   = (gₛₛ ι ≫ c_τ_ν) ≫ c_εφ_γεφ btc_s_t
      := category_associativity

  _   = ((gₛₛ ι ≫ τ) ≫ γν) ≫ c_εφ_γεφ btc_s_t
      := congrArg
            (. ≫ c_εφ_γεφ btc_s_t)
            category_associativity

  _   = (gₛₛ ι ≫ τ) ≫ γν ≫ c_εφ_γεφ btc_s_t
      := Eq.symm category_associativity

  _   = g_utc_s ≫ γν ≫ c_εφ_γεφ btc_s_t
      := congrArg
            (. ≫ γν ≫ c_εφ_γεφ btc_s_t)
            rfl

  _   = (g_utc_s ≫ γν) ≫ c_εφ_γεφ btc_s_t
      := category_associativity

  _   = gₛ g_utc_s ≫ c_εφ_γεφ btc_s_t
      := congrArg
            (. ≫ c_εφ_γεφ btc_s_t)
            (Eq.symm νProperty)

  _   = gₜ (g_utc_s ≫ εφ btc_s_t)
      := Eq.symm pointfreeGlobal

  _   = gₛₜ btc_s_t ≫ φφ (g_utc_s ≫ εφ .)
      := Eq.symm pointfreeApplication

  _   = gₛₜ btc_s_t ≫ σ
      := congrArg (gₛₜ btc_s_t ≫ .) rfl
```

`pointfreeCoEndoYonedaLemma1` proves that every
`endoNaturalTransformation : EndoNaturalTransformation btc (btc s ≻ Id) utc` can be defined
(up to composiyion with `γν`) in terms
of `g_utc_s : (utc ≻ (Global btc ≻ Id)) s := gₛₛ ι ≫ τ` where `gₛₛ := toGlobal (btc s s)`.

The equality itself is up to composition with global value `gₛₜ btc_s_t`

```
@[simp] theorem pointfreeCoEndoYonedaLemma2
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    [FunctorProperties endoFunctor]
    {s : Type}
    [FunctorProperties
       (globalTripleOf btc).tripleEndoFunctor]
    {g_utc_s : (utc ≻ (Global btc ≻ Id)) s}
    {t₀: Type}
    {btc_s_t₀ : (btc s) t₀}
    {t₁: Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let εφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc (utc t₀) (utc t₁)) :=
        endoFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let coYonedaEndoFunctor (s : Type):
    EndoFunctor btc (btc s ≻ Id) :=
      coYonedaEndoFunctorOf s

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctor s).φ

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_utc_s ≫ εφ .)
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let gₛₜ₀ :
    function ((btc s) t₀) (Global btc ((btc s) t₀)) :=
      toGlobal ((btc s) t₀)

  gₛₜ₀ btc_s_t₀ ≫ (σ ≫ c_εφ_γεφ btc_t₀_t₁)
    = gₛₜ₀ btc_s_t₀ ≫ (cΥεφ btc_t₀_t₁ ≫ σ) :=

  let εφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc (utc t₀) (utc t₁)) :=
        endoFunctor.φ

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let coYonedaEndoFunctor (s : Type):
    EndoFunctor btc (btc s ≻ Id) :=
      coYonedaEndoFunctorOf s

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctor s).φ

  let γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((Global btc ≻ Id) t₀)
        ((Global btc ≻ Id) t₁)) :=
      globalEndoFunctor.φ

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_utc_s ≫ εφ .)
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let gₛₜ₀ :
    function ((btc s) t₀) (Global btc ((btc s) t₀)) :=
      toGlobal ((btc s) t₀)

  let gₛₜ₁ :
    function ((btc s) t₁) (Global btc ((btc s) t₁)) :=
      toGlobal ((btc s) t₁)

  let gₛ :
    function
      (Global btc (utc s))
      (Global btc (Global btc (utc s))) :=
      toGlobal (Global btc (utc s))

  let gₜ₀ :
    function
      (Global btc (utc t₀))
      (Global btc (Global btc (utc t₀))) :=
      toGlobal (Global btc (utc t₀))

  let gₜ₁ :
    function
      (Global btc (utc t₁))
      (Global btc (Global btc (utc t₁))) :=
      toGlobal (Global btc (utc t₁))

  calc

    gₛₜ₀ btc_s_t₀ ≫ (σ ≫ c_εφ_γεφ btc_t₀_t₁)

  _   = gₛₜ₀ btc_s_t₀ ≫
          ((φφ (g_utc_s ≫ εφ .) ≫ c_εφ_γεφ btc_t₀_t₁))
      := congrArg
          (gₛₜ₀ btc_s_t₀ ≫ . ≫ c_εφ_γεφ btc_t₀_t₁)
          rfl

  _   = (gₛₜ₀ btc_s_t₀ ≫ (φφ (g_utc_s ≫ εφ .))) ≫
          c_εφ_γεφ btc_t₀_t₁
      := category_associativity

  _   = (gₜ₀ (g_utc_s ≫ εφ btc_s_t₀)) ≫ c_εφ_γεφ btc_t₀_t₁
      := congrArg
           (. ≫ c_εφ_γεφ btc_t₀_t₁)
           pointfreeApplication

  _   = (gₜ₀ (g_utc_s ≫ εφ btc_s_t₀)) ≫
          γεφ (εφ btc_t₀_t₁)
      := congrArg
           ((gₜ₀ (g_utc_s ≫ εφ btc_s_t₀)) ≫ .)
           rfl

  _   = (gₛ g_utc_s ≫ γεφ (εφ btc_s_t₀)) ≫
          γεφ (εφ btc_t₀_t₁)
      := congrArg
           (. ≫ γεφ (εφ btc_t₀_t₁))
           pointfreeGlobal

  _   = gₛ g_utc_s ≫
          ((γεφ (εφ btc_s_t₀)) ≫ γεφ (εφ btc_t₀_t₁))
      := Eq.symm category_associativity

  _   = gₛ g_utc_s ≫
          (γεφ (εφ btc_s_t₀ ≫ εφ btc_t₀_t₁))
      := congrArg
           (gₛ g_utc_s ≫ .)
           functor_sequential_composition

  _   = gₜ₁ (g_utc_s ≫ (εφ btc_s_t₀ ≫ εφ btc_t₀_t₁))
      := Eq.symm pointfreeGlobal

  _   = gₜ₁ (g_utc_s ≫ εφ (btc_s_t₀ ≫ btc_t₀_t₁))
      := congrArg
           (gₜ₁ ∘ (g_utc_s ≫ .))
           functor_sequential_composition

  _  = gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫ (φφ (g_utc_s ≫ εφ .))
      := Eq.symm pointfreeApplication

  _  = gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫ σ
      := congrArg
           (gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫ .)
           rfl

  _  = (gₛₜ₀ btc_s_t₀ ≫ cΥεφ btc_t₀_t₁) ≫ σ
      := congrArg
           (. ≫ σ)
           (pointfreeCoEndoYoneda s)

  _  = gₛₜ₀ btc_s_t₀ ≫ (cΥεφ btc_t₀_t₁ ≫ σ)
      := Eq.symm category_associativity
```

`pointfreeCoEndoYonedaLemma2` proves that every
`g_utc_s : (utc ≻ (Global btc ≻ Id)) s` can be used to define a transformation of type
`EndoTransformation btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id))` that is a natural transformation.

The `naturalTransformation_natural` equality itself is up to composition with global value
`gₛₜ₀ btc_s_t₀`


### `μTheorem`

```
@[simp] theorem μTheorem
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [TripleProperties (globalTripleOf btc)]
    (t : Type)
    {g_g_t_v : Global btc (Global btc t)} :

  let gₜ :
    function
      (Global btc (Global btc t))
      (Global btc (Global btc (Global btc t))) :=
    toGlobal
      (Global btc (Global btc t))

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let γμ {t : Type} :
    btc
      ((Global btc ≻ Id) ((Global btc ≻ Id) t))
      ((Global btc ≻ Id) t) :=
        globalTriple.μ

  gₜ g_g_t_v ≫ γμ
    = g_g_t_v :=

  let gₜ :
    function
      (Global btc (Global btc t))
      (Global btc (Global btc (Global btc t))) :=
    toGlobal
      (Global btc (Global btc t))

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let γν {t : Type} :
    btc (Id t) ((Global btc ≻ Id) t) :=
       globalTriple.ν

  let γμ {t : Type} :
    btc
      ((Global btc ≻ Id) ((Global btc ≻ Id) t))
      ((Global btc ≻ Id) t) :=
       globalTriple.μ

  calc

    gₜ g_g_t_v ≫ γμ

  _   = (g_g_t_v ≫ γν) ≫ γμ
      := congrArg (. ≫ γμ) νProperty

  _   = g_g_t_v ≫ (γν ≫ γμ)
      := Eq.symm category_associativity

  _   = g_g_t_v ≫ ι
      := congrArg (g_g_t_v ≫ .) triple_left_identity

  _   = g_g_t_v
      := category_right_identity
```

`μTheorem` is similar to (and proved using) `νProperty`.

### `pointfreeCoEndoYonedaLemma3` and `pointfreeCoEndoYonedaLemma4`

```
@[simp] theorem pointfreeCoEndoYonedaLemma3
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    [TripleProperties (globalTripleOf btc)]
    {s : Type}
    {endoNaturalTransformation :
      EndoNaturalTransformation
        btc
        (btc s ≻ Id)
        (utc ≻ (Global btc ≻ Id))}
    [NaturalTransformationProperties
      (coYonedaEndoFunctorOf s)
      (endoFunctor ⋙
        (globalTripleOf btc).tripleEndoFunctor)]
    {t : Type}
    {btc_s_t : (btc s) t} :

  let gₛₛ :
    function (btc s s) (Global btc (btc s s)) :=
      toGlobal (btc s s)

  let ι : btc s s := functionalCategory.ι

  let τ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
      endoNaturalTransformation.τ

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let g_g_utc_s :
    (utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) s :=
      gₛₛ ι ≫ τ

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let γμ {t : Type} :
    btc
    (((Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)
    ((Global btc ≻ Id) t) :=
      globalTriple.μ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let gₛₜ :
    function ((btc s) t) (Global btc ((btc s) t)) :=
      toGlobal ((btc s) t)

  gₛₜ btc_s_t ≫ τ
    = gₛₜ btc_s_t ≫ σ :=

  let gₛₛ :
    function (btc s s) (Global btc (btc s s)) :=
      toGlobal (btc s s)

  let ι : btc s s := functionalCategory.ι

  let τ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
      endoNaturalTransformation.τ

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let coYonedaEndoFunctor (s : Type):
    EndoFunctor btc (btc s ≻ Id) :=
      coYonedaEndoFunctorOf s

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctor s).φ

  let g_g_utc_s :
    (utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) s :=
      gₛₛ ι ≫ τ

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let γμ {t : Type} :
    btc
    (((Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)
    ((Global btc ≻ Id) t) :=
      globalTriple.μ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let gₛₜ :
    function ((btc s) t) ((btc s ≻ (Global btc ≻ Id)) t) :=
      toGlobal ((btc s) t)

  let gₜ :
    function
      ((utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)
      ((utc ≻ (Global btc ≻ Id) ≻
        (Global btc ≻ Id) ≻
        (Global btc ≻ Id)) t) :=
      toGlobal
        ((utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)

  calc

    gₛₜ btc_s_t ≫ τ

  _   = gₛₜ (ι ≫ btc_s_t) ≫ τ
      := congrArg (gₛₜ . ≫ τ) category_left_identity

  _   = (gₛₛ ι ≫ cΥεφ btc_s_t) ≫ τ
      := congrArg (. ≫ τ) (pointfreeCoEndoYoneda s)

  _   = gₛₛ ι ≫ (cΥεφ btc_s_t ≫ τ)
      := Eq.symm category_associativity

  _   = gₛₛ ι ≫ (τ ≫ c_εφ_γεφ btc_s_t)
      := congrArg (gₛₛ ι ≫ .) naturalTransformation_natural

  _   = (gₛₛ ι ≫ τ) ≫ c_εφ_γεφ btc_s_t
      := category_associativity

  _   = g_g_utc_s ≫ c_εφ_γεφ btc_s_t
      := congrArg (. ≫ c_εφ_γεφ btc_s_t) rfl

  _   = gₜ (g_g_utc_s ≫ c_εφ_γεφ btc_s_t) ≫ γμ
      := Eq.symm (μTheorem (utc t))

  _   = (gₛₜ btc_s_t ≫ φφ (g_g_utc_s ≫ c_εφ_γεφ .)) ≫ γμ
      := congrArg
           (. ≫ γμ)
           (Eq.symm pointfreeApplication)

  _   = gₛₜ btc_s_t ≫ (φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ)
      := Eq.symm category_associativity

  _   = gₛₜ btc_s_t ≫ σ
      := congrArg (gₛₜ btc_s_t ≫ .) rfl
```

`pointfreeCoEndoYonedaLemma3` proves that every
`endoNaturalTransformation : EndoNaturalTransformation btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id))`
can be defined in terms of 
`g_g_utc_s : (utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) s := gₛₛ ι ≫ τ` where 
gₛₛ := toGlobal (btc s s)`.

The equality itself is up to composition with global value `gₛₜ btc_s_t`

Using function extensionality to define a companion theorem `((. ≫ (τ ≫ γν)) = (. ≫ σ)` does not
work because the argument `gₛₜ btc_s_t` is not a general argument of type `btc Unit (btc s t)`.

```
@[simp] theorem pointfreeCoEndoYonedaLemma4
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties 
      functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    [FunctorProperties
      (endoFunctor ⋙ 
        (globalTripleOf btc).tripleEndoFunctor)]
    [TripleProperties (globalTripleOf btc)]
    {s : Type}
    {g_g_utc_s :
      (utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) s}
    {t₀: Type}
    {btc_s_t₀ : (btc s) t₀}
    {t₁: Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let coYonedaEndoFunctor (s : Type):
    EndoFunctor btc (btc s ≻ Id) :=
      coYonedaEndoFunctorOf s

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctor s).φ

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let γμ {t : Type} :
    btc
    (((Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)
    ((Global btc ≻ Id) t) :=
      globalTriple.μ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let gₛₜ₀ :
    function ((btc s) t₀) (Global btc ((btc s) t₀)) :=
      toGlobal ((btc s) t₀)

  gₛₜ₀ btc_s_t₀ ≫ (σ ≫ c_εφ_γεφ btc_t₀_t₁)
    = gₛₜ₀ btc_s_t₀ ≫ (cΥεφ btc_t₀_t₁ ≫ σ) :=

  let φφ {t₀ t₁ : Type} :
    function (function t₀ t₁) (btc t₀ t₁) :=
      functionalCategory.functionalFunctor.φ

  let coYonedaEndoFunctor (s : Type):
    EndoFunctor btc (btc s ≻ Id) :=
      coYonedaEndoFunctorOf s

  let cΥεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc ((btc s ≻ Id) t₀) ((btc s ≻ Id) t₁)) :=
      (coYonedaEndoFunctor s).φ

  let globalTriple : Triple btc (Global btc ≻ Id) :=
    globalTripleOf btc

  let globalEndoFunctor :
    EndoFunctor btc (Global btc ≻ Id) :=
      globalTriple.tripleEndoFunctor

  let c_εφ_γεφ {t₀ t₁ : Type} :
    function
      (btc t₀ t₁)
      (btc
        ((utc ≻ (Global btc ≻ Id)) t₀)
        ((utc ≻ (Global btc ≻ Id)) t₁)) :=
      (endoFunctor ⋙ globalEndoFunctor).φ

  let γμ {t : Type} :
    btc
    (((Global btc ≻ Id) ≻ (Global btc ≻ Id)) t)
    ((Global btc ≻ Id) t) :=
      globalTriple.μ

  let endoTransformation :
    EndoTransformation
      btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id)) :=
    {
      τ {t : Type} :
        btc
          ((btc s ≻ Id) t)
          ((utc ≻ (Global btc ≻ Id)) t) :=
            φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ
    }

  let σ {t : Type} :
    btc ((btc s ≻ Id) t) ((utc ≻ (Global btc ≻ Id)) t) :=
    endoTransformation.τ

  let gₛₜ₀ :
    function ((btc s) t₀) (Global btc ((btc s) t₀)) :=
      toGlobal ((btc s) t₀)

  let gₛₜ₁ :
    function ((btc s) t₁) (Global btc ((btc s) t₁)) :=
      toGlobal ((btc s) t₁)

  let gₜ₀:
    function
      ((utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) t₀)
      ((utc ≻ (Global btc ≻ Id) ≻
        (Global btc ≻ Id) ≻
        (Global btc ≻ Id)) t₀) :=
      toGlobal
        ((utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) t₀)

  let gₜ₁ :
    function
      ((utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) t₁)
      ((utc ≻ (Global btc ≻ Id) ≻
        (Global btc ≻ Id) ≻
        (Global btc ≻ Id)) t₁) :=
      toGlobal
        ((utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) t₁)

  calc

    gₛₜ₀ btc_s_t₀ ≫ (σ ≫ c_εφ_γεφ btc_t₀_t₁)

  _   = (gₛₜ₀ btc_s_t₀ ≫ σ) ≫ c_εφ_γεφ btc_t₀_t₁
      := category_associativity

  _   = (gₛₜ₀ btc_s_t₀ ≫
          (φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ)) ≫
            c_εφ_γεφ btc_t₀_t₁
      := congrArg (. ≫ c_εφ_γεφ btc_t₀_t₁) rfl

  _   = ((gₛₜ₀ btc_s_t₀ ≫ φφ (g_g_utc_s ≫ c_εφ_γεφ .)) ≫
          γμ) ≫ c_εφ_γεφ btc_t₀_t₁
      := congrArg
           (. ≫ c_εφ_γεφ btc_t₀_t₁)
           category_associativity

  _   = (gₛₜ₀ btc_s_t₀ ≫ φφ (g_g_utc_s ≫ c_εφ_γεφ .)) ≫
          (γμ ≫ c_εφ_γεφ btc_t₀_t₁)
      := Eq.symm category_associativity

  _   = gₜ₀ (g_g_utc_s ≫ c_εφ_γεφ btc_s_t₀) ≫
          (γμ ≫ c_εφ_γεφ btc_t₀_t₁)
      := congrArg
          (. ≫ (γμ ≫ c_εφ_γεφ btc_t₀_t₁))
          pointfreeApplication

  _   = (gₜ₀ (g_g_utc_s ≫ c_εφ_γεφ btc_s_t₀) ≫ γμ) ≫
          c_εφ_γεφ btc_t₀_t₁
      := category_associativity

  _   = (g_g_utc_s ≫ c_εφ_γεφ btc_s_t₀) ≫
            c_εφ_γεφ btc_t₀_t₁
      := congrArg
           (. ≫ c_εφ_γεφ btc_t₀_t₁)
           (μTheorem (utc t₀))

  _   = g_g_utc_s ≫
          (c_εφ_γεφ btc_s_t₀ ≫ c_εφ_γεφ btc_t₀_t₁)
      := Eq.symm category_associativity

  _   = g_g_utc_s ≫
          (c_εφ_γεφ (btc_s_t₀ ≫ btc_t₀_t₁))
      := congrArg
          (g_g_utc_s ≫ .)
          functor_sequential_composition

  _   = gₜ₁ (g_g_utc_s ≫
          c_εφ_γεφ (btc_s_t₀ ≫ btc_t₀_t₁)) ≫ γμ
      := Eq.symm (μTheorem (utc t₁))

  _   = (gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫
          φφ (g_g_utc_s ≫ c_εφ_γεφ .)) ≫ γμ
      := congrArg
           (. ≫ γμ)
           (Eq.symm pointfreeApplication)

  _   = gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫
          (φφ (g_g_utc_s ≫ c_εφ_γεφ .) ≫ γμ)
      := Eq.symm category_associativity

  _   = gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫ σ
      := congrArg
           (gₛₜ₁ (btc_s_t₀ ≫ btc_t₀_t₁) ≫ .)
           rfl

  _   = (gₛₜ₀ btc_s_t₀ ≫ cΥεφ btc_t₀_t₁) ≫ σ
      := congrArg
           (. ≫ σ)
           (pointfreeCoEndoYoneda s)

  _   = gₛₜ₀ btc_s_t₀ ≫ (cΥεφ btc_t₀_t₁ ≫ σ)
      := Eq.symm category_associativity
```

`pointfreeCoEndoYonedaLemma4` proves that every
`g_g_utc_s : (utc ≻ (Global btc ≻ Id) ≻ (Global btc ≻ Id)) s` can be used to define a transformation
of type `EndoNaturalTransformation btc (btc s ≻ Id) (utc ≻ (Global btc ≻ Id))` that is a natural
transformation.

The `naturalTransformation_natural` equality itself is up to composition with global value
`gₛₜ₀ btc_s_t₀`

Using function extensionality to define a companion theorem 
`(. ≫ (σ ≫ c_εφ_γεφ btc_t₀_t₁) = (. ≫ (cΥεφ btc_t₀_t₁ ≫ σ))` does not
work because the argument `gₛₜ btc_s_t` is not a general argument of type `btc Unit (btc s t)`.

## Remark

So what are the properties that are used?

- for `pointfreeCoEndoYonedaLemma1` and `pointfreeCoEndoYonedaLemma2`

  - `category_left_identity`
  - `category_associativity`
  - `functor_sequential_composition`
  - `naturalTransformation_natural`
  - `νProperty`

Note that `multiplicationNaturalTransformation` of `Triple` is not needed.  

- extra for `pointfreeCoEndoYonedaLemma3` and `pointfreeCoEndoYonedaLemma4`

  - `category_right_identity`
  - `triple_left_identity`
  



  















