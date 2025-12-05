namespace CoEndoYoneda01

open Function

open Unit

--
-- abbreviations
--

abbrev function t₀ t₁ := t₀ → t₁

abbrev unaryTypeConstructor := Type → Type

abbrev binaryTypeConstructor := Type → Type → Type

        --------------
        -- Category --
        --------------

-- class

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

-- properties

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

-- instances

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

-- theorems

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

        -------------
        -- Functor --
        -------------

-- class

class Functor
    (btc₀ : binaryTypeConstructor)
    (btc₁ : binaryTypeConstructor)
    (utc : unaryTypeConstructor)
  where
  -- declared
  φ {t₀ t₁ : Type} :
    function (btc₀ t₀ t₁) (btc₁ (utc t₀) (utc t₁))

export Functor (φ)

-- properties

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

-- instances

instance identityEndoFunctor
    {btc : binaryTypeConstructor}
    [Category btc] :
  Functor btc btc Id :=
    {
      φ {t₀ t₁ : Type} :
        function (btc t₀ t₁) (btc (Id t₀) (Id t₁)) :=
        id
    }

-- abbreviation

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

-- definitions

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

-- theorems

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

        ----------------------------
        -- Natural Transformation --
        ----------------------------

-- class

class NaturalTransformation
    (btc₀ : binaryTypeConstructor)
    (btc₁ : binaryTypeConstructor)
    (utc₀ : unaryTypeConstructor)
    (utc₁ : unaryTypeConstructor)
  where
  -- decared
  τ {t : Type} : btc₁ (utc₀ t) (utc₁ t)

export NaturalTransformation (τ)

-- properties

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

--
-- abbreviations
--

abbrev EndoFunctor btc utc := Functor btc btc utc

abbrev EndoNaturalTransformation btc utc₀ utc₁ :=
  NaturalTransformation btc btc utc₀ utc₁

-- instances

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

-- theorems

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

        ------------------------
        -- Transformation --
        ------------------------

--
-- abbreviatons
--

abbrev Transformation btc₀ btc₁ utc₀ utc₁ :=
  NaturalTransformation btc₀ btc₁ utc₀ utc₁

        --------------
        -- Theorems --
        --------------

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

        ------------
        -- Triple --
        -------------

-- class

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

-- properties

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

        ------------------------
        -- FunctionalCategory --
        ------------------------
--
-- abbreviations
--

abbrev Global
  (btc : binaryTypeConstructor)
  (t : Type)
  := (btc Unit) t

-- class

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

-- definitions

def toGlobal
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    (t : Type) :
  function t ((Global btc) t) :=
    const Unit ≫ functionalFunctor.φ

def coYonedaEndoFunctorOf
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    (s : Type) :
  EndoFunctor btc (btc s ≻ Id) :=
    coYonedaFunctorOf s ⋙
      functionalFunctor

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

-- properties

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

-- instances

instance functionFunctionalCategory :
  FunctionalCategory function :=
    {
      functionalFunctor :
        Functor function function Id :=
          identityEndoFunctor

      γμ {t : Type} :
        function
          ((function Unit ≻ function Unit) t)
          ((function Unit) t) :=
            (. unit)
    }

        --------------
        -- Theorems --
        --------------

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

--
-- abbreviations
--

abbrev EndoTransformation btc utc₀ utc₁ :=
  Transformation btc btc utc₀ utc₁

        --------------
        -- Theorems --
        --------------

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

end CoEndoYoneda01

