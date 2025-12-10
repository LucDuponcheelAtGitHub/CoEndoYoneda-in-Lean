namespace CoEndoYoneda03

set_option linter.unusedVariables false

open Function Unit

abbrev binaryTypeConstructor := Type → Type → Type

class Category (btc : binaryTypeConstructor) where

  ι {t : Type} : btc t t

  andThen {t₀ t₁ t₂ : Type} : btc t₀ t₁ → btc t₁ t₂ → btc t₀ t₂

export Category (ι andThen)

infixr:80 " ≫ " => andThen

class CategoryProperties (btc : binaryTypeConstructor) [Category btc] : Prop
  where

  category_left_identity {t₀ t₁ : Type} {btc_t₀_t₁ : btc t₀ t₁} :
    btc_t₀_t₁ = ι ≫ btc_t₀_t₁

  category_right_identity {t₀ t₁ : Type} {btc_t₀_t₁ : btc t₀ t₁} :
    btc_t₀_t₁ ≫ ι = btc_t₀_t₁

  category_associativity
      {t₀ t₁ t₂ t₃ : Type}
      {btc_t₀_t₁ : btc t₀ t₁} {btc_t₁_t₂ : btc t₁ t₂} {btc_t₂_t₃ : btc t₂ t₃} :
    btc_t₀_t₁ ≫ (btc_t₁_t₂ ≫ btc_t₂_t₃) = (btc_t₀_t₁ ≫ btc_t₁_t₂) ≫ btc_t₂_t₃

export CategoryProperties (
  category_right_identity
  category_left_identity
  category_associativity
  )

attribute [simp]
category_right_identity
  category_left_identity
  category_associativity

abbrev function t₀ t₁ := t₀ → t₁

instance : Category function where

  ι {t : Type} : function t t := id

  andThen {t₀ t₁ t₂ : Type} :
    function t₀ t₁ → function t₁ t₂ → function t₀ t₂ :=
      λ fun_t₀_t₁ fun_t₁_t₂ ↦ fun_t₁_t₂ ∘ fun_t₀_t₁

@[simp] theorem functionCategory_left_identity
    {t₀ t₁ : Type} {fun_t₀_t₁ : function t₀ t₁} :

  ι ≫ fun_t₀_t₁ = fun_t₀_t₁ := by simp[andThen, ι]

@[simp] theorem functionCategory_right_identity
    {t₀ t₁ : Type} {fun_t₀_t₁ : function t₀ t₁} :

  fun_t₀_t₁ ≫ ι = fun_t₀_t₁ := by simp[andThen, ι]

@[simp] theorem function_associativity
    {t₀ t₁ t₂ t₃ : Type}
    {fun_t₀_t₁ : function t₀ t₁}
    {fun_t₁_t₂ : function t₁ t₂}
    {fun_t₂_t₃ : function t₂ t₃} :

  (fun_t₂_t₃ ∘ fun_t₁_t₂) ∘ fun_t₀_t₁ = fun_t₂_t₃ ∘ (fun_t₁_t₂ ∘ fun_t₀_t₁) :=
  by rfl

@[simp] theorem functionCategory_associativity
    {t₀ t₁ t₂ t₃ : Type}
    {fun_t₀_t₁ : function t₀ t₁}
    {fun_t₁_t₂ : function t₁ t₂}
    {fun_t₂_t₃ : function t₂ t₃} :

  (fun_t₀_t₁ ≫ fun_t₁_t₂) ≫ fun_t₂_t₃ = fun_t₀_t₁ ≫ (fun_t₁_t₂ ≫ fun_t₂_t₃) :=
  by simp[andThen]

abbrev unaryTypeConstructor := Type → Type

class Functor
    (btc₀ : binaryTypeConstructor)
    (btc₁ : binaryTypeConstructor)
    (utc : unaryTypeConstructor) where
  φ {t₀ t₁ : Type} : function (btc₀ t₀ t₁) (btc₁ (utc t₀) (utc t₁))

export Functor (φ)

class FunctorProperties
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    [Category btc₀]
    [Category btc₁]
    {utc : unaryTypeConstructor}
    (functor : Functor btc₀ btc₁ utc) : Prop where

  functor_identity {t : Type} : (functor.φ ι : btc₁ (utc t) (utc t)) = ι

  functor_sequential_composition
      {t₀ t₁ t₂ : Type}
      {btc_t₀_t₁ : btc₀ t₀ t₁} {btc_t₁_t₂ : btc₀ t₁ t₂} :

    functor.φ btc_t₀_t₁ ≫ functor.φ btc_t₁_t₂ =
    functor.φ (btc_t₀_t₁ ≫ btc_t₁_t₂)

export FunctorProperties (functor_identity functor_sequential_composition)

attribute [simp] functor_identity functor_sequential_composition

instance identityEndoFunctor
    {btc : binaryTypeConstructor}
    [Category btc] :
  Functor btc btc Id where

    φ {t₀ t₁ : Type} : function (btc t₀ t₁) (btc (Id t₀) (Id t₁)) := id

@[simp] theorem identityEndoFunctor_identity
    {btc : binaryTypeConstructor}
    [Category btc]
    {t : Type} :

  (identityEndoFunctor.φ ι : btc (Id t) (Id t)) =
  ι := by simp[identityEndoFunctor]

@[simp] theorem identityEndoFunctor_sequential_composition
    {btc : binaryTypeConstructor}
    [Category btc]
    {t₀ t₁ t₂ : Type}
    {btc_t₀_t₁ : btc t₀ t₁}
    {btc_t₁_t₂ : btc t₁ t₂} :

  identityEndoFunctor.φ (btc_t₀_t₁ ≫ btc_t₁_t₂) =
  identityEndoFunctor.φ btc_t₀_t₁ ≫ identityEndoFunctor.φ btc_t₁_t₂ :=
    by simp[φ]

abbrev composedUnaryTypeConstructor
    (utc₀ : unaryTypeConstructor)
    (utc₁ : unaryTypeConstructor) : unaryTypeConstructor := utc₁ ∘ utc₀

infixr:80 " ≻ " => composedUnaryTypeConstructor

instance composedFunctor
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    {btc₂ : binaryTypeConstructor}
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    (functor₀ : Functor btc₀ btc₁ utc₀)
    (functor₁ : Functor btc₁ btc₂ utc₁) :
  Functor btc₀ btc₂ (utc₀ ≻ utc₁) where

    φ {t₀ t₁ : Type} :
      function (btc₀ t₀ t₁) (btc₂ ((utc₀ ≻ utc₁) t₀) ((utc₀ ≻ utc₁) t₁)) :=
        functor₁.φ ∘ functor₀.φ

infixr:80 " ⋙ " => composedFunctor

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

  ((functor₀ ⋙ functor₁).φ ι : btc₂ ((utc₀ ≻ utc₁) t) ((utc₀ ≻ utc₁) t)) = ι :=
  by simp[composedFunctor]

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

  (functor₀ ⋙ functor₁).φ (btc_t₀_t₁ ≫ btc_t₁_t₂) =
  (functor₀ ⋙ functor₁).φ btc_t₀_t₁ ≫ (functor₀ ⋙ functor₁).φ btc_t₁_t₂ := by
  simp[composedFunctor]

instance coYonedaFunctorOf
    {btc : binaryTypeConstructor}
    [Category btc]
    (s : Type) :
  Functor btc function (btc s) where

    φ {t₀ t₁ : Type} :
      function (btc t₀ t₁) (function ((btc s) t₀) ((btc s) t₁)) :=
        λ btc_t₀_t₁ btc_s_t₀ ↦ btc_s_t₀ ≫ btc_t₀_t₁

@[simp] theorem coYonedaFunctor_identity
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {s t₀ : Type} :

  ((coYonedaFunctorOf s).φ ι : function ((btc s) t₀) ((btc s) t₀)) = ι :=

    calc
      (coYonedaFunctorOf s).φ ι
    _   = ι
        := funext (λ btc_s_t₀ ↦ category_right_identity)

@[simp] theorem coYonedaFunctor_sequential_composition
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {s t₀ t₁ t₂ : Type}
    {btc_t₀_t₁ : btc t₀ t₁}
    {btc_t₁_t₂ : btc t₁ t₂} :

  (coYonedaFunctorOf s).φ (btc_t₀_t₁ ≫ btc_t₁_t₂) =
  (coYonedaFunctorOf s).φ btc_t₀_t₁ ≫ (coYonedaFunctorOf s).φ btc_t₁_t₂ :=

    calc
      (coYonedaFunctorOf s).φ (btc_t₀_t₁ ≫ btc_t₁_t₂)
    _   = (coYonedaFunctorOf s).φ btc_t₀_t₁ ≫ (coYonedaFunctorOf s).φ btc_t₁_t₂
        := funext (λ btc_s_t₀ ↦ category_associativity)

class NaturalTransformation
    (btc₀ : binaryTypeConstructor)
    (btc₁ : binaryTypeConstructor)
    (utc₀ : unaryTypeConstructor)
    (utc₁ : unaryTypeConstructor) where

   τ (t : Type) : btc₁ (utc₀ t) (utc₁ t)

export NaturalTransformation (τ)

class NaturalTransformationProperties
    {btc₀ : binaryTypeConstructor}
    {btc₁ : binaryTypeConstructor}
    [Category btc₁]
    {utc₀ : unaryTypeConstructor}
    {utc₁ : unaryTypeConstructor}
    (functor₀ : Functor btc₀ btc₁ utc₀)
    (functor₁ : Functor btc₀ btc₁ utc₁) : Prop where

  naturalTransformation_natural
      {t₀ t₁ : Type}
      {btc_t₀_t₁ : btc₀ t₀ t₁}
      {τ : (t : Type) → btc₁ (utc₀ t) (utc₁ t)} :
    functor₀.φ btc_t₀_t₁ ≫ τ t₁ = τ t₀ ≫ functor₁.φ btc_t₀_t₁

export NaturalTransformationProperties (naturalTransformation_natural)

attribute [simp] naturalTransformation_natural

abbrev Transformation btc₀ btc₁ utc₀ utc₁ :=
  NaturalTransformation btc₀ btc₁ utc₀ utc₁

def functorialValueToTransformation
    {btc : binaryTypeConstructor}
    [Category btc]
    {utc : unaryTypeConstructor}
    (functionValuedFunctor : Functor btc function utc)
    {s : Type}
    (utc_s : utc s) :=

  let transformation : Transformation btc function (btc s) utc :=
    {
      τ (t : Type) : (btc s) t → utc t := (functionValuedFunctor.φ . utc_s)
    }

  transformation

theorem pointfulCoYonedaLemma1
    {btc : binaryTypeConstructor}
    [Category btc]
    {category : Category btc}
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    (functionValuedFunctor : Functor btc function utc)
    [FunctorProperties functionValuedFunctor]
    {s : Type}
    (utc_s : utc s)
    {t₀ t₁ : Type}
    {btc_s_t₀ : (btc s) t₀}
    {btc_t₀_t₁ : btc t₀ t₁} :

  ((functorialValueToTransformation functionValuedFunctor utc_s).τ t₀ ≫
    functionValuedFunctor.φ btc_t₀_t₁)
      btc_s_t₀ =
  ((coYonedaFunctorOf s).φ btc_t₀_t₁ ≫
    (functorialValueToTransformation functionValuedFunctor utc_s).τ t₁)
      btc_s_t₀ :=

  calc
    ((functorialValueToTransformation functionValuedFunctor utc_s).τ t₀ ≫
      functionValuedFunctor.φ btc_t₀_t₁) btc_s_t₀
  _   = functionValuedFunctor.φ (btc_s_t₀ ≫ btc_t₀_t₁) utc_s
      := congrArg
           ((. utc_s) : function (function (utc s) (utc t₁)) (utc t₁))
           functor_sequential_composition
  _   = ((coYonedaFunctorOf s).φ btc_t₀_t₁ ≫
          (functorialValueToTransformation functionValuedFunctor utc_s).τ t₁)
            btc_s_t₀
      := rfl

theorem coYonedaLemma1
    {btc : binaryTypeConstructor}
    [Category btc]
    {category : Category btc}
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    {functionValuedFunctor : Functor btc function utc}
    [FunctorProperties functionValuedFunctor]
    {s : Type}
    (utc_s : utc s)
    {t₀ t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  (functorialValueToTransformation functionValuedFunctor utc_s).τ t₀ ≫
    functionValuedFunctor.φ btc_t₀_t₁ =
  (coYonedaFunctorOf s).φ btc_t₀_t₁ ≫
    (functorialValueToTransformation functionValuedFunctor utc_s).τ t₁ :=

  calc
    (functorialValueToTransformation functionValuedFunctor utc_s).τ t₀ ≫
      functionValuedFunctor.φ btc_t₀_t₁
  _   = (coYonedaFunctorOf s).φ btc_t₀_t₁ ≫
          (functorialValueToTransformation functionValuedFunctor utc_s).τ t₁
      := funext λ btc_s_t₀ ↦
           pointfulCoYonedaLemma1 functionValuedFunctor utc_s

@[simp]theorem pointfulCoYonedaLemma2
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    (functionValuedFunctor : Functor btc function utc)
    {s : Type}
    (naturalTransformation :NaturalTransformation btc function (btc s) utc)
    [NaturalTransformationProperties
      (coYonedaFunctorOf s) functionValuedFunctor]
    {t : Type}
    {btc_s_t : (btc s) t} :

  naturalTransformation.τ t btc_s_t =
  (functorialValueToTransformation
    functionValuedFunctor (naturalTransformation.τ s ι)).τ t btc_s_t :=

  calc
    naturalTransformation.τ t btc_s_t
  _   = naturalTransformation.τ t (ι ≫ btc_s_t)
      := congrArg
           (naturalTransformation.τ t .)
           category_left_identity
  _   = ((coYonedaFunctorOf s).φ btc_s_t ≫ naturalTransformation.τ t) ι
      := rfl
  _   = (functorialValueToTransformation
           functionValuedFunctor
             (naturalTransformation.τ s ι)).τ t btc_s_t
      := congrArg
           ((. ι) : function (btc s s) (utc t) → utc t)
           naturalTransformation_natural

@[simp]theorem coYonedaLemma2
    {btc : binaryTypeConstructor}
    [Category btc]
    [CategoryProperties btc]
    {utc : unaryTypeConstructor}
    (functionValuedFunctor : Functor btc function utc)
    {s : Type}
    (naturalTransformation :
      NaturalTransformation btc function (btc s) utc)
    [NaturalTransformationProperties
      (coYonedaFunctorOf s) functionValuedFunctor]
    {t : Type} :

  naturalTransformation.τ t =
  (functorialValueToTransformation
    functionValuedFunctor (naturalTransformation.τ s ι)).τ t :=

  calc
    naturalTransformation.τ t
  _   = (functorialValueToTransformation
         functionValuedFunctor (naturalTransformation.τ s ι)).τ t
      := funext λ btc_s_t ↦
           pointfulCoYonedaLemma2 functionValuedFunctor naturalTransformation

abbrev EndoFunctor btc utc := Functor btc btc utc

abbrev NaturalEndoTransformation btc utc₀ utc₁ :=
  NaturalTransformation btc btc utc₀ utc₁

class Triple (btc : binaryTypeConstructor) (utc : unaryTypeConstructor) where

  endoFunctor : EndoFunctor btc utc

  neutralElement : NaturalEndoTransformation btc Id utc

  multiplication : NaturalEndoTransformation btc (utc ≻ utc) utc

  εφ {t₀ t₁ : Type} : btc t₀ t₁ → btc (utc t₀) (utc t₁) := endoFunctor.φ

  η (t : Type) : btc (Id t) (utc t) := neutralElement.τ t

  μ (t : Type) : btc ((utc ≻ utc) t) (utc t) := multiplication.τ t

class TripleProperties
    {btc : binaryTypeConstructor}
    [Category btc]
    {utc : unaryTypeConstructor}
    (triple : Triple btc utc) : Prop where

  triple_left_identity {t : Type} : triple.η (utc t) ≫ triple.μ t = ι

  triple_right_identity {t : Type} : triple.εφ (triple.η t) ≫ triple.μ t = ι

  triple_associativity {t : Type} :
    triple.εφ (triple.μ t) ≫ triple.μ t = triple.μ (utc t) ≫ triple.μ t

export TripleProperties (
  triple_left_identity
  triple_right_identity
  triple_associativity
  )

attribute [simp]
  triple_left_identity
  triple_right_identity
  triple_associativity

abbrev Global (btc : binaryTypeConstructor) (t : Type) := (btc Unit ≻ Id) t

class FunctionalCategory (btc : binaryTypeConstructor) extends Category btc
  where

  functionalFunctor : Functor function btc Id

  γμ {t : Type} : btc ((Global btc ≻ Global btc) t) ((Global btc) t)

export FunctionalCategory (functionalFunctor γμ)

def toGlobal
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    (t : Type) :
  function t ((Global btc) t) := const Unit ≫ functionalFunctor.φ

instance coYonedaEndoFunctorOf
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    (s : Type) :
  EndoFunctor btc (btc s ≻ Id) := coYonedaFunctorOf s ⋙ functionalFunctor

instance globalEndoFunctor {btc : binaryTypeConstructor} [FunctionalCategory btc] :
  EndoFunctor btc (btc Unit ≻ Id) := coYonedaEndoFunctorOf Unit

instance globalTriple {btc : binaryTypeConstructor} [FunctionalCategory btc] :
  Triple btc (Global btc) where
    -- use globalEndoFunctor instead of endoFunctor.endoFunctor
    endoFunctor : EndoFunctor btc (Global btc) := globalEndoFunctor

    neutralElement : NaturalEndoTransformation btc Id (Global btc) :=
      {
        τ (t : Type) : btc (Id t) ((Global btc) t) :=
          functionalFunctor.φ (toGlobal t)
      }

    multiplication :
      NaturalEndoTransformation btc (Global btc ≻ Global btc) (Global btc) :=
      {
        τ (t : Type) : btc (((Global btc) ≻ (Global btc)) t) ((Global btc) t) :=
          γμ
      }

class FunctionalCategoryProperties
    (btc : binaryTypeConstructor)
    [FunctionalCategory btc] : Prop
    extends CategoryProperties btc where

  νProperty {t : Type} {g_t : (Global btc) t} :
    toGlobal ((Global btc) t) g_t = g_t ≫ globalTriple.η t

  -- no μProperty is defined because
  -- a μTheorem can be proved using νProperty

export FunctionalCategoryProperties (νProperty)

attribute [simp] νProperty

instance : FunctionalCategory function where
    functionalFunctor : Functor function function Id := identityEndoFunctor

    γμ {t : Type} :
      function ((function Unit ≻ function Unit) t) ((function Unit) t) :=
        (. unit)

def bind {t₀ t₁ : Type} : t₀ → (function t₀ t₁) → t₁ :=
  λ v_t₀ fun_t₀_t₁ => fun_t₀_t₁ v_t₀

infixl:80 " >>= " => bind

@[simp] theorem pointfreeBinding
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctorProperties functionalCategory.functionalFunctor]
    {t₀ t₁ : Type}
    {fun_t₀_t₁ : function t₀ t₁}
    {v_t₀ : t₀} :

  ((toGlobal t₀) v_t₀ ≫ functionalFunctor.φ fun_t₀_t₁ : (Global btc) t₁) =
  (toGlobal t₁) (v_t₀ >>= fun_t₀_t₁) :=

  calc
    ((toGlobal t₀) v_t₀ ≫ functionalFunctor.φ fun_t₀_t₁ : (Global btc) t₁)
  _   = (toGlobal t₁) (v_t₀ >>= fun_t₀_t₁)
      := functor_sequential_composition

-- just a special case of pointfreeBinding
@[simp] theorem pointfreeCoEndoYonedaProperty
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctorProperties functionalCategory.functionalFunctor]
    (s : Type)
    {t₀ : Type}
    {btc_s_t₀ : btc s t₀}
    {t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  toGlobal (btc s t₁) (btc_s_t₀ ≫ btc_t₀_t₁) =
  toGlobal (btc s t₀) btc_s_t₀ ≫ (coYonedaEndoFunctorOf s).φ btc_t₀_t₁ :=

  calc
    toGlobal ((btc s) t₁) (btc_s_t₀ ≫ btc_t₀_t₁)
  _   = toGlobal ((btc s) t₀) btc_s_t₀ ≫ (coYonedaEndoFunctorOf s).φ btc_t₀_t₁
      := Eq.symm pointfreeBinding

-- just a special case of pointfreeCoEndoYonedaProperty
@[simp] theorem pointfreeGlobal
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctorProperties functionalCategory.functionalFunctor]
    {t₀ : Type}
    {g_t₀ : (Global btc) t₀}
    {t₁ : Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  toGlobal ((Global btc) t₁) (g_t₀ ≫ btc_t₀_t₁) =
  toGlobal ((Global btc) t₀) g_t₀ ≫ globalEndoFunctor.φ btc_t₀_t₁ :=

  calc
    toGlobal ((Global btc) t₁) (g_t₀ ≫ btc_t₀_t₁)
  _   = toGlobal ((Global btc) t₀) g_t₀ ≫ globalEndoFunctor.φ btc_t₀_t₁
      := pointfreeCoEndoYonedaProperty Unit

abbrev EndoTransformation btc utc₀ utc₁ := Transformation btc btc utc₀ utc₁

instance globalFunctorialValueToEndoTransformation1
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    {utc : unaryTypeConstructor}
    (endoFunctor : EndoFunctor btc utc)
    {s : Type}
    (g_utc_s : (utc ≻ Global btc) s) :

  EndoTransformation btc (btc s ≻ Id) (utc ≻ Global btc) :=

    let endoTransformation :
      EndoTransformation btc (btc s ≻ Id) (utc ≻ Global btc) :=
      {
        τ (t : Type) : btc ((btc s ≻ Id) t) ((utc ≻ Global btc) t) :=
          functionalFunctor.φ (g_utc_s ≫ endoFunctor.φ .)
      }

    endoTransformation

@[simp] theorem pointfreeCoEndoYonedaLemma1
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    [FunctorProperties endoFunctor]
    {s : Type}
    [FunctorProperties (endoFunctor ⋙ globalEndoFunctor)]
    {g_utc_s : (utc ≻ Global btc) s}
    {t₀: Type}
    {btc_s_t₀ : (btc s) t₀}
    {t₁: Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  toGlobal ((btc s) t₀) btc_s_t₀ ≫
    ((globalFunctorialValueToEndoTransformation1 endoFunctor g_utc_s).τ t₀ ≫
      (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁) =
  toGlobal ((btc s) t₀) btc_s_t₀ ≫
    ((coYonedaEndoFunctorOf s).φ btc_t₀_t₁ ≫
      (globalFunctorialValueToEndoTransformation1 endoFunctor g_utc_s).τ t₁) :=

  calc
    toGlobal ((btc s) t₀) btc_s_t₀ ≫
      ((globalFunctorialValueToEndoTransformation1 endoFunctor g_utc_s).τ t₀ ≫
        (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
  _   = (toGlobal ((btc s) t₀) btc_s_t₀ ≫
          (functionalFunctor.φ (g_utc_s ≫ endoFunctor.φ .))) ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁
      := category_associativity
  _   = (toGlobal (Global btc (utc t₀)) (g_utc_s ≫ endoFunctor.φ btc_s_t₀)) ≫
          (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁
      := congrArg
           (. ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
           pointfreeBinding
  _   = (toGlobal (Global btc (utc s)) g_utc_s ≫
          globalEndoFunctor.φ (endoFunctor.φ btc_s_t₀)) ≫
            globalEndoFunctor.φ (endoFunctor.φ btc_t₀_t₁)
      := congrArg
           (. ≫ globalEndoFunctor.φ (endoFunctor.φ btc_t₀_t₁))
           pointfreeGlobal
  _   = toGlobal (Global btc (utc s)) g_utc_s ≫
          ((endoFunctor ⋙ globalEndoFunctor).φ btc_s_t₀ ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
      := Eq.symm category_associativity
  _   = toGlobal (Global btc (utc s)) g_utc_s ≫
          (endoFunctor ⋙ globalEndoFunctor).φ (btc_s_t₀ ≫ btc_t₀_t₁)
      := congrArg
           (toGlobal (Global btc (utc s)) g_utc_s ≫ .)
           functor_sequential_composition
  _   = toGlobal (Global btc (utc t₁))
          (g_utc_s ≫ (endoFunctor.φ (btc_s_t₀ ≫ btc_t₀_t₁)))
      := Eq.symm pointfreeGlobal
  _  = toGlobal ((btc s) t₁) (btc_s_t₀ ≫ btc_t₀_t₁) ≫
         (functionalFunctor.φ (g_utc_s ≫ endoFunctor.φ .))
      := Eq.symm pointfreeBinding
  _  = (toGlobal ((btc s) t₀) btc_s_t₀ ≫
         (coYonedaEndoFunctorOf s).φ btc_t₀_t₁) ≫
           (globalFunctorialValueToEndoTransformation1 endoFunctor g_utc_s).τ t₁
      := congrArg
           (. ≫
             (globalFunctorialValueToEndoTransformation1
               endoFunctor
               g_utc_s).τ t₁)
           (pointfreeCoEndoYonedaProperty s)
  _  = toGlobal ((btc s) t₀) btc_s_t₀ ≫
         ((coYonedaEndoFunctorOf s).φ btc_t₀_t₁ ≫
           (globalFunctorialValueToEndoTransformation1
             endoFunctor g_utc_s).τ t₁)
      := Eq.symm category_associativity

instance globalEndoTransformation
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    {utc : unaryTypeConstructor}
    {s : Type}
    (naturalEndoTransformation :
      NaturalEndoTransformation btc (btc s ≻ Id) utc) :

  EndoTransformation btc (btc s ≻ Id) (utc ≻ Global btc) where

    τ (t : Type) : btc ((btc s ≻ Id) t) ((utc ≻ Global btc) t) :=
      naturalEndoTransformation.τ t ≫ globalTriple.η (utc t)

@[simp] theorem pointfreeCoEndoYonedaLemma2
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    {s : Type}
    {naturalEndoTransformation : NaturalEndoTransformation btc (btc s ≻ Id) utc}
    [NaturalTransformationProperties
      (coYonedaEndoFunctorOf s) (endoFunctor ⋙ globalEndoFunctor)]
    {t : Type}
    {btc_s_t : (btc s) t} :

  toGlobal ((btc s) t) btc_s_t ≫
    (globalEndoTransformation naturalEndoTransformation).τ t =
  toGlobal ((btc s) t) btc_s_t ≫
    (globalFunctorialValueToEndoTransformation1
      endoFunctor (toGlobal (btc s s) ι ≫
        naturalEndoTransformation.τ s)).τ t :=

  calc
    toGlobal ((btc s) t) btc_s_t ≫
      (globalEndoTransformation naturalEndoTransformation).τ t
  _   = toGlobal ((btc s) t) (ι ≫ btc_s_t) ≫
          (naturalEndoTransformation.τ t ≫ globalTriple.η (utc t))
      := congrArg
           (toGlobal ((btc s) t) . ≫
              (globalEndoTransformation naturalEndoTransformation).τ t)
            category_left_identity
  _   = (toGlobal (btc s s) ι ≫ (coYonedaEndoFunctorOf s).φ btc_s_t) ≫
          (globalEndoTransformation naturalEndoTransformation).τ t
      := congrArg
           (. ≫ (naturalEndoTransformation.τ t ≫ globalTriple.η (utc t)))
           (pointfreeCoEndoYonedaProperty s)
  _   = toGlobal (btc s s) ι ≫
          ((coYonedaEndoFunctorOf s).φ btc_s_t ≫
            (globalEndoTransformation naturalEndoTransformation).τ t)
      := Eq.symm category_associativity
  _   = toGlobal (btc s s) ι ≫
          ((globalEndoTransformation naturalEndoTransformation).τ s ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t)
      := congrArg
            (toGlobal (btc s s) ι ≫ .)
            naturalTransformation_natural
  _   = (toGlobal (btc s s) ι ≫
          (globalEndoTransformation naturalEndoTransformation).τ s) ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t
      := category_associativity
  _   = ((toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s) ≫
          globalTriple.η (utc s)) ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t
      := congrArg
            (. ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t)
            category_associativity
  _   = (toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s) ≫
          globalTriple.η (utc s) ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t
      := Eq.symm category_associativity
  _   = ((toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s) ≫
          globalTriple.η (utc s)) ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t
      := category_associativity
  _   = toGlobal (Global btc (utc s))
          (toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s) ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t
      := congrArg
          (. ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t)
          (Eq.symm νProperty)
  _   = toGlobal (Global btc (utc t)) ((toGlobal (btc s s) ι ≫
          naturalEndoTransformation.τ s) ≫ endoFunctor.φ btc_s_t)
      := Eq.symm pointfreeGlobal
  _   = toGlobal ((btc s) t) btc_s_t ≫
          (globalFunctorialValueToEndoTransformation1
            endoFunctor
            (toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s)).τ t
      := Eq.symm pointfreeBinding

-- defined to keep the type system happy
def globalTripleOf
    (btc : binaryTypeConstructor) :
  [FunctionalCategory btc] → Triple btc (Global btc) := @globalTriple btc

@[simp] theorem μTheorem
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [TripleProperties (globalTripleOf btc)]
    (t : Type)
    {g_g_t : (Global btc ≻ Global btc) t} :

  toGlobal ((Global btc) ((Global btc) t)) g_g_t ≫ globalTriple.μ t = g_g_t :=

  calc
    toGlobal ((Global btc ≻ Global btc) t) g_g_t ≫ (globalTripleOf btc).μ t
  _   = (g_g_t ≫ (globalTripleOf btc).η ((Global btc) t)) ≫ (globalTripleOf btc).μ t
      := congrArg (. ≫ (globalTripleOf btc).μ t) νProperty
  _   = g_g_t ≫ ((globalTripleOf btc).η ((Global btc) t) ≫ (globalTripleOf btc).μ t)
      := Eq.symm category_associativity
  _   = g_g_t ≫ ι
      := congrArg (g_g_t ≫ .) triple_left_identity
  _   = g_g_t
      := category_right_identity

def globalFunctorialValueToEndoTransformation3
    {btc : binaryTypeConstructor}
    [FunctionalCategory btc]
    {utc : unaryTypeConstructor}
    (endoFunctor : Functor btc btc utc)
    {s : Type}
    (g_g_utc_s : (utc ≻ Global btc ≻ Global btc) s) :
  EndoTransformation btc (btc s ≻ Id) (utc ≻ Global btc) where
    τ (t : Type) : btc ((btc s ≻ Id) t) ((utc ≻ Global btc) t) :=
      functionalFunctor.φ
        (g_g_utc_s ≫ (endoFunctor ⋙ globalEndoFunctor).φ .) ≫
          globalTriple.μ (utc t)

@[simp] theorem pointfreeCoEndoYonedaLemma3
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    (endoFunctor : Functor btc btc utc)
    [FunctorProperties (endoFunctor ⋙ (globalTripleOf btc).endoFunctor)]
    [TripleProperties (globalTripleOf btc)]
    {s : Type}
    {g_g_utc_s : (utc ≻ Global btc ≻ Global btc) s}
    {t₀: Type}
    {btc_s_t₀ : (btc s) t₀}
    {t₁: Type}
    {btc_t₀_t₁ : btc t₀ t₁} :

  toGlobal ((btc s) t₀) btc_s_t₀ ≫
    ((globalFunctorialValueToEndoTransformation3 endoFunctor g_g_utc_s).τ t₀ ≫
      (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁) =
  toGlobal ((btc s) t₀) btc_s_t₀ ≫
    ((coYonedaEndoFunctorOf s).φ btc_t₀_t₁ ≫
      (globalFunctorialValueToEndoTransformation3
        endoFunctor g_g_utc_s).τ t₁) :=

  calc
    toGlobal ((btc s) t₀) btc_s_t₀ ≫
      ((globalFunctorialValueToEndoTransformation3
        endoFunctor g_g_utc_s).τ t₀ ≫
          (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
  _   = (toGlobal ((btc s) t₀) btc_s_t₀ ≫
          (globalFunctorialValueToEndoTransformation3
            endoFunctor g_g_utc_s).τ t₀) ≫
              (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁
      := category_associativity
  _   = ((toGlobal ((btc s) t₀) btc_s_t₀ ≫
          functionalFunctor.φ (g_g_utc_s ≫
            (endoFunctor ⋙ globalEndoFunctor).φ .)) ≫
              globalTriple.μ (utc t₀)) ≫
               (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁
      := congrArg
           (. ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
           category_associativity
  _   = (toGlobal ((btc s) t₀) btc_s_t₀ ≫
          functionalFunctor.φ (g_g_utc_s ≫
            (endoFunctor ⋙ globalEndoFunctor).φ .)) ≫
              (globalTriple.μ (utc t₀) ≫
                (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
      := Eq.symm category_associativity
  _   = toGlobal ((utc ≻ Global btc ≻ Global btc) t₀)
          (g_g_utc_s ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t₀) ≫
          (globalTriple.μ (utc t₀) ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
      := congrArg
          (. ≫ (globalTriple.μ (utc t₀) ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁))
          pointfreeBinding
  _   = (toGlobal ((utc ≻ Global btc ≻ Global btc) t₀)
          (g_g_utc_s ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t₀) ≫
            globalTriple.μ (utc t₀)) ≫
              (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁
      := category_associativity
  _   = (g_g_utc_s ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t₀) ≫
          (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁
      := congrArg
           (. ≫ (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
           (μTheorem (utc t₀))
  _   = g_g_utc_s ≫
        ((endoFunctor ⋙ globalEndoFunctor).φ btc_s_t₀ ≫
          (endoFunctor ⋙ globalEndoFunctor).φ btc_t₀_t₁)
      := Eq.symm category_associativity
  _   = g_g_utc_s ≫
          ((endoFunctor ⋙ globalEndoFunctor).φ (btc_s_t₀ ≫ btc_t₀_t₁))
      := congrArg
          (g_g_utc_s ≫ .)
          functor_sequential_composition
  _   = toGlobal ((utc ≻ Global btc ≻ Global btc) t₁)
          (g_g_utc_s ≫ (endoFunctor ⋙ globalEndoFunctor).φ
            (btc_s_t₀ ≫ btc_t₀_t₁)) ≫ globalTriple.μ (utc t₁)
      := Eq.symm (μTheorem (utc t₁))

  _   = (toGlobal ((btc s) t₁) (btc_s_t₀ ≫ btc_t₀_t₁) ≫
          functionalFunctor.φ (g_g_utc_s ≫ (endoFunctor ⋙
            globalEndoFunctor).φ .)) ≫ globalTriple.μ (utc t₁)
      := congrArg
           (. ≫ globalTriple.μ (utc t₁))
           (Eq.symm pointfreeBinding)
  _   = toGlobal ((btc s) t₁) (btc_s_t₀ ≫ btc_t₀_t₁) ≫
          (functionalFunctor.φ (g_g_utc_s ≫
            (endoFunctor ⋙ globalEndoFunctor).φ .) ≫ globalTriple.μ (utc t₁))
      := Eq.symm category_associativity
  _   = (toGlobal ((btc s) t₀) btc_s_t₀ ≫
          (coYonedaEndoFunctorOf s).φ btc_t₀_t₁) ≫
            (globalFunctorialValueToEndoTransformation3
              endoFunctor
              g_g_utc_s).τ t₁
      := congrArg
           (. ≫
             (globalFunctorialValueToEndoTransformation3
                endoFunctor
                g_g_utc_s).τ t₁)
           (pointfreeCoEndoYonedaProperty s)
  _   = toGlobal ((btc s) t₀) btc_s_t₀ ≫
          ((coYonedaEndoFunctorOf s).φ btc_t₀_t₁ ≫
            (globalFunctorialValueToEndoTransformation3
              endoFunctor
              g_g_utc_s).τ t₁)
      := Eq.symm category_associativity

@[simp] theorem pointfreeCoEndoYonedaLemma4
    {btc : binaryTypeConstructor}
    {functionalCategory : FunctionalCategory btc}
    [FunctionalCategoryProperties btc]
    [FunctorProperties functionalCategory.functionalFunctor]
    {utc : unaryTypeConstructor}
    {endoFunctor : Functor btc btc utc}
    [TripleProperties (globalTripleOf btc)]
    {s : Type}
    {naturalEndoTransformation :
      NaturalEndoTransformation
        btc (btc s ≻ Id) (utc ≻ Global btc)}
    [NaturalTransformationProperties
      (coYonedaEndoFunctorOf s)
      (endoFunctor ⋙
        (globalTripleOf btc).endoFunctor)]
    {t : Type}
    {btc_s_t : (btc s) t} :

  toGlobal ((btc s) t) btc_s_t ≫ naturalEndoTransformation.τ t =
  toGlobal ((btc s) t) btc_s_t ≫
    (globalFunctorialValueToEndoTransformation3
      endoFunctor (toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s)).τ t :=


  calc
    toGlobal ((btc s) t) btc_s_t ≫ naturalEndoTransformation.τ t
  _   = toGlobal ((btc s) t) (ι ≫ btc_s_t) ≫ naturalEndoTransformation.τ t
      := congrArg
           (toGlobal ((btc s) t) . ≫ naturalEndoTransformation.τ t)
           category_left_identity
  _   = (toGlobal (btc s s) ι ≫
          (coYonedaEndoFunctorOf s).φ btc_s_t) ≫
            naturalEndoTransformation.τ t
      := congrArg
           (. ≫ naturalEndoTransformation.τ t)
           (pointfreeCoEndoYonedaProperty s)
  _   = toGlobal (btc s s) ι ≫
          ((coYonedaEndoFunctorOf s).φ btc_s_t ≫ naturalEndoTransformation.τ t)
      := Eq.symm category_associativity
  _   = toGlobal (btc s s) ι ≫
          (naturalEndoTransformation.τ s ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t)
      := congrArg
           (toGlobal (btc s s) ι ≫ .)
           naturalTransformation_natural
  _   = (toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s) ≫
          (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t
      := category_associativity
  _   = toGlobal ((utc ≻ Global btc ≻ Global btc) t)
          ((toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s) ≫
            (endoFunctor ⋙ globalEndoFunctor).φ btc_s_t) ≫
              globalTriple.μ (utc t)
      := Eq.symm (μTheorem (utc t))
  _   = (toGlobal ((btc s) t) btc_s_t ≫
          functionalFunctor.φ ((toGlobal (btc s s) ι ≫
            naturalEndoTransformation.τ s) ≫
              (endoFunctor ⋙ globalEndoFunctor).φ .)) ≫
                globalTriple.μ (utc t)
      := congrArg
           (. ≫ globalTriple.μ (utc t))
           (Eq.symm pointfreeBinding)
  _   = toGlobal ((btc s) t) btc_s_t ≫
          (globalFunctorialValueToEndoTransformation3
            endoFunctor
            (toGlobal (btc s s) ι ≫ naturalEndoTransformation.τ s)).τ t
      := Eq.symm category_associativity

end CoEndoYoneda03

-- instance identityEndoNaturalTransformation
--     {btc : binaryTypeConstructor}
--     [Category btc]
--     {utc : unaryTypeConstructor} :

--   NaturalEndoTransformation btc utc utc where

--     τ (t : Type) := ι

-- @[simp] theorem identityEndoNaturalTransformation_natural
--     {btc : binaryTypeConstructor}
--     [Category btc]
--     [CategoryProperties btc]
--     {utc : unaryTypeConstructor}
--     {functor : EndoFunctor btc utc}
--     {t₀ t₁ : Type}
--     {btc_t₀_t₁ : btc t₀ t₁} :

--   identityEndoNaturalTransformation.τ t₀ ≫ functor.φ btc_t₀_t₁ =
--   functor.φ btc_t₀_t₁ ≫ identityEndoNaturalTransformation.τ t₁ :=

--   calc
--     identityEndoNaturalTransformation.τ t₀ ≫ functor.φ btc_t₀_t₁
--   _   = functor.φ btc_t₀_t₁
--       := Eq.symm category_left_identity
--   _   = functor.φ btc_t₀_t₁ ≫ identityEndoNaturalTransformation.τ t₁
--       := Eq.symm category_right_identity

-- instance composedEndoNaturalTransformation
--     {btc : binaryTypeConstructor}
--     [Category btc]
--     {utc₀ : unaryTypeConstructor}
--     {utc₁ : unaryTypeConstructor}
--     {utc₂ : unaryTypeConstructor}
--     (endoNaturalTransformation₀ : NaturalEndoTransformation btc utc₀ utc₁)
--     (endoNaturalTransformation₁ : NaturalEndoTransformation btc utc₁ utc₂) :
--   NaturalEndoTransformation btc utc₀ utc₂ where

--     τ (t : Type) :=
--       endoNaturalTransformation₀.τ t ≫ endoNaturalTransformation₁.τ t

--  infixr:80 " ≻≻≻ " => composedEndoNaturalTransformation

-- @[simp] theorem composedEndoNaturalTransformation_natural
--     {btc : binaryTypeConstructor}
--     [Category btc]
--     [CategoryProperties btc]
--     {utc₀ : unaryTypeConstructor}
--     {utc₁ : unaryTypeConstructor}
--     {utc₂ : unaryTypeConstructor}
--     {functor₀ : EndoFunctor btc utc₀}
--     {functor₁ : EndoFunctor btc utc₁}
--     {functor₂ : EndoFunctor btc utc₂}
--     {endoNaturalTransformation₀ : NaturalEndoTransformation btc utc₀ utc₁}
--     {endoNaturalTransformation₁ : NaturalEndoTransformation btc utc₁ utc₂}
--     [NaturalTransformationProperties functor₀ functor₁]
--     [NaturalTransformationProperties functor₁ functor₂]
--     {t₀ t₁ : Type}
--     {btc_t₀_t₁ : btc t₀ t₁} :

--   functor₀.φ btc_t₀_t₁ ≫
--     (endoNaturalTransformation₀ ≻≻≻ endoNaturalTransformation₁).τ t₁ =
--   (endoNaturalTransformation₀ ≻≻≻ endoNaturalTransformation₁).τ t₀ ≫
--     functor₂.φ btc_t₀_t₁ :=

--   calc
--     functor₀.φ btc_t₀_t₁ ≫
--       (endoNaturalTransformation₀ ≻≻≻ endoNaturalTransformation₁).τ t₁
--   _   = (functor₀.φ btc_t₀_t₁ ≫
--           endoNaturalTransformation₀.τ t₁) ≫ endoNaturalTransformation₁.τ t₁
--       := category_associativity
--   _   = (endoNaturalTransformation₀.τ t₀ ≫ functor₁.φ btc_t₀_t₁) ≫
--           endoNaturalTransformation₁.τ t₁
--       := congrArg
--            (. ≫ endoNaturalTransformation₁.τ t₁)
--            naturalTransformation_natural
--   _   = endoNaturalTransformation₀.τ t₀ ≫
--           (functor₁.φ btc_t₀_t₁ ≫ endoNaturalTransformation₁.τ t₁)
--       := Eq.symm category_associativity
--   _   = endoNaturalTransformation₀.τ t₀ ≫
--           (endoNaturalTransformation₁.τ t₀ ≫ functor₂.φ btc_t₀_t₁)
--       := congrArg
--            (endoNaturalTransformation₀.τ t₀ ≫ .)
--            naturalTransformation_natural
--   _   = (endoNaturalTransformation₀ ≻≻≻ endoNaturalTransformation₁).τ t₀ ≫
--         functor₂.φ btc_t₀_t₁
--       := category_associativity

-- instance : FunctionalCategory function where
--     functionalFunctor : Functor function function Id := identityEndoFunctor

--     γμ {t : Type} :
--       function ((function Unit ≻ function Unit) t) ((function Unit) t) :=
--         (. unit)
