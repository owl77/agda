
postulate

 object :  Set

property : Set1
property = ∀ (x : object) → Set

postulate

  encodes : object → property → Set
  concrete : property

data Bot : Set where

absurd : ∀ {A : Set} (P : A → Set) ( x : A) → ( Bot →  P x)
absurd P x ()

¬  : ∀ {X : Set} (P : X → Set) → (X → Set)
¬ p = λ (x : _) → (p x → Bot)


Abstract :  object → Set
Abstract  = λ (o : object) → (¬ concrete) o

postulate  
  con_enc : ∀(o : object) (F : property)→ encodes o F → (Abstract o)

open import Agda.Builtin.Sigma

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

open import Agda.Primitive

_×_ :   ∀ {a b} (A :  Set a )( B : Set b )  →  Set (a ⊔ b)
A × B = Σ A (λ y → B)

_⇔_ : ∀ {X : Set} (P : X → Set)(Q : X → Set) →  ( X → Set)
(P ⇔ Q) x  =   ( ∀ (p : P x ) →  Q x ) × (∀ (q : Q x ) →  P x)

_↔_ :  { a b : Level} (P : Set a )( Q : Set b)  → Set (a ⊔ b)
P ↔ Q = (P → Q) × (Q → P)

D2Eq : property → property →  Set
D2Eq F G = ∀ (x : object)→ ( F ⇔ G) x

D2aux : ∀ (F : property) → D2Eq F F
D2aux F x  = (λ (w : F x) →  w), (λ ( w : F x) →  w)

postulate
 abs : (property → Set) → object
 AObj1 : ∀ ( p : property → Set) →  Abstract  (abs p )
 AObj2 :  ∀ (p : property → Set) → ∀ ( G : property) →  ( (encodes (abs p) G ) ↔  p G )

PlatonicForm1 : property → object → Set1
PlatonicForm1 F o = ∀ ( G : property ) → (encodes o G ↔ D2Eq F G)

plato1aux1 : property → (property → Set)
plato1aux1 f = λ ( g : property) → D2Eq f g

plato1 : ∀ (f : property) → Σ object (λ o  →    PlatonicForm1 f o)
plato1 f =     abs (plato1aux1 f),  (AObj2 (plato1aux1 f))   

plato1a : ∀ (F : property) (o : object) → PlatonicForm1 F o →  Abstract o
plato1a F o f =  (con_enc o F) (snd (f F) (D2aux F)) 

ConEq : object → object →  Set1
ConEq x y =  ((concrete x) × (concrete y) )  × ( ∀ (f :  property) → (f x ↔ f y)    )

AbsEq : object → object →  Set1
AbsEq x y =  ((Abstract x) × (Abstract y) )  × ( ∀ (F :  property) → (encodes x F  ↔ encodes  y F)    )

plato_aux  :  ∀ (F : property) (a b : object) →  PlatonicForm1 F a → PlatonicForm1 F b → AbsEq a b
plato_aux F a b X Y = (plato1a F a X ,  plato1a F b Y)    ,  (λ x → (λ x₁ →   (snd (Y x)) (fst ( X x ) x₁) ) ,  (λ x₁ →   (snd (X x)) (fst ( Y x ) x₁) )              ) 

infixr 1 _⊎_

data _⊎_ { a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {a b : Level} { A : Set a} {B : Set b} {C : A ⊎ B → Set (a ⊔ b)} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y


ObjEq : object → object →  Set1
ObjEq x y = (ConEq x y) ⊎ (AbsEq x y)

Unique : (p : object → Set1) → Set1
Unique p = (∀ ( y z : object) → ((p y) × (p z) → ObjEq y z))

-- for every property F there is a unique (up to AbsEq) object which is the Platonic Form of F

platouniq :  ∀ ( F : property) → Unique (λ ( o : object) → PlatonicForm1 F o)
platouniq F y z W =  inj₂ (plato_aux F y z (fst W) (snd W))


Form :  ∀ (F : property) → object
Form F =   fst (plato1 F)


plato_new : ∀ (F G : property) → encodes (Form F) G → D2Eq F G
plato_new F G W = (fst ( snd( plato1 F)  G ) ) W


plato_new1 : ∀ (F G : property) → encodes (Form F) G → ∀ (x : object) → G x → F x
plato_new1 F G W x p = (snd ((plato_new F G W) x)) p


plato3 : ∀ (F : property) → encodes (Form F) F 
plato3 F =   (snd ((snd (plato1 F)) F)) (D2aux F)


-- y participates of the form x

Participates : ∀ (y x : object) → Set₁
Participates  y x = Σ property (λ F → (encodes x F) × (F y) )


plato4_aux :  ∀ (x : object) → Abstract x →  AbsEq x x
plato4_aux x A = (A , A) , λ F → (λ x₁ → x₁) , (λ x₁ → x₁)


plato4 :  ∀ (x y : object) (F : property) →  (F x × F y) -> Σ  object (λ o →  ((AbsEq o (Form F)) × ( Participates x o ×  Participates  y o )))
plato4 x y F W = (Form F) , (plato4_aux (Form F) (plato1a F ( Form F)  (snd (plato1 F) ))     , (F , ( (snd ((snd (plato1 F)) F)) (D2aux F)  , (fst W))) , (F , (  (snd ((snd (plato1 F)) F)) (D2aux F)   , snd W)))

Part_aux : ∀ (x : object)(F : property) → Participates x (Form F) → F x
Part_aux x F W =       plato_new1  F (fst W)  (fst (snd W)) x  (snd (snd W))   

plato5 : ∀  (x : object) (F : property) →  ( F x ↔  (Participates x (Form F)  ) )
plato5 x F = (λ x₁ → F , (  (snd ((snd (plato1 F)) F)) (D2aux  F)  , x₁)) ,  Part_aux x F


Form_abs : ∀ (F : property) →  Abstract (Form F)
Form_abs F =   plato1a F (Form F) (snd (plato1 F))

ABSTRACT : object
ABSTRACT = Form Abstract

Form_abs1 : ∀ (F : property)→ Participates (Form F) ABSTRACT
Form_abs1 F = Abstract , ((plato3 Abstract ) , Form_abs F)

Abs_Par : Participates ABSTRACT ABSTRACT
Abs_Par = Form_abs1 Abstract
