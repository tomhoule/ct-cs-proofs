open import Cubical.Foundations.Everything
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary using (¬_ ; isProp¬ ; Discrete)
open import Cubical.Data.Sigma

record Graph {ℓ ℓ′} : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  constructor graph
  field
    node : Type ℓ
    arrow : node → node → Type ℓ′

open Graph

isSmall : {ℓ′ : Level} → Graph {ℓ′ = ℓ′} → Type₀
isSmall g = isSet (node g)

endo : {ℓ : Level} {G : Graph {ℓ} {ℓ-suc ℓ}} → node G → Type (ℓ-suc ℓ)
endo {G = G} n = arrow G n n

-- A graph is discrete when it has no arrows.
isDiscrete : Graph → Type₀
isDiscrete g = ¬ (Σ[ ab ∈ node g × node g ]( arrow g (fst ab) (snd ab)))

isSimple : Graph → Type₀
isSimple g = ∀ (a b : node g) → isProp (arrow g a b)

-- The graph of sets and functions.
-- Example 1.3.3

SetGraph : Graph
SetGraph = graph Set (λ a b → (a → b))

EmptyGraph : Graph
EmptyGraph = graph ⊥ (λ a b → ⊥)

EmptyGraphisDiscrete : isDiscrete EmptyGraph
EmptyGraphisDiscrete = λ { ((elem1 , elem2) , ()) }

