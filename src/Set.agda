open import Cubical.Foundations.Everything
open import Cubical.Relation.Nullary using (¬_ ; isProp¬ ; Discrete)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

-- Hom sets
hom : {ℓ ℓ′ : Level} → Type ℓ → Type ℓ′ → Type (ℓ-max ℓ ℓ′)
hom A B = A → B

-- Hom functions
-- Notation: Hom(S, f)
homFun : {T V : Set } (S : Set) (f : T → V) → hom S T → hom S V
homFun S f g = f ∘ g

-- Hom functions in the other direction.
-- Notation: Hom(h, T)
homFun' : {W S : Set} (h : W → S) (T : Set) → hom S T → hom W T
homFun' h T g = g ∘ h

isInjective : {S : Set} {T : Set} (f : S → T) → Type₀
isInjective {S} {T} f = ∀ (a b : S) → ¬ (a ≡ b) → ¬ (f a ≡ f b)

isPropIsInjective : {S T : Set} {f : S → T} → isProp (isInjective f)
isPropIsInjective {f = f} = isPropΠ λ a → isPropΠ λ b → isPropΠ λ ¬a≡b → isProp¬ (f a ≡ f b)

isSurjective : {S T : Set} (f : S → T) → Type₀
isSurjective {S} {T} f = ∀ (t : T) → Σ[ s ∈ S ]( f s ≡ t )

isSurjective→rightCancel : {S T V : Set} (f : S → T) (g h : T → V) →
  isSurjective f →
  g ∘ f ≡ h ∘ f →
  g ≡ h
isSurjective→rightCancel {T = T} f g h fSurjective g∘f≡h∘f = funExt gx≡hx
  where

  gx≡hx : (x : T) → g x ≡ h x
  gx≡hx x = let (( s , fs≡x )) = fSurjective x in
    g x        ≡[ i ]⟨ g ((sym fs≡x) i) ⟩
    g (f s)    ≡⟨ refl ⟩
    (g ∘ f) s  ≡[ i ]⟨ g∘f≡h∘f i s ⟩
    (h ∘ f) s  ≡⟨ refl ⟩
    h (f s)    ≡[ i ]⟨ h (fs≡x i) ⟩
    h x ∎

homFun'Inj→ : {W S T : Set} (h : W → S) →
  isSurjective h → isInjective (homFun' h T)
homFun'Inj→ {W} {S} {T = T} h hSurjective S→T₁ S→T₂ ¬a≡b fS→T₁≡fS→T₂ = ¬a≡b S→T₁≡S→T₂
  where
    S→T₁≡S→T₂ : S→T₁ ≡ S→T₂
    S→T₁≡S→T₂ = isSurjective→rightCancel h S→T₁ S→T₂ hSurjective fS→T₁≡fS→T₂

-- S has at least two elements.
notSingleton : (S : Set) → Type₀
notSingleton S = Σ[ xs ∈ (S × S) ]( ¬ (fst xs ≡ snd xs) )

-- Commenting this out, as I think we would need to make even more assumptions
-- to make this work without excluded middle / choice.
-- homFun'Inj← : {W S T : Set} (h : W → S) →
--   notSingleton T →
--   Discrete S →
--   isInjective (homFun' h T) → ¬ ¬ isSurjective h
-- homFun'Inj← {W} {S} {T = T} h notSingletonT discreteS hHomIsInjective hNotSurjective = {!!}
--   where
--     ts : T × T
--     ts = fst notSingletonT

--     f₁ : S → T
--     f₁ = λ _ → fst ts

--     f₂ : S → T
--     f₂ = λ _ → snd ts

--     s : Σ[ s ∈ S ]( ∀ (w : W ) → ¬(h w ≡ s) )
--     s = {!!} -- consequence of hNotSurjective

--     ¬f₁≡f₂ : ¬ f₁ ≡ f₂
--     ¬f₁≡f₂ contra = (snd notSingletonT) oops
--       where
--         oops : fst ts ≡ snd ts
--         oops =
--           fst ts ≡⟨ refl ⟩
--           f₁ (fst s) ≡[ i ]⟨ (contra i) (fst s) ⟩
--           f₂ (fst s) ≡⟨ refl ⟩
--           snd ts ∎


--     -- At this point, we can prove directly that f₁ ∘ h ≡ f₂ ∘ h
--     a≡b : f₁ ∘ h ≡ f₂ ∘ h
--     a≡b = funExt λ w → {!!}

--     ¬a≡b : ¬ (f₁ ∘ h ≡ f₂ ∘ h)
--     ¬a≡b = hHomIsInjective f₁ f₂ ¬f₁≡f₂

-- Definition 1.2.8
×fg : {X S T : Set} (f : X → S) (g : X → T) → X → S × T
×fg f g = λ x → (f x , g x)

×fgIso : {X S T : Set} → Iso (hom X S × hom X T) (hom X (S × T))
×fgIso = iso
  (λ { (f , g) → ×fg f g })
  (λ f → ( λ x → fst (f x)) , λ x → snd (f x))
  (λ _ → refl)
  (λ _ → refl)

×fgId : {S T : Set} → (×fg {S × T} {S} {T} fst snd) ≡ idfun (S × T)
×fgId {S} {T} = funExt λ st → refl

φ : {S T V : Set} → hom S V × hom T V → hom (S ⊎ T) V
φ (f , g) (inl x) = f x
φ (f , g) (inr x) = g x

φ-iso : {S T V : Set} → isIso (φ {S} {T} {V})
φ-iso {S} {T} {V} = φ⁻¹ ,
  (λ { h → funExt λ { (inl x) → refl ; (inr x) → refl } }),
  λ { (f , g) → refl }
  where
    φ⁻¹ : hom (S ⊎ T) V → hom S V × hom T V
    φ⁻¹ f = (λ s → f (inl s)) , λ v → f (inr v)

φId : {S T : Set} → (φ {S} {T} {S ⊎ T} (inl , inr)) ≡ idfun (S ⊎ T)
φId {S} {T} = funExt λ { (inl x) → refl ; (inr x) → refl }


module P where
  open import Cubical.Foundations.Powerset

  Rel : Set → Set → Type₁
  Rel A B = ℙ (A × B)

  φ′ : {A B : Set} → Rel A B → hom A (ℙ B)
  φ′ rel a = λ b → ((a , b) ∈ rel) , (∈-isProp rel (a , b))

  φ′⁻¹ : {A B : Set} → hom A (ℙ B) → Rel A B
  φ′⁻¹ A→ℙB (a , b) = (b ∈ (A→ℙB a)) , (∈-isProp (A→ℙB a) b)

  φ′-iso : {A B : Set} → isIso (φ′ {A} {B})
  φ′-iso = φ′⁻¹ ,
    (λ b → refl),
    λ b → refl

  -- The diagonal relation.
  Δ : (A : Set) → Rel A A
  Δ A = λ (a₁ , a₂) → ⊤ , isPropUnit

  φ′Id : {A : Set} → (φ′⁻¹ {A} {A} λ a₁ a₂ → ⊤ , isPropUnit) ≡ Δ A
  φ′Id = funExt λ aa → refl

  -- Universe management is tricky here
  -- φ′IdB : {B : Set} → (φ′⁻¹ {ℙ B} {B} ?) ≡ idfun B
  -- φ′IdB = funExt λ aa → refl
