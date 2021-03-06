module Cx.Elim where

open import Common
open import Container.List

open import Cx.Cx
open import Cx.Named.Desc

-- Dependent case function
CaseHypCon : ∀ {I Γ} (c : ConDesc I Γ) (γ : ⟦ Γ ⟧) (A : ⟦ I ⟧ → Set)
          → ((i : ⟦ I ⟧) → ⟦ c ⟧ γ A i → Set) → Set
CaseHypCon (ι o)           γ A T = T (o γ) refl
CaseHypCon (nm /    S ⊗ c) γ A T = (x : S γ)     → CaseHypCon c (γ , x) A (λ i xs → T i (x , xs))
CaseHypCon (nm /rec j ⊗ c) γ A T = (x : A (j γ)) → CaseHypCon c γ       A (λ i xs → T i (x , xs))

CaseHypDat : ∀ {I Γ #c} (d : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (A : ⟦ I ⟧ → Set)
          → (T : (i : ⟦ I ⟧) → ⟦ d ⟧ γ A i → Set) → Set
CaseHypDat `0       γ A T = ⊥
CaseHypDat (c ⊕ cs) γ A T = CaseHypCon c γ A (λ i x → T i (zero , x))
                          × CaseHypDat cs γ A (λ i → T i ∘ (suc *** id))

CaseHyp : ∀ {I Γ #c} (d : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (T : (i : ⟦ I ⟧) → μ d γ i → Set) → Set
CaseHyp d γ T = CaseHypDat d γ (μ d γ) (λ i x → T i ⟨ x ⟩)

caseCon : ∀ {I Γ} (c : ConDesc I Γ) {γ : ⟦ Γ ⟧} {A} (T : (i : ⟦ I ⟧) → ⟦ c ⟧ γ A i → Set)
        → CaseHypCon c γ A T → {i : ⟦ I ⟧} (x : ⟦ c ⟧ γ A i)  → T i x
caseCon (ι o)           T h refl     = h
caseCon (nm /    S ⊗ c) T h (x , xs) = caseCon c (λ i xs → T i (x , xs)) (h x) xs
caseCon (nm /rec i ⊗ c) T h (x , xs) = caseCon c (λ i xs → T i (x , xs)) (h x) xs

caseDat : ∀ {I Γ #c} (d : DatDesc I Γ #c) {γ : ⟦ Γ ⟧} {A} (T : (i : ⟦ I ⟧) → ⟦ d ⟧ γ A i → Set)
        → CaseHypDat d γ A T → {i : ⟦ I ⟧} (x : ⟦ d ⟧ γ A i)  → T i x
caseDat `0 T () x
caseDat (c ⊕ cs) T (h , hs) (zero  , v) = caseCon c  (λ i x → T i (zero , x))   h  v
caseDat (c ⊕ cs) T (h , hs) (suc k , v) = caseDat cs (λ i → T i ∘ (suc *** id)) hs (k , v)

case : ∀ {I Γ #c} (d : DatDesc I Γ #c) {γ : ⟦ Γ ⟧} (T : (i : ⟦ I ⟧) → μ d γ i → Set)
     → CaseHyp d γ T → ∀ {i} x → T i x
case d T h ⟨ x ⟩ = caseDat d (λ i x → T i ⟨ x ⟩) h x

module Test-case-nondependent where
  open import Cx.Named.Examples

  case-nat : (X : Set)
           → (X × (μ natD tt tt → X) × ⊥)
           → μ natD tt tt → X
  case-nat X n = case natD (λ _ _ → X) n

  case-list : {A : Set} (X : Set)
            → (X × (A → μ listD (tt , A) tt → X) × ⊥)
            → μ listD (tt , A) tt → X
  case-list X n = case listD (λ _ _ → X) n

module Test-case-dependent where
  open import Cx.Named.Examples

  case-nat : (X : μ natD tt tt → Set)
           → (X ⟨ 0 , refl ⟩ × ((n : μ natD tt tt) → X ⟨ 1 , n , refl ⟩) × ⊥)
           → (n : μ natD tt tt) → X n
  case-nat X n = case natD (λ _ → X) n

  case-list : {A : Set} (X : μ listD (tt , A) tt → Set)
            → (X ⟨ 0 , refl ⟩ × ((x : A) (xs : μ listD (tt , A) tt) → X ⟨ 1 , x , xs , refl ⟩) × ⊥)
            → (l : μ listD (tt , A) tt) → X l
  case-list X n = case listD (λ _ → X) n

-- The eliminator
ElimHypCon : ∀ {I Γ} (c : ConDesc I Γ) (γ : ⟦ Γ ⟧)
           → (A : ⟦ I ⟧ → Set) (R : (i : ⟦ I ⟧) → A i → Set)
           → ((i : ⟦ I ⟧) → ⟦ c ⟧ γ A i → Set) → Set
ElimHypCon (ι o)           γ A R T = T (o γ) refl
ElimHypCon (nm /    S ⊗ c) γ A R T = (x : S γ)
                                   → ElimHypCon c (γ , x) A R (λ i xs → T i (x , xs))
ElimHypCon (nm /rec j ⊗ c) γ A R T = (x : A (j γ))
                                   → R (j γ) x
                                   → ElimHypCon c γ A R (λ i xs → T i (x , xs))

ElimHypDat : ∀ {I Γ #c} (d : DatDesc I Γ #c) (γ : ⟦ Γ ⟧)
           → (A : ⟦ I ⟧ → Set) (R : (i : ⟦ I ⟧) → A i → Set)
           → (T : (i : ⟦ I ⟧) → ⟦ d ⟧ γ A i → Set) → Set
ElimHypDat `0       γ A R T = ⊥
ElimHypDat (c ⊕ cs) γ A R T = ElimHypCon c γ A R (λ i x → T i (zero , x))
                            × ElimHypDat cs γ A R (λ i → T i ∘ (suc *** id))

ElimHyp : ∀ {I Γ #c} (d : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (T : (i : ⟦ I ⟧) → μ d γ i → Set) → Set
ElimHyp d γ T = ElimHypDat d γ (μ d γ) T (λ i x → T i ⟨ x ⟩)

module _ {I Γ #c} (d : DatDesc I Γ #c)
         {γ : ⟦ Γ ⟧} (R : (i : ⟦ I ⟧) → μ d γ i → Set)
         (h : ElimHyp d γ R) where

  D : ⟦ I ⟧ → Set
  D i = μ d γ i

  elim : ∀ {i} x → R i x

  elimCon : ∀ {Γ'} (c : ConDesc I Γ') {γ : ⟦ Γ' ⟧}
          → (T : (i : ⟦ I ⟧) → ⟦ c ⟧ γ D i → Set)
          → ElimHypCon c γ D R T → {i : ⟦ I ⟧} (x : ⟦ c ⟧ γ D i) → T i x
  elimCon (ι o)           T h refl     = h
  elimCon (nm /    S ⊗ c) T h (x , xs) = elimCon c (λ i xs → T i (x , xs)) (h x) xs
  elimCon (nm /rec i ⊗ c) T h (x , xs) = elimCon c (λ i xs → T i (x , xs)) (h x (elim x)) xs

  elimDat : ∀ {#c'} (d' : DatDesc I Γ #c') {γ : ⟦ Γ ⟧}
          → (T : (i : ⟦ I ⟧) → ⟦ d' ⟧ γ D i → Set)
          → ElimHypDat d' γ D R T → {i : ⟦ I ⟧} (x : ⟦ d' ⟧ γ D i)  → T i x
  elimDat `0       T ()       x
  elimDat (c ⊕ cs) T (h , hs) (zero  , v) = elimCon c  (λ i x → T i (zero , x))   h  v
  elimDat (c ⊕ cs) T (h , hs) (suc k , v) = elimDat cs (λ i → T i ∘ (suc *** id)) hs (k , v)

  elim ⟨ x ⟩ = elimDat d (λ i x → R i ⟨ x ⟩) h x

module Test-elim-nondependent where
  open import Cx.Named.Examples

  elim-nat : (X : Set)
           → (X × (μ natD tt tt → X → X) × ⊥)
           → μ natD tt tt → X
  elim-nat X n = elim natD (λ _ _ → X) n

  elim-list : {A : Set} (X : Set)
            → (X × (A → μ listD (tt , A) tt → X → X) × ⊥)
            → μ listD (tt , A) tt → X
  elim-list X n = elim listD (λ _ _ → X) n

module Test-elim-dependent where
  open import Cx.Named.Examples

  elim-nat : (X : μ natD tt tt → Set)
           → (X ⟨ 0 , refl ⟩ × ((n : μ natD tt tt) → X n → X ⟨ 1 , n , refl ⟩) × ⊥)
           → (n : μ natD tt tt) → X n
  elim-nat X n = elim natD (λ _ → X) n

  elim-list : {A : Set} (X : μ listD (tt , A) tt → Set)
            → (X ⟨ 0 , refl ⟩ × ((x : A) (xs : μ listD (tt , A) tt) → X xs → X ⟨ 1 , x , xs , refl ⟩) × ⊥)
            → (l : μ listD (tt , A) tt) → X l
  elim-list X n = elim listD (λ _ → X) n
