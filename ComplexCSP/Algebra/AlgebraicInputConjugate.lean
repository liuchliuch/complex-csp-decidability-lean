import ComplexCSP.Algebra.AlgebraicInput
import ComplexCSP.Algebra.InitialPrimitiveCoordinates

/-! # Exact conjugate descriptions and paired input encoding -/
namespace ComplexCSP.AlgebraicEncoding
open ComplexRootCertificates

/-- Reflection of an open rational rectangle across the real axis. -/
def conjugateRectangle (box : Rectangle) : Rectangle :=
  ⟨box.reLo,box.reHi,-box.imHi,-box.imLo⟩

@[simp] theorem conjugateRectangle_contains (box : Rectangle) (z : ℂ) :
    (conjugateRectangle box).Contains (star z) ↔ box.Contains z := by
  simp only [Rectangle.Contains, conjugateRectangle, RCLike.star_def, Complex.conj_re,
    Complex.conj_im, Rat.cast_neg, neg_lt_neg_iff]
  tauto

/-- Integer coefficients are unchanged by conjugation. -/
def AlgebraicInput.conjugate (a : AlgebraicInput) : AlgebraicInput :=
  ⟨a.coefficients,conjugateRectangle a.rectangle⟩

 theorem AlgebraicInput.Represents.conjugate {a : AlgebraicInput} {z : ℂ}
    (h : a.Represents z) : a.conjugate.Represents (star z) := by
  refine ⟨h.1, ?_, (conjugateRectangle_contains a.rectangle z).mpr h.2.2.1, ?_⟩
  · have he := map_evalIntegerList (starRingEnd ℂ) a.coefficients z
    simpa only [starRingEnd_apply, h.2.1, map_zero] using he.symm
  · intro w hwroot hwbox
    apply star_injective
    simp only [star_star]
    apply h.2.2.2
    · have he := map_evalIntegerList (starRingEnd ℂ) a.coefficients w
      change evalIntegerList a.coefficients w = 0 at hwroot
      simpa only [starRingEnd_apply, hwroot, map_zero] using he.symm
    · exact (conjugateRectangle_contains a.rectangle (star w)).mp
        (by simpa only [star_star] using hwbox)

/-- Originals followed by their exact conjugate descriptions. -/
def pairedDescriptions {m : ℕ} (input : Fin m → AlgebraicInput)
    (i : Fin (m+m)) : AlgebraicInput :=
  Sum.elim input (fun j => (input j).conjugate) (finSumFinEquiv.symm i)

 theorem pairedDescriptions_represents {m : ℕ} (input : Fin m → AlgebraicInput)
    (z : Fin m → ℂ) (hz : ∀ i, (input i).Represents (z i)) :
    ∀ i, (pairedDescriptions input i).Represents (pairedInputs z i) := by
  intro i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl i => simpa only [pairedDescriptions, pairedInputs, Equiv.symm_apply_apply,
      Sum.elim_inl] using hz i
  | inr i => simpa only [pairedDescriptions, pairedInputs, Equiv.symm_apply_apply,
      Sum.elim_inr] using (hz i).conjugate

end ComplexCSP.AlgebraicEncoding
