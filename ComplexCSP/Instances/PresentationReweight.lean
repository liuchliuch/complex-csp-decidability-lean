import ComplexCSP.Instances.PresentationAlgorithms
import ComplexCSP.Instances.ValueTransport

/-! # Reinterpretation of finite templates across coefficient representations -/
namespace ComplexCSP
variable {D K R S ι B H : Type}

namespace Language
/-- Retain the exact arity signature while replacing all coefficient data. -/
def reweight (L : Language D K ι) (value : ∀ i, (Fin (L.arity i) → D) → R) :
    Language D R ι := ⟨L.arity,L.arity_pos,value⟩
end Language

namespace Instance
variable {L : Language D K ι}

def reweight (I : Instance L B H) (value : ∀ i, (Fin (L.arity i) → D) → R) :
    Instance (L.reweight value) B H :=
  ⟨I.constraints.map (fun c => ⟨c.symbol,c.scope⟩)⟩

@[simp] theorem reweight_reweight (I : Instance L B H)
    (value : ∀ i, (Fin (L.arity i) → D) → R)
    (value' : ∀ i, (Fin (L.arity i) → D) → S) :
    (I.reweight value).reweight value' = I.reweight value' := by
  cases I
  simp only [reweight,List.map_map]
  rfl

@[simp] theorem reweight_self (I : Instance L B H) : I.reweight L.value = I := by
  cases I with
  | mk cs =>
    change Instance.mk (cs.map id) = Instance.mk cs
    rw [List.map_id]

 theorem partition_reweight_map [CommSemiring K] [CommSemiring R] [Fintype D]
    [Fintype H] [DecidableEq H] (I : Instance L B H) (σ : K →+* R) (a : B → D) :
    (I.reweight (fun i x => σ (L.value i x))).partition a = σ (I.partition a) :=
  partition_mapValues I σ a

end Instance

namespace Presentation
variable {L : Language D K ι}

def reweight (P : Presentation L B) (value : ∀ i, (Fin (L.arity i) → D) → R) :
    Presentation (L.reweight value) B := ⟨P.hidden,P.inst.reweight value⟩

@[simp] theorem reweight_reweight (P : Presentation L B)
    (value : ∀ i, (Fin (L.arity i) → D) → R)
    (value' : ∀ i, (Fin (L.arity i) → D) → S) :
    (P.reweight value).reweight value' = P.reweight value' := by
  cases P
  simp only [reweight,Instance.reweight_reweight]

@[simp] theorem reweight_self (P : Presentation L B) : P.reweight L.value = P := by
  cases P
  simp only [reweight,Instance.reweight_self]

 theorem table_reweight_map [CommSemiring K] [CommSemiring R] [Fintype D]
    (P : Presentation L B) (σ : K →+* R) (a : B → D) :
    (P.reweight (fun i x => σ (L.value i x))).table a = σ (P.table a) :=
  P.inst.partition_reweight_map σ a

end Presentation
end ComplexCSP
