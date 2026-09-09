import GraphCut
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option maxHeartbeats 3000000
namespace HubAveraging
noncomputable section
open Finset MeasureTheory
open scoped ENNReal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def cutMaximum (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) : ℝ :=
  univ.sup' univ_nonempty (cutCap G color)

omit [DecidableEq V] in
theorem cutCap_le_maximum (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) : cutCap G color v ≤ cutMaximum G color := by
  exact le_sup' (f := cutCap G color) (mem_univ v)

omit [DecidableEq V] in
theorem cutMaximum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (k : ℕ) (hk : ∀ v, sameDegree G color v ≤ k) :
    cutMaximum G color ≤ 4*((k : ℝ)+1) := by
  apply (sup'_le_iff univ_nonempty (cutCap G color)).mpr
  intro v _
  have hkv : (sameDegree G color v : ℝ) ≤ k := by exact_mod_cast hk v
  have hb := cut_constant_le (G.degree v : ℝ) (sameDegree G color v : ℝ)
    (by positivity) (by positivity)
  unfold cutCap at ⊢
  linarith

/-- Extended expected residual permits arbitrary output distributions,
including outputs with infinite expected energy. -/
def worstBlockResidual {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : (V → ℝ) → Ω → (V → ℝ)) : ℝ≥0∞ :=
  ⨆ x : {x : V → ℝ // 0 < disagreement x},
    ∫⁻ o, ENNReal.ofReal (disagreement (T x.1 o)/disagreement x.1) ∂μ

/- Proposition 5 with arbitrary randomness and real-valued local outputs.
The lower integral also covers the infinite-expectation case. -/
theorem arbitrary_random_cut_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (hbal : total (signState color) = 0)
    (hub : (V → ℝ) → Ω → V) (T : (V → ℝ) → Ω → (V → ℝ))
    (hpres : ∀ x o, (∑ u ∈ closedBlock G (hub x o), T x o u) =
      ∑ u ∈ closedBlock G (hub x o), x u)
    (hoff : ∀ x o u, u ∉ closedBlock G (hub x o) → T x o u = x u) :
    ENNReal.ofReal (max 0 (1-cutMaximum G color/Fintype.card V)) ≤ worstBlockResidual μ T := by
  let w := signState color
  have hw : disagreement w = Fintype.card V := by
    rw [disagreement_of_total_zero _ hbal, sign_energy _ (signState_values color)]
  have hwpos : 0 < disagreement w := by rw [hw]; exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hb (o : Ω) : max 0 (1-cutMaximum G color/Fintype.card V) ≤
      disagreement (T w o)/disagreement w := by
    rw [hw]
    calc
      _ ≤ max 0 (1-cutCap G color (hub w o)/Fintype.card V) := by
        apply max_le_max le_rfl
        exact sub_le_sub_left (div_le_div_of_nonneg_right (cutCap_le_maximum G color (hub w o)) hN.le) _
      _ ≤ _ := graph_cut_residual G color hbal (hub w o) (T w o) (hpres w o) (hoff w o)
  apply le_iSup_of_le (⟨w,hwpos⟩ : {x : V → ℝ // 0 < disagreement x})
  calc
    _ = ∫⁻ _o, ENNReal.ofReal (max 0 (1-cutMaximum G color/Fintype.card V)) ∂μ := by simp
    _ ≤ _ := lintegral_mono fun o => ENNReal.ofReal_le_ofReal (hb o)

end
end HubAveraging
