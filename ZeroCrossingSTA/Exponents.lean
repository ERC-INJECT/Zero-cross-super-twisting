import Mathlib

namespace ZeroCrossingSTA

noncomputable section

/-- Homogeneous exponent alpha = 1/(1-ell). -/
def alpha (ell : ℝ) : ℝ := 1 / (1 - ell)

/-- Homogeneous exponent beta = (1+ell)/(1-ell). -/
def beta (ell : ℝ) : ℝ := (1 + ell) / (1 - ell)

lemma one_sub_ell_pos {ell : ℝ} (hell : ell ≤ 0) : 0 < 1 - ell := by
  linarith

lemma alpha_pos {ell : ℝ} (hell : ell ≤ 0) : 0 < alpha ell := by
  unfold alpha
  exact div_pos (by norm_num) (one_sub_ell_pos hell)

lemma beta_nonneg {ell : ℝ} (hlo : -1 ≤ ell) (hhi : ell ≤ 0) : 0 ≤ beta ell := by
  unfold beta
  exact div_nonneg (by linarith) (le_of_lt (one_sub_ell_pos hhi))

lemma beta_le_one {ell : ℝ} (hell : ell ≤ 0) : beta ell ≤ 1 := by
  unfold beta
  have hden : 0 < 1 - ell := one_sub_ell_pos hell
  apply (div_le_iff₀ hden).2
  linarith

lemma beta_le_alpha {ell : ℝ} (hell : ell ≤ 0) : beta ell ≤ alpha ell := by
  unfold alpha beta
  have hden : 0 < 1 - ell := one_sub_ell_pos hell
  apply (div_le_div_iff_of_pos_right hden).2
  linarith

lemma beta_eq_two_alpha_sub_one {ell : ℝ} (hell : ell ≤ 0) :
    beta ell = 2 * alpha ell - 1 := by
  unfold alpha beta
  have hden : 1 - ell ≠ 0 := ne_of_gt (one_sub_ell_pos hell)
  field_simp [hden]
  ring

lemma one_sub_alpha_eq_homogeneous_time_exponent {ell : ℝ} (hell : ell ≤ 0) :
    1 - alpha ell = (-ell) / (1 - ell) := by
  unfold alpha
  have hden : 1 - ell ≠ 0 := ne_of_gt (one_sub_ell_pos hell)
  field_simp [hden]
  ring

@[simp] lemma alpha_neg_one : alpha (-1) = (1 / 2 : ℝ) := by
  norm_num [alpha]

@[simp] lemma beta_neg_one : beta (-1) = 0 := by
  norm_num [beta]

@[simp] lemma alpha_zero : alpha 0 = 1 := by
  norm_num [alpha]

@[simp] lemma beta_zero : beta 0 = 1 := by
  norm_num [beta]

end
end ZeroCrossingSTA
