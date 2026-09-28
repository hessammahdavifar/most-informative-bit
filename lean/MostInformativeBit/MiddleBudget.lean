import MostInformativeBit.PivotalLogSum
import MostInformativeBit.GrowthBudget

namespace MostInformativeBit
open scoped BigOperators
open Real

theorem mass_log_lower {Z V : ℝ} (hZ : 0 < Z) (hV : 0 < V) :
    Z-V ≤ Z*log (Z/V) := by
  have hh := one_sub_inv_le_log_of_pos (div_pos hZ hV)
  have hm := mul_le_mul_of_nonneg_left hh hZ.le
  have he : Z*(1-(Z/V)⁻¹) = Z-V := by field_simp
  rwa [he] at hm

/-- A channel-profile comparison converted into the exact tilted mass bound. -/
theorem tilted_mass_of_profile {a v V ell Ftop Fv beta Htop Hv : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hV : 0 < V) (he : 0 < ell)
    (hf : 0 < Ftop) (hheight : Fv = V*Ftop/a)
    (hprofile : beta*(Htop-Hv) ≤ log (v*Fv/(ell*Ftop))) :
    a^2*exp (-beta*Hv) ≤ (V/ell)*exp (-beta*Htop)*(a*v) := by
  have hratio : 0 < v*Fv/(ell*Ftop) := by rw [hheight]; positivity
  have hh := Real.exp_le_exp.mpr hprofile
  rw [Real.exp_log hratio] at hh
  have hm := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ a^2*exp (-beta*Htop) by positivity)
  have hleft : exp (beta*(Htop-Hv))*(a^2*exp (-beta*Htop)) =
      a^2*exp (-beta*Hv) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hright : (v*Fv/(ell*Ftop))*(a^2*exp (-beta*Htop)) =
      (V/ell)*exp (-beta*Htop)*(a*v) := by
    rw [hheight]
    field_simp
  rwa [hleft, hright] at hm

theorem tilted_budget_of_profiles {ι : Type*} (s : Finset ι)
    (a v Fv H : ι → ℝ) {V ell Ftop beta Htop : ℝ}
    (ha : ∀ i ∈ s, 0 < a i) (hv : ∀ i ∈ s, 0 < v i)
    (hV : 0 < V) (he : 0 < ell) (hf : 0 < Ftop)
    (hheight : ∀ i ∈ s, Fv i = V*Ftop/a i)
    (hprofile : ∀ i ∈ s, beta*(Htop-H i) ≤ log (v i*Fv i/(ell*Ftop)))
    (hweight : (∑ i ∈ s, a i*v i) ≤ ell) :
    (∑ i ∈ s, a i^2*exp (-beta*H i)) ≤ V*exp (-beta*Htop) := by
  have hh := Finset.sum_le_sum (fun i hi =>
    tilted_mass_of_profile (ha i hi) (hv i hi) hV he hf
      (hheight i hi) (hprofile i hi))
  rw [← Finset.mul_sum] at hh
  have hm := mul_le_mul_of_nonneg_left hweight
    (show 0 ≤ V/ell*exp (-beta*Htop) by positivity)
  have hid : (V/ell*exp (-beta*Htop))*ell = V*exp (-beta*Htop) := by field_simp
  rw [hid] at hm
  exact le_trans hh hm

/-- Middle-regime closure with all finite log-sum steps discharged. The stated
profile, edge, spectral, and channel inequalities are the separate analytic inputs. -/
theorem middle_pivotal_closure {ι : Type*} (s : Finset ι)
    (z a v Fv H : ι → ℝ)
    {action angular r ell theta eta gamma delta V m meanCorrection Ftop Htop : ℝ}
    (hr : 0 < r) (he : 0 < eta) (hg : 0 < gamma) (hd : 0 < delta)
    (hV : 0 < V) (hell : 0 < ell) (hf : 0 < Ftop)
    (ha : ∀ i ∈ s, 0 < a i) (hv : ∀ i ∈ s, 0 < v i)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hza : ∀ i ∈ s, z i ≤ a i)
    (hH : ∀ i ∈ s, 0 ≤ H i)
    (hZ : 0 < ∑ i ∈ s, z i) (hZV : (∑ i ∈ s, z i) ≤ V)
    (hvariance : V = 1-m^2)
    (hheight : ∀ i ∈ s, Fv i = V*Ftop/a i)
    (hprofile : ∀ i ∈ s, (2*r/eta)*(Htop-H i) ≤ log (v i*Fv i/(ell*Ftop)))
    (hweight : (∑ i ∈ s, a i*v i) ≤ ell)
    (hidentity : r*ell = theta^2+r*Htop)
    (henergy : 0 ≤ theta^2-r*Htop-eta/2)
    (hmean : 0 ≤ meanCorrection-r*Htop*m^2)
    (hbaseline : theta^2*(1+V-(∑ i ∈ s, z i))+
      eta/2*(∑ i ∈ s, z i*log (z i/a i^2))+meanCorrection+2*gamma*delta ≤ angular)
    (hedge : angular+r*(∑ i ∈ s, a i*H i) ≤ action) :
    r*ell < action := by
  have hb := tilted_budget_of_profiles s a v Fv H ha hv hV hell hf hheight hprofile hweight
  have hc := pivotal_log_compensation s z a H hr.le he hV ha hz hza hH hZ hb
  have hl := mul_le_mul_of_nonneg_left (mass_log_lower hZ hV)
    (show 0 ≤ eta/2 by positivity)
  have hreserve := mul_nonneg henergy (sub_nonneg.mpr hZV)
  have hstrict : 0 < 2*gamma*delta := by positivity
  rw [hvariance] at hbaseline hl hreserve hc
  rw [hidentity]
  nlinarith only [hbaseline, hedge, hc, hl, hreserve, hstrict, hmean]

end MostInformativeBit
