import MostInformativeBit.LowNumericalBridge

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace MostInformativeBit
namespace LowCertificates
open IntervalBounds

noncomputable def v0 : ℝ := Real.exp ((31:ℝ)/40)
theorem b0 : Encloses v0 ((2170592127183:ℝ)/1000000000000) ((135662007949:ℝ)/62500000000) := by
  unfold v0
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (31:ℝ)/40) 16
  have hu := Real.exp_bound' (by norm_num : 0 ≤ (31:ℝ)/40) (by norm_num : (31:ℝ)/40 ≤ 1) (by norm_num : 0 < (16:ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at hl hu
  constructor <;> linarith

noncomputable def v1 : ℝ := v0^4
theorem b1 : Encloses v1 ((22197951281423:ℝ)/1000000000000) ((4439590256293:ℝ)/200000000000) := by
  unfold v1
  exact weaken (pow_nonneg b0 (by norm_num) 4) (by norm_num) (by norm_num)

noncomputable def v2 : ℝ := Real.exp (31/10)
theorem b2 : Encloses v2 ((22197951281423:ℝ)/1000000000000) ((4439590256293:ℝ)/200000000000) := by
  unfold v2
  rw [show (31:ℝ)/10 = (4:ℕ)*(31/40) by norm_num, Real.exp_nat_mul]
  exact b1

noncomputable def v3 : ℝ := (1:ℝ)
theorem b3 : Encloses v3 ((1:ℝ)) ((1:ℝ)) := by
  unfold v3
  exact exact_value _

noncomputable def v4 : ℝ := v2-v3
theorem b4 : Encloses v4 ((21197951281423:ℝ)/1000000000000) ((4239590256293:ℝ)/200000000000) := by
  unfold v4
  exact weaken (sub b2 b3) (by norm_num) (by norm_num)

noncomputable def v5 : ℝ := v2+v3
theorem b5 : Encloses v5 ((23197951281423:ℝ)/1000000000000) ((4639590256293:ℝ)/200000000000) := by
  unfold v5
  exact weaken (add b2 b3) (by norm_num) (by norm_num)

noncomputable def v6 : ℝ := v4/v5
theorem b6 : Encloses v6 ((228446372529:ℝ)/250000000000) ((22844637253:ℝ)/25000000000) := by
  unfold v6
  exact weaken (div_nonneg b4 b5 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v7 : ℝ := lowCutoff
theorem b7 : Encloses v7 ((228446372529:ℝ)/250000000000) ((22844637253:ℝ)/25000000000) := by
  unfold v7
  rw [lowCutoff_exp]
  exact b6

noncomputable def v8 : ℝ := (2:ℝ)/5
theorem b8 : Encloses v8 ((2:ℝ)/5) ((2:ℝ)/5) := by
  unfold v8
  exact exact_value _

noncomputable def v9 : ℝ := (2:ℝ)/3
theorem b9 : Encloses v9 ((2:ℝ)/3) ((2:ℝ)/3) := by
  unfold v9
  exact exact_value _

noncomputable def v10 : ℝ := v3+v8
theorem b10 : Encloses v10 ((7:ℝ)/5) ((7:ℝ)/5) := by
  unfold v10
  exact weaken (add b3 b8) (by norm_num) (by norm_num)

noncomputable def v11 : ℝ := (2:ℝ)
theorem b11 : Encloses v11 ((2:ℝ)) ((2:ℝ)) := by
  unfold v11
  exact exact_value _

noncomputable def v12 : ℝ := v11/v10
theorem b12 : Encloses v12 ((1428571428571:ℝ)/1000000000000) ((357142857143:ℝ)/250000000000) := by
  unfold v12
  exact weaken (div_nonneg b11 b10 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v13 : ℝ := Real.log ((1428571428571:ℝ)/1000000000000)
theorem b13 : Encloses v13 ((178337471969:ℝ)/500000000000) ((356674943939:ℝ)/1000000000000) := by
  unfold v13
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (428571428571:ℝ)/2428571428571) (by norm_num : (428571428571:ℝ)/2428571428571 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (428571428571:ℝ)/2428571428571) (by norm_num : (428571428571:ℝ)/2428571428571 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v14 : ℝ := Real.log ((357142857143:ℝ)/250000000000)
theorem b14 : Encloses v14 ((356674943939:ℝ)/1000000000000) ((17833747197:ℝ)/50000000000) := by
  unfold v14
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (107142857143:ℝ)/607142857143) (by norm_num : (107142857143:ℝ)/607142857143 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (107142857143:ℝ)/607142857143) (by norm_num : (107142857143:ℝ)/607142857143 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v15 : ℝ := Real.log v12
theorem b15 : Encloses v15 ((178337471969:ℝ)/500000000000) ((17833747197:ℝ)/50000000000) := by
  unfold v15
  exact IntervalBounds.log b12 (by norm_num) b13.1 b14.2

noncomputable def v16 : ℝ := v3-v8
theorem b16 : Encloses v16 ((3:ℝ)/5) ((3:ℝ)/5) := by
  unfold v16
  exact weaken (sub b3 b8) (by norm_num) (by norm_num)

noncomputable def v17 : ℝ := v16^2
theorem b17 : Encloses v17 ((9:ℝ)/25) ((9:ℝ)/25) := by
  unfold v17
  exact weaken (pow_nonneg b16 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v18 : ℝ := v15/v17
theorem b18 : Encloses v18 ((990763733161:ℝ)/1000000000000) ((990763733167:ℝ)/1000000000000) := by
  unfold v18
  exact weaken (div_nonneg b15 b17 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v19 : ℝ := v3+v9
theorem b19 : Encloses v19 ((833333333333:ℝ)/500000000000) ((1666666666667:ℝ)/1000000000000) := by
  unfold v19
  exact weaken (add b3 b9) (by norm_num) (by norm_num)

noncomputable def v20 : ℝ := v11/v19
theorem b20 : Encloses v20 ((1199999999999:ℝ)/1000000000000) ((1200000000001:ℝ)/1000000000000) := by
  unfold v20
  exact weaken (div_nonneg b11 b19 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v21 : ℝ := Real.log ((1199999999999:ℝ)/1000000000000)
theorem b21 : Encloses v21 ((182321556793:ℝ)/1000000000000) ((91160778397:ℝ)/500000000000) := by
  unfold v21
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (199999999999:ℝ)/2199999999999) (by norm_num : (199999999999:ℝ)/2199999999999 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (199999999999:ℝ)/2199999999999) (by norm_num : (199999999999:ℝ)/2199999999999 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v22 : ℝ := Real.log ((1200000000001:ℝ)/1000000000000)
theorem b22 : Encloses v22 ((91160778397:ℝ)/500000000000) ((36464311359:ℝ)/200000000000) := by
  unfold v22
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (200000000001:ℝ)/2200000000001) (by norm_num : (200000000001:ℝ)/2200000000001 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (200000000001:ℝ)/2200000000001) (by norm_num : (200000000001:ℝ)/2200000000001 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v23 : ℝ := Real.log v20
theorem b23 : Encloses v23 ((182321556793:ℝ)/1000000000000) ((36464311359:ℝ)/200000000000) := by
  unfold v23
  exact IntervalBounds.log b20 (by norm_num) b21.1 b22.2

noncomputable def v24 : ℝ := v3-v9
theorem b24 : Encloses v24 ((333333333333:ℝ)/1000000000000) ((166666666667:ℝ)/500000000000) := by
  unfold v24
  exact weaken (sub b3 b9) (by norm_num) (by norm_num)

noncomputable def v25 : ℝ := v24^2
theorem b25 : Encloses v25 ((11111111111:ℝ)/100000000000) ((13888888889:ℝ)/125000000000) := by
  unfold v25
  exact weaken (pow_nonneg b24 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v26 : ℝ := v23/v25
theorem b26 : Encloses v26 ((1640894011123:ℝ)/1000000000000) ((410223502793:ℝ)/250000000000) := by
  unfold v26
  exact weaken (div_nonneg b23 b25 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v27 : ℝ := v11*v8
theorem b27 : Encloses v27 ((4:ℝ)/5) ((4:ℝ)/5) := by
  unfold v27
  exact weaken (mul_nonneg b11 b8 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v28 : ℝ := v3+v8
theorem b28 : Encloses v28 ((7:ℝ)/5) ((7:ℝ)/5) := by
  unfold v28
  exact weaken (add b3 b8) (by norm_num) (by norm_num)

noncomputable def v29 : ℝ := v3-v8
theorem b29 : Encloses v29 ((3:ℝ)/5) ((3:ℝ)/5) := by
  unfold v29
  exact weaken (sub b3 b8) (by norm_num) (by norm_num)

noncomputable def v30 : ℝ := v28/v29
theorem b30 : Encloses v30 ((2333333333333:ℝ)/1000000000000) ((1166666666667:ℝ)/500000000000) := by
  unfold v30
  exact weaken (div_nonneg b28 b29 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v31 : ℝ := Real.log ((2333333333333:ℝ)/2000000000000)
theorem b31 : Encloses v31 ((154150679827:ℝ)/1000000000000) ((38537669957:ℝ)/250000000000) := by
  unfold v31
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (333333333333:ℝ)/4333333333333) (by norm_num : (333333333333:ℝ)/4333333333333 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (333333333333:ℝ)/4333333333333) (by norm_num : (333333333333:ℝ)/4333333333333 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v32 : ℝ := Real.log ((2:ℝ))
theorem b32 : Encloses v32 ((693147180559:ℝ)/1000000000000) ((8664339757:ℝ)/12500000000) := by
  unfold v32
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (1:ℝ)/3) (by norm_num : (1:ℝ)/3 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (1:ℝ)/3) (by norm_num : (1:ℝ)/3 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v33 : ℝ := v3*v32
theorem b33 : Encloses v33 ((693147180559:ℝ)/1000000000000) ((8664339757:ℝ)/12500000000) := by
  unfold v33
  exact weaken (mul_nonneg b3 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v34 : ℝ := v31+v33
theorem b34 : Encloses v34 ((423648930193:ℝ)/500000000000) ((211824465097:ℝ)/250000000000) := by
  unfold v34
  exact weaken (add b31 b33) (by norm_num) (by norm_num)

noncomputable def v35 : ℝ := Real.log ((2333333333333:ℝ)/1000000000000)
theorem b35 : Encloses v35 ((423648930193:ℝ)/500000000000) ((211824465097:ℝ)/250000000000) := by
  unfold v35
  have he : Real.log ((2333333333333:ℝ)/1000000000000) = Real.log ((2333333333333:ℝ)/2000000000000) + (1:ℝ)*Real.log 2 := by
    rw [show ((2333333333333:ℝ)/1000000000000) = ((2333333333333:ℝ)/2000000000000) * (2:ℝ)^(1:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b34

noncomputable def v36 : ℝ := Real.log ((1166666666667:ℝ)/1000000000000)
theorem b36 : Encloses v36 ((154150679827:ℝ)/1000000000000) ((38537669957:ℝ)/250000000000) := by
  unfold v36
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (166666666667:ℝ)/2166666666667) (by norm_num : (166666666667:ℝ)/2166666666667 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (166666666667:ℝ)/2166666666667) (by norm_num : (166666666667:ℝ)/2166666666667 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v37 : ℝ := v3*v32
theorem b37 : Encloses v37 ((693147180559:ℝ)/1000000000000) ((8664339757:ℝ)/12500000000) := by
  unfold v37
  exact weaken (mul_nonneg b3 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v38 : ℝ := v36+v37
theorem b38 : Encloses v38 ((423648930193:ℝ)/500000000000) ((211824465097:ℝ)/250000000000) := by
  unfold v38
  exact weaken (add b36 b37) (by norm_num) (by norm_num)

noncomputable def v39 : ℝ := Real.log ((1166666666667:ℝ)/500000000000)
theorem b39 : Encloses v39 ((423648930193:ℝ)/500000000000) ((211824465097:ℝ)/250000000000) := by
  unfold v39
  have he : Real.log ((1166666666667:ℝ)/500000000000) = Real.log ((1166666666667:ℝ)/1000000000000) + (1:ℝ)*Real.log 2 := by
    rw [show ((1166666666667:ℝ)/500000000000) = ((1166666666667:ℝ)/1000000000000) * (2:ℝ)^(1:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b38

noncomputable def v40 : ℝ := Real.log v30
theorem b40 : Encloses v40 ((423648930193:ℝ)/500000000000) ((211824465097:ℝ)/250000000000) := by
  unfold v40
  exact IntervalBounds.log b30 (by norm_num) b35.1 b39.2

noncomputable def v41 : ℝ := v40/v11
theorem b41 : Encloses v41 ((423648930193:ℝ)/1000000000000) ((211824465097:ℝ)/500000000000) := by
  unfold v41
  exact weaken (div_nonneg b40 b11 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v42 : ℝ := Real.artanh v8
theorem b42 : Encloses v42 ((423648930193:ℝ)/1000000000000) ((211824465097:ℝ)/500000000000) := by
  unfold v42
  rw [Real.artanh_eq_half_log (by constructor <;> linarith [b8.1, b8.2])]
  convert b41 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41] <;> ring

noncomputable def v43 : ℝ := v42/v18
theorem b43 : Encloses v43 ((213799171291:ℝ)/500000000000) ((427598342587:ℝ)/1000000000000) := by
  unfold v43
  exact weaken (div_nonneg b42 b18 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v44 : ℝ := v27-v43
theorem b44 : Encloses v44 ((372401657413:ℝ)/1000000000000) ((186200828709:ℝ)/500000000000) := by
  unfold v44
  exact weaken (sub b27 b43) (by norm_num) (by norm_num)

noncomputable def v45 : ℝ := v11*v9
theorem b45 : Encloses v45 ((1333333333333:ℝ)/1000000000000) ((666666666667:ℝ)/500000000000) := by
  unfold v45
  exact weaken (mul_nonneg b11 b9 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v46 : ℝ := v3+v9
theorem b46 : Encloses v46 ((833333333333:ℝ)/500000000000) ((1666666666667:ℝ)/1000000000000) := by
  unfold v46
  exact weaken (add b3 b9) (by norm_num) (by norm_num)

noncomputable def v47 : ℝ := v3-v9
theorem b47 : Encloses v47 ((333333333333:ℝ)/1000000000000) ((166666666667:ℝ)/500000000000) := by
  unfold v47
  exact weaken (sub b3 b9) (by norm_num) (by norm_num)

noncomputable def v48 : ℝ := v46/v47
theorem b48 : Encloses v48 ((1249999999997:ℝ)/250000000000) ((5000000000007:ℝ)/1000000000000) := by
  unfold v48
  exact weaken (div_nonneg b46 b47 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v49 : ℝ := Real.log ((1249999999997:ℝ)/1000000000000)
theorem b49 : Encloses v49 ((223143551311:ℝ)/1000000000000) ((13946471957:ℝ)/62500000000) := by
  unfold v49
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (249999999997:ℝ)/2249999999997) (by norm_num : (249999999997:ℝ)/2249999999997 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (249999999997:ℝ)/2249999999997) (by norm_num : (249999999997:ℝ)/2249999999997 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v50 : ℝ := v11*v32
theorem b50 : Encloses v50 ((693147180559:ℝ)/500000000000) ((8664339757:ℝ)/6250000000) := by
  unfold v50
  exact weaken (mul_nonneg b11 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v51 : ℝ := v49+v50
theorem b51 : Encloses v51 ((1609437912429:ℝ)/1000000000000) ((100589869527:ℝ)/62500000000) := by
  unfold v51
  exact weaken (add b49 b50) (by norm_num) (by norm_num)

noncomputable def v52 : ℝ := Real.log ((1249999999997:ℝ)/250000000000)
theorem b52 : Encloses v52 ((1609437912429:ℝ)/1000000000000) ((100589869527:ℝ)/62500000000) := by
  unfold v52
  have he : Real.log ((1249999999997:ℝ)/250000000000) = Real.log ((1249999999997:ℝ)/1000000000000) + (2:ℝ)*Real.log 2 := by
    rw [show ((1249999999997:ℝ)/250000000000) = ((1249999999997:ℝ)/1000000000000) * (2:ℝ)^(2:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b51

noncomputable def v53 : ℝ := Real.log ((5000000000007:ℝ)/4000000000000)
theorem b53 : Encloses v53 ((44628710263:ℝ)/200000000000) ((55785887829:ℝ)/250000000000) := by
  unfold v53
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (1000000000007:ℝ)/9000000000007) (by norm_num : (1000000000007:ℝ)/9000000000007 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (1000000000007:ℝ)/9000000000007) (by norm_num : (1000000000007:ℝ)/9000000000007 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v54 : ℝ := v11*v32
theorem b54 : Encloses v54 ((693147180559:ℝ)/500000000000) ((8664339757:ℝ)/6250000000) := by
  unfold v54
  exact weaken (mul_nonneg b11 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v55 : ℝ := v53+v54
theorem b55 : Encloses v55 ((1609437912433:ℝ)/1000000000000) ((402359478109:ℝ)/250000000000) := by
  unfold v55
  exact weaken (add b53 b54) (by norm_num) (by norm_num)

noncomputable def v56 : ℝ := Real.log ((5000000000007:ℝ)/1000000000000)
theorem b56 : Encloses v56 ((1609437912433:ℝ)/1000000000000) ((402359478109:ℝ)/250000000000) := by
  unfold v56
  have he : Real.log ((5000000000007:ℝ)/1000000000000) = Real.log ((5000000000007:ℝ)/4000000000000) + (2:ℝ)*Real.log 2 := by
    rw [show ((5000000000007:ℝ)/1000000000000) = ((5000000000007:ℝ)/4000000000000) * (2:ℝ)^(2:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b55

noncomputable def v57 : ℝ := Real.log v48
theorem b57 : Encloses v57 ((1609437912429:ℝ)/1000000000000) ((402359478109:ℝ)/250000000000) := by
  unfold v57
  exact IntervalBounds.log b48 (by norm_num) b52.1 b56.2

noncomputable def v58 : ℝ := v57/v11
theorem b58 : Encloses v58 ((402359478107:ℝ)/500000000000) ((402359478109:ℝ)/500000000000) := by
  unfold v58
  exact weaken (div_nonneg b57 b11 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v59 : ℝ := Real.artanh v9
theorem b59 : Encloses v59 ((402359478107:ℝ)/500000000000) ((402359478109:ℝ)/500000000000) := by
  unfold v59
  rw [Real.artanh_eq_half_log (by constructor <;> linarith [b9.1, b9.2])]
  convert b58 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58] <;> ring

noncomputable def v60 : ℝ := v59/v26
theorem b60 : Encloses v60 ((245207475539:ℝ)/500000000000) ((61301868887:ℝ)/125000000000) := by
  unfold v60
  exact weaken (div_nonneg b59 b26 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v61 : ℝ := v45-v60
theorem b61 : Encloses v61 ((842918382237:ℝ)/1000000000000) ((52682398891:ℝ)/62500000000) := by
  unfold v61
  exact weaken (sub b45 b60) (by norm_num) (by norm_num)

noncomputable def v62 : ℝ := v3/v18
theorem b62 : Encloses v62 ((63082648171:ℝ)/62500000000) ((1009322370743:ℝ)/1000000000000) := by
  unfold v62
  exact weaken (div_nonneg b3 b18 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v63 : ℝ := v3/v26
theorem b63 : Encloses v63 ((609423883073:ℝ)/1000000000000) ((152355970773:ℝ)/250000000000) := by
  unfold v63
  exact weaken (div_nonneg b3 b26 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v64 : ℝ := v62-v63
theorem b64 : Encloses v64 ((99974621911:ℝ)/250000000000) ((39989848767:ℝ)/100000000000) := by
  unfold v64
  exact weaken (sub b62 b63) (by norm_num) (by norm_num)

noncomputable def v65 : ℝ := v61-v44
theorem b65 : Encloses v65 ((470516724819:ℝ)/1000000000000) ((470516724843:ℝ)/1000000000000) := by
  unfold v65
  exact weaken (sub b61 b44) (by norm_num) (by norm_num)

noncomputable def v66 : ℝ := v64/v65
theorem b66 : Encloses v66 ((424956719421:ℝ)/500000000000) ((849913438941:ℝ)/1000000000000) := by
  unfold v66
  exact weaken (div_nonneg b64 b65 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v67 : ℝ := lowBeta
theorem b67 : Encloses v67 ((424956719421:ℝ)/500000000000) ((849913438941:ℝ)/1000000000000) := by
  unfold v67
  convert b66 using 1 <;> norm_num [lowBeta, TangentMinorant.A, TangentMinorant.z, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66]

noncomputable def v68 : ℝ := v3/v18
theorem b68 : Encloses v68 ((63082648171:ℝ)/62500000000) ((1009322370743:ℝ)/1000000000000) := by
  unfold v68
  exact weaken (div_nonneg b3 b18 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v69 : ℝ := v67*v44
theorem b69 : Encloses v69 ((158254586641:ℝ)/500000000000) ((79127293331:ℝ)/250000000000) := by
  unfold v69
  exact weaken (mul_nonneg b67 b44 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v70 : ℝ := v68+v69
theorem b70 : Encloses v70 ((662915772009:ℝ)/500000000000) ((1325831544067:ℝ)/1000000000000) := by
  unfold v70
  exact weaken (add b68 b69) (by norm_num) (by norm_num)

noncomputable def v71 : ℝ := lowAlpha
theorem b71 : Encloses v71 ((662915772009:ℝ)/500000000000) ((1325831544067:ℝ)/1000000000000) := by
  unfold v71
  convert b70 using 1 <;> norm_num [lowAlpha, TangentMinorant.A, TangentMinorant.z, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70]

noncomputable def v72 : ℝ := (5:ℝ)/8
theorem b72 : Encloses v72 ((5:ℝ)/8) ((5:ℝ)/8) := by
  unfold v72
  exact exact_value _

noncomputable def v73 : ℝ := (4:ℝ)/5
theorem b73 : Encloses v73 ((4:ℝ)/5) ((4:ℝ)/5) := by
  unfold v73
  exact exact_value _

noncomputable def v74 : ℝ := v3+v72
theorem b74 : Encloses v74 ((13:ℝ)/8) ((13:ℝ)/8) := by
  unfold v74
  exact weaken (add b3 b72) (by norm_num) (by norm_num)

noncomputable def v75 : ℝ := v3-v72
theorem b75 : Encloses v75 ((3:ℝ)/8) ((3:ℝ)/8) := by
  unfold v75
  exact weaken (sub b3 b72) (by norm_num) (by norm_num)

noncomputable def v76 : ℝ := v74/v75
theorem b76 : Encloses v76 ((4333333333333:ℝ)/1000000000000) ((2166666666667:ℝ)/500000000000) := by
  unfold v76
  exact weaken (div_nonneg b74 b75 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v77 : ℝ := Real.log ((4333333333333:ℝ)/4000000000000)
theorem b77 : Encloses v77 ((80042707673:ℝ)/1000000000000) ((40021353837:ℝ)/500000000000) := by
  unfold v77
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (333333333333:ℝ)/8333333333333) (by norm_num : (333333333333:ℝ)/8333333333333 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (333333333333:ℝ)/8333333333333) (by norm_num : (333333333333:ℝ)/8333333333333 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v78 : ℝ := v11*v32
theorem b78 : Encloses v78 ((693147180559:ℝ)/500000000000) ((8664339757:ℝ)/6250000000) := by
  unfold v78
  exact weaken (mul_nonneg b11 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v79 : ℝ := v77+v78
theorem b79 : Encloses v79 ((1466337068791:ℝ)/1000000000000) ((733168534397:ℝ)/500000000000) := by
  unfold v79
  exact weaken (add b77 b78) (by norm_num) (by norm_num)

noncomputable def v80 : ℝ := Real.log ((4333333333333:ℝ)/1000000000000)
theorem b80 : Encloses v80 ((1466337068791:ℝ)/1000000000000) ((733168534397:ℝ)/500000000000) := by
  unfold v80
  have he : Real.log ((4333333333333:ℝ)/1000000000000) = Real.log ((4333333333333:ℝ)/4000000000000) + (2:ℝ)*Real.log 2 := by
    rw [show ((4333333333333:ℝ)/1000000000000) = ((4333333333333:ℝ)/4000000000000) * (2:ℝ)^(2:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b79

noncomputable def v81 : ℝ := Real.log ((2166666666667:ℝ)/2000000000000)
theorem b81 : Encloses v81 ((80042707673:ℝ)/1000000000000) ((40021353837:ℝ)/500000000000) := by
  unfold v81
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (166666666667:ℝ)/4166666666667) (by norm_num : (166666666667:ℝ)/4166666666667 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (166666666667:ℝ)/4166666666667) (by norm_num : (166666666667:ℝ)/4166666666667 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v82 : ℝ := v11*v32
theorem b82 : Encloses v82 ((693147180559:ℝ)/500000000000) ((8664339757:ℝ)/6250000000) := by
  unfold v82
  exact weaken (mul_nonneg b11 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v83 : ℝ := v81+v82
theorem b83 : Encloses v83 ((1466337068791:ℝ)/1000000000000) ((733168534397:ℝ)/500000000000) := by
  unfold v83
  exact weaken (add b81 b82) (by norm_num) (by norm_num)

noncomputable def v84 : ℝ := Real.log ((2166666666667:ℝ)/500000000000)
theorem b84 : Encloses v84 ((1466337068791:ℝ)/1000000000000) ((733168534397:ℝ)/500000000000) := by
  unfold v84
  have he : Real.log ((2166666666667:ℝ)/500000000000) = Real.log ((2166666666667:ℝ)/2000000000000) + (2:ℝ)*Real.log 2 := by
    rw [show ((2166666666667:ℝ)/500000000000) = ((2166666666667:ℝ)/2000000000000) * (2:ℝ)^(2:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b83

noncomputable def v85 : ℝ := Real.log v76
theorem b85 : Encloses v85 ((1466337068791:ℝ)/1000000000000) ((733168534397:ℝ)/500000000000) := by
  unfold v85
  exact IntervalBounds.log b76 (by norm_num) b80.1 b84.2

noncomputable def v86 : ℝ := v85/v11
theorem b86 : Encloses v86 ((146633706879:ℝ)/200000000000) ((733168534397:ℝ)/1000000000000) := by
  unfold v86
  exact weaken (div_nonneg b85 b11 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v87 : ℝ := Real.artanh v72
theorem b87 : Encloses v87 ((146633706879:ℝ)/200000000000) ((733168534397:ℝ)/1000000000000) := by
  unfold v87
  rw [Real.artanh_eq_half_log (by constructor <;> linarith [b72.1, b72.2])]
  convert b86 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86] <;> ring

noncomputable def v88 : ℝ := v3+v72
theorem b88 : Encloses v88 ((13:ℝ)/8) ((13:ℝ)/8) := by
  unfold v88
  exact weaken (add b3 b72) (by norm_num) (by norm_num)

noncomputable def v89 : ℝ := Real.log ((13:ℝ)/8)
theorem b89 : Encloses v89 ((485507815781:ℝ)/1000000000000) ((242753907891:ℝ)/500000000000) := by
  unfold v89
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (5:ℝ)/21) (by norm_num : (5:ℝ)/21 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (5:ℝ)/21) (by norm_num : (5:ℝ)/21 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v90 : ℝ := Real.log v88
theorem b90 : Encloses v90 ((485507815781:ℝ)/1000000000000) ((242753907891:ℝ)/500000000000) := by
  unfold v90
  have he : v88 = ((13:ℝ)/8) := le_antisymm b88.2 b88.1
  rw [he]
  exact b89

noncomputable def v91 : ℝ := v32-v90
theorem b91 : Encloses v91 ((207639364777:ℝ)/1000000000000) ((207639364779:ℝ)/1000000000000) := by
  unfold v91
  exact weaken (sub b32 b90) (by norm_num) (by norm_num)

noncomputable def v92 : ℝ := v3-v72
theorem b92 : Encloses v92 ((3:ℝ)/8) ((3:ℝ)/8) := by
  unfold v92
  exact weaken (sub b3 b72) (by norm_num) (by norm_num)

noncomputable def v93 : ℝ := v92*v87
theorem b93 : Encloses v93 ((137469100199:ℝ)/500000000000) ((274938200399:ℝ)/1000000000000) := by
  unfold v93
  exact weaken (mul_nonneg b92 b87 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v94 : ℝ := v91+v93
theorem b94 : Encloses v94 ((19303102607:ℝ)/40000000000) ((241288782589:ℝ)/500000000000) := by
  unfold v94
  exact weaken (add b91 b93) (by norm_num) (by norm_num)

noncomputable def v95 : ℝ := h v72
theorem b95 : Encloses v95 ((19303102607:ℝ)/40000000000) ((241288782589:ℝ)/500000000000) := by
  unfold v95
  rw [h_log_formula (by linarith [b72.1]) (by linarith [b72.2])]
  convert b94 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94]

noncomputable def v96 : ℝ := v72^2
theorem b96 : Encloses v96 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v96
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v97 : ℝ := v67*v96
theorem b97 : Encloses v97 ((331997437047:ℝ)/1000000000000) ((331997437087:ℝ)/1000000000000) := by
  unfold v97
  exact weaken (mul_nonneg b67 b96 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v98 : ℝ := v71-v97
theorem b98 : Encloses v98 ((993834106931:ℝ)/1000000000000) ((49691705351:ℝ)/50000000000) := by
  unfold v98
  exact weaken (sub b71 b97) (by norm_num) (by norm_num)

noncomputable def v99 : ℝ := (147:ℝ)/32
theorem b99 : Encloses v99 ((147:ℝ)/32) ((147:ℝ)/32) := by
  unfold v99
  exact exact_value _

noncomputable def v100 : ℝ := v99*v72
theorem b100 : Encloses v100 ((735:ℝ)/256) ((735:ℝ)/256) := by
  unfold v100
  exact weaken (mul_nonneg b99 b72 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v101 : ℝ := (-113:ℝ)/32
theorem b101 : Encloses v101 ((-113:ℝ)/32) ((-113:ℝ)/32) := by
  unfold v101
  exact exact_value _

noncomputable def v102 : ℝ := v101+v100
theorem b102 : Encloses v102 ((-169:ℝ)/256) ((-169:ℝ)/256) := by
  unfold v102
  exact weaken (add b101 b100) (by norm_num) (by norm_num)

noncomputable def v103 : ℝ := v11*v67
theorem b103 : Encloses v103 ((424956719421:ℝ)/250000000000) ((849913438941:ℝ)/500000000000) := by
  unfold v103
  exact weaken (mul_nonneg b11 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v104 : ℝ := v103*v95
theorem b104 : Encloses v104 ((820298315851:ℝ)/1000000000000) ((820298315953:ℝ)/1000000000000) := by
  unfold v104
  exact weaken (mul_nonneg b103 b95 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v105 : ℝ := v102+v104
theorem b105 : Encloses v105 ((160142065851:ℝ)/1000000000000) ((160142065953:ℝ)/1000000000000) := by
  unfold v105
  exact weaken (add b102 b104) (by norm_num) (by norm_num)

noncomputable def v106 : ℝ := (4:ℝ)
theorem b106 : Encloses v106 ((4:ℝ)) ((4:ℝ)) := by
  unfold v106
  exact exact_value _

noncomputable def v107 : ℝ := v106*v67
theorem b107 : Encloses v107 ((424956719421:ℝ)/125000000000) ((849913438941:ℝ)/250000000000) := by
  unfold v107
  exact weaken (mul_nonneg b106 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v108 : ℝ := v107*v72
theorem b108 : Encloses v108 ((424956719421:ℝ)/200000000000) ((2124783597353:ℝ)/1000000000000) := by
  unfold v108
  exact weaken (mul_nonneg b107 b72 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v109 : ℝ := v108*v87
theorem b109 : Encloses v109 ((389456118949:ℝ)/250000000000) ((1557824475983:ℝ)/1000000000000) := by
  unfold v109
  exact weaken (mul_nonneg b108 b87 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v110 : ℝ := v105-v109
theorem b110 : Encloses v110 ((-349420602533:ℝ)/250000000000) ((-1397682409843:ℝ)/1000000000000) := by
  unfold v110
  exact weaken (sub b105 b109) (by norm_num) (by norm_num)

noncomputable def v111 : ℝ := v72^2
theorem b111 : Encloses v111 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v111
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v112 : ℝ := v3-v111
theorem b112 : Encloses v112 ((39:ℝ)/64) ((39:ℝ)/64) := by
  unfold v112
  exact weaken (sub b3 b111) (by norm_num) (by norm_num)

noncomputable def v113 : ℝ := v98/v112
theorem b113 : Encloses v113 ((1630907252399:ℝ)/1000000000000) ((815453626273:ℝ)/500000000000) := by
  unfold v113
  exact weaken (div_nonneg b98 b112 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v114 : ℝ := v110+v113
theorem b114 : Encloses v114 ((233224842267:ℝ)/1000000000000) ((233224842703:ℝ)/1000000000000) := by
  unfold v114
  exact weaken (add b110 b113) (by norm_num) (by norm_num)

theorem second_start : Encloses (lowGapSecond v72) ((233224842267:ℝ)/1000000000000) ((233224842703:ℝ)/1000000000000) := by
  convert b114 using 1 <;> norm_num [lowGapSecond, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114]

noncomputable def v115 : ℝ := -v101
theorem b115 : Encloses v115 ((113:ℝ)/32) ((113:ℝ)/32) := by
  unfold v115
  exact weaken (neg b101) (by norm_num) (by norm_num)

noncomputable def v116 : ℝ := v115*v72
theorem b116 : Encloses v116 ((565:ℝ)/256) ((565:ℝ)/256) := by
  unfold v116
  exact weaken (mul_nonneg b115 b72 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v117 : ℝ := -v116
theorem b117 : Encloses v117 ((-565:ℝ)/256) ((-565:ℝ)/256) := by
  unfold v117
  exact weaken (neg b116) (by norm_num) (by norm_num)

noncomputable def v118 : ℝ := v72^2
theorem b118 : Encloses v118 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v118
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v119 : ℝ := (147:ℝ)/64
theorem b119 : Encloses v119 ((147:ℝ)/64) ((147:ℝ)/64) := by
  unfold v119
  exact exact_value _

noncomputable def v120 : ℝ := v119*v118
theorem b120 : Encloses v120 ((3675:ℝ)/4096) ((3675:ℝ)/4096) := by
  unfold v120
  exact weaken (mul_nonneg b119 b118 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v121 : ℝ := v117+v120
theorem b121 : Encloses v121 ((-5365:ℝ)/4096) ((-5365:ℝ)/4096) := by
  unfold v121
  exact weaken (add b117 b120) (by norm_num) (by norm_num)

noncomputable def v122 : ℝ := v11*v67
theorem b122 : Encloses v122 ((424956719421:ℝ)/250000000000) ((849913438941:ℝ)/500000000000) := by
  unfold v122
  exact weaken (mul_nonneg b11 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v123 : ℝ := v122*v72
theorem b123 : Encloses v123 ((132798974819:ℝ)/125000000000) ((1062391798677:ℝ)/1000000000000) := by
  unfold v123
  exact weaken (mul_nonneg b122 b72 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v124 : ℝ := v123*v95
theorem b124 : Encloses v124 ((512686447407:ℝ)/1000000000000) ((512686447471:ℝ)/1000000000000) := by
  unfold v124
  exact weaken (mul_nonneg b123 b95 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v125 : ℝ := v121+v124
theorem b125 : Encloses v125 ((-398564002859:ℝ)/500000000000) ((-398564002827:ℝ)/500000000000) := by
  unfold v125
  exact weaken (add b121 b124) (by norm_num) (by norm_num)

noncomputable def v126 : ℝ := v98*v87
theorem b126 : Encloses v126 ((72864789561:ℝ)/100000000000) ((364323947839:ℝ)/500000000000) := by
  unfold v126
  exact weaken (mul_nonneg b98 b87 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v127 : ℝ := v125+v126
theorem b127 : Encloses v127 ((-17120027527:ℝ)/250000000000) ((-8560013747:ℝ)/125000000000) := by
  unfold v127
  exact weaken (add b125 b126) (by norm_num) (by norm_num)

noncomputable def v128 : ℝ := (6:ℝ)
theorem b128 : Encloses v128 ((6:ℝ)) ((6:ℝ)) := by
  unfold v128
  exact exact_value _

noncomputable def v129 : ℝ := v128*v67
theorem b129 : Encloses v129 ((1274870158263:ℝ)/250000000000) ((2549740316823:ℝ)/500000000000) := by
  unfold v129
  exact weaken (mul_nonneg b128 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v130 : ℝ := v129*v87
theorem b130 : Encloses v130 ((373877874191:ℝ)/100000000000) ((3738778742357:ℝ)/1000000000000) := by
  unfold v130
  exact weaken (mul_nonneg b129 b87 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v131 : ℝ := v99-v130
theorem b131 : Encloses v131 ((854971257643:ℝ)/1000000000000) ((85497125809:ℝ)/100000000000) := by
  unfold v131
  exact weaken (sub b99 b130) (by norm_num) (by norm_num)

noncomputable def v132 : ℝ := v128*v67
theorem b132 : Encloses v132 ((1274870158263:ℝ)/250000000000) ((2549740316823:ℝ)/500000000000) := by
  unfold v132
  exact weaken (mul_nonneg b128 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v133 : ℝ := v132*v72
theorem b133 : Encloses v133 ((3187175395657:ℝ)/1000000000000) ((3187175396029:ℝ)/1000000000000) := by
  unfold v133
  exact weaken (mul_nonneg b132 b72 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v134 : ℝ := v72^2
theorem b134 : Encloses v134 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v134
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v135 : ℝ := v3-v134
theorem b135 : Encloses v135 ((39:ℝ)/64) ((39:ℝ)/64) := by
  unfold v135
  exact weaken (sub b3 b134) (by norm_num) (by norm_num)

noncomputable def v136 : ℝ := v133/v135
theorem b136 : Encloses v136 ((5230236546719:ℝ)/1000000000000) ((523023654733:ℝ)/100000000000) := by
  unfold v136
  exact weaken (div_nonneg b133 b135 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v137 : ℝ := v131-v136
theorem b137 : Encloses v137 ((-4375265289687:ℝ)/1000000000000) ((-4375265288629:ℝ)/1000000000000) := by
  unfold v137
  exact weaken (sub b131 b136) (by norm_num) (by norm_num)

noncomputable def v138 : ℝ := v11*v72
theorem b138 : Encloses v138 ((5:ℝ)/4) ((5:ℝ)/4) := by
  unfold v138
  exact weaken (mul_nonneg b11 b72 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v139 : ℝ := v138*v98
theorem b139 : Encloses v139 ((1242292633663:ℝ)/1000000000000) ((49691705351:ℝ)/40000000000) := by
  unfold v139
  exact weaken (mul_nonneg b138 b98 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v140 : ℝ := v72^2
theorem b140 : Encloses v140 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v140
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v141 : ℝ := v3-v140
theorem b141 : Encloses v141 ((39:ℝ)/64) ((39:ℝ)/64) := by
  unfold v141
  exact weaken (sub b3 b140) (by norm_num) (by norm_num)

noncomputable def v142 : ℝ := v141^2
theorem b142 : Encloses v142 ((1521:ℝ)/4096) ((1521:ℝ)/4096) := by
  unfold v142
  exact weaken (pow_nonneg b141 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v143 : ℝ := v139/v142
theorem b143 : Encloses v143 ((66909015483:ℝ)/20000000000) ((3345450774453:ℝ)/1000000000000) := by
  unfold v143
  exact weaken (div_nonneg b139 b142 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v144 : ℝ := v137+v143
theorem b144 : Encloses v144 ((-1029814515537:ℝ)/1000000000000) ((-2011356473:ℝ)/1953125000) := by
  unfold v144
  exact weaken (add b137 b143) (by norm_num) (by norm_num)

noncomputable def v145 : ℝ := v3/v98
theorem b145 : Encloses v145 ((503102073543:ℝ)/500000000000) ((503102073589:ℝ)/500000000000) := by
  unfold v145
  exact weaken (div_nonneg b3 b98 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v146 : ℝ := v3-v72
theorem b146 : Encloses v146 ((3:ℝ)/8) ((3:ℝ)/8) := by
  unfold v146
  exact weaken (sub b3 b72) (by norm_num) (by norm_num)

noncomputable def v147 : ℝ := v145*v146
theorem b147 : Encloses v147 ((377326555157:ℝ)/1000000000000) ((47165819399:ℝ)/125000000000) := by
  unfold v147
  exact weaken (mul_nonneg b145 b146 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v148 : ℝ := v3+v72
theorem b148 : Encloses v148 ((13:ℝ)/8) ((13:ℝ)/8) := by
  unfold v148
  exact weaken (add b3 b72) (by norm_num) (by norm_num)

noncomputable def v149 : ℝ := v72^2
theorem b149 : Encloses v149 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v149
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v150 : ℝ := (49:ℝ)/64
theorem b150 : Encloses v150 ((49:ℝ)/64) ((49:ℝ)/64) := by
  unfold v150
  exact exact_value _

noncomputable def v151 : ℝ := v150*v149
theorem b151 : Encloses v151 ((1225:ℝ)/4096) ((1225:ℝ)/4096) := by
  unfold v151
  exact weaken (mul_nonneg b150 b149 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v152 : ℝ := v148-v151
theorem b152 : Encloses v152 ((5431:ℝ)/4096) ((5431:ℝ)/4096) := by
  unfold v152
  exact weaken (sub b148 b151) (by norm_num) (by norm_num)

noncomputable def v153 : ℝ := v147*v152
theorem b153 : Encloses v153 ((250153872199:ℝ)/500000000000) ((250153872223:ℝ)/500000000000) := by
  unfold v153
  exact weaken (mul_nonneg b147 b152 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v154 : ℝ := v72^2
theorem b154 : Encloses v154 ((25:ℝ)/64) ((25:ℝ)/64) := by
  unfold v154
  exact weaken (pow_nonneg b72 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v155 : ℝ := v154/v11
theorem b155 : Encloses v155 ((25:ℝ)/128) ((25:ℝ)/128) := by
  unfold v155
  exact weaken (div_nonneg b154 b11 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v156 : ℝ := v153+v155
theorem b156 : Encloses v156 ((347810122199:ℝ)/500000000000) ((347810122223:ℝ)/500000000000) := by
  unfold v156
  exact weaken (add b153 b155) (by norm_num) (by norm_num)

noncomputable def v157 : ℝ := v156-v32
theorem b157 : Encloses v157 ((1236531919:ℝ)/500000000000) ((2473063887:ℝ)/1000000000000) := by
  unfold v157
  exact weaken (sub b156 b32) (by norm_num) (by norm_num)

theorem first_start : Encloses (lowGapFirst v72) ((-17120027527:ℝ)/250000000000) ((-8560013747:ℝ)/125000000000) := by
  convert b127 using 1 <;> norm_num [lowGapFirst, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157]

theorem third_start : Encloses (lowGapThird v72) ((-1029814515537:ℝ)/1000000000000) ((-2011356473:ℝ)/1953125000) := by
  convert b144 using 1 <;> norm_num [lowGapThird, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157]

theorem slack_start : Encloses (lowCoefficient v72*(1-v72)*(1+v72-(49:ℝ)/64*v72^2)+v72^2/2-Real.log 2) ((1236531919:ℝ)/500000000000) ((2473063887:ℝ)/1000000000000) := by
  convert b157 using 1 <;> norm_num [lowCoefficient, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157]

noncomputable def v158 : ℝ := v3+v73
theorem b158 : Encloses v158 ((9:ℝ)/5) ((9:ℝ)/5) := by
  unfold v158
  exact weaken (add b3 b73) (by norm_num) (by norm_num)

noncomputable def v159 : ℝ := v3-v73
theorem b159 : Encloses v159 ((1:ℝ)/5) ((1:ℝ)/5) := by
  unfold v159
  exact weaken (sub b3 b73) (by norm_num) (by norm_num)

noncomputable def v160 : ℝ := v158/v159
theorem b160 : Encloses v160 ((9:ℝ)) ((9:ℝ)) := by
  unfold v160
  exact weaken (div_nonneg b158 b159 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v161 : ℝ := Real.log ((9:ℝ)/8)
theorem b161 : Encloses v161 ((14722879457:ℝ)/125000000000) ((117783035657:ℝ)/1000000000000) := by
  unfold v161
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (1:ℝ)/17) (by norm_num : (1:ℝ)/17 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (1:ℝ)/17) (by norm_num : (1:ℝ)/17 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v162 : ℝ := (3:ℝ)
theorem b162 : Encloses v162 ((3:ℝ)) ((3:ℝ)) := by
  unfold v162
  exact exact_value _

noncomputable def v163 : ℝ := v162*v32
theorem b163 : Encloses v163 ((2079441541677:ℝ)/1000000000000) ((25993019271:ℝ)/12500000000) := by
  unfold v163
  exact weaken (mul_nonneg b162 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v164 : ℝ := v161+v163
theorem b164 : Encloses v164 ((2197224577333:ℝ)/1000000000000) ((2197224577337:ℝ)/1000000000000) := by
  unfold v164
  exact weaken (add b161 b163) (by norm_num) (by norm_num)

noncomputable def v165 : ℝ := Real.log ((9:ℝ))
theorem b165 : Encloses v165 ((2197224577333:ℝ)/1000000000000) ((2197224577337:ℝ)/1000000000000) := by
  unfold v165
  have he : Real.log ((9:ℝ)) = Real.log ((9:ℝ)/8) + (3:ℝ)*Real.log 2 := by
    rw [show ((9:ℝ)) = ((9:ℝ)/8) * (2:ℝ)^(3:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b164

noncomputable def v166 : ℝ := Real.log v160
theorem b166 : Encloses v166 ((2197224577333:ℝ)/1000000000000) ((2197224577337:ℝ)/1000000000000) := by
  unfold v166
  have he : v160 = ((9:ℝ)) := le_antisymm b160.2 b160.1
  rw [he]
  exact b165

noncomputable def v167 : ℝ := v166/v11
theorem b167 : Encloses v167 ((549306144333:ℝ)/500000000000) ((1098612288669:ℝ)/1000000000000) := by
  unfold v167
  exact weaken (div_nonneg b166 b11 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v168 : ℝ := Real.artanh v73
theorem b168 : Encloses v168 ((549306144333:ℝ)/500000000000) ((1098612288669:ℝ)/1000000000000) := by
  unfold v168
  rw [Real.artanh_eq_half_log (by constructor <;> linarith [b73.1, b73.2])]
  convert b167 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167] <;> ring

noncomputable def v169 : ℝ := v3+v73
theorem b169 : Encloses v169 ((9:ℝ)/5) ((9:ℝ)/5) := by
  unfold v169
  exact weaken (add b3 b73) (by norm_num) (by norm_num)

noncomputable def v170 : ℝ := Real.log ((9:ℝ)/5)
theorem b170 : Encloses v170 ((293893332451:ℝ)/500000000000) ((587786664903:ℝ)/1000000000000) := by
  unfold v170
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (2:ℝ)/7) (by norm_num : (2:ℝ)/7 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (2:ℝ)/7) (by norm_num : (2:ℝ)/7 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v171 : ℝ := Real.log v169
theorem b171 : Encloses v171 ((293893332451:ℝ)/500000000000) ((587786664903:ℝ)/1000000000000) := by
  unfold v171
  have he : v169 = ((9:ℝ)/5) := le_antisymm b169.2 b169.1
  rw [he]
  exact b170

noncomputable def v172 : ℝ := v32-v171
theorem b172 : Encloses v172 ((13170064457:ℝ)/125000000000) ((52680257829:ℝ)/500000000000) := by
  unfold v172
  exact weaken (sub b32 b171) (by norm_num) (by norm_num)

noncomputable def v173 : ℝ := v3-v73
theorem b173 : Encloses v173 ((1:ℝ)/5) ((1:ℝ)/5) := by
  unfold v173
  exact weaken (sub b3 b73) (by norm_num) (by norm_num)

noncomputable def v174 : ℝ := v173*v168
theorem b174 : Encloses v174 ((219722457733:ℝ)/1000000000000) ((109861228867:ℝ)/500000000000) := by
  unfold v174
  exact weaken (mul_nonneg b173 b168 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v175 : ℝ := v172+v174
theorem b175 : Encloses v175 ((325082973389:ℝ)/1000000000000) ((20317685837:ℝ)/62500000000) := by
  unfold v175
  exact weaken (add b172 b174) (by norm_num) (by norm_num)

noncomputable def v176 : ℝ := h v73
theorem b176 : Encloses v176 ((325082973389:ℝ)/1000000000000) ((20317685837:ℝ)/62500000000) := by
  unfold v176
  rw [h_log_formula (by linarith [b73.1]) (by linarith [b73.2])]
  convert b175 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175]

noncomputable def v177 : ℝ := v73^2
theorem b177 : Encloses v177 ((16:ℝ)/25) ((16:ℝ)/25) := by
  unfold v177
  exact weaken (pow_nonneg b73 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v178 : ℝ := v67*v177
theorem b178 : Encloses v178 ((271972300429:ℝ)/500000000000) ((543944600923:ℝ)/1000000000000) := by
  unfold v178
  exact weaken (mul_nonneg b67 b177 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v179 : ℝ := v71-v178
theorem b179 : Encloses v179 ((156377388619:ℝ)/200000000000) ((781886943209:ℝ)/1000000000000) := by
  unfold v179
  exact weaken (sub b71 b178) (by norm_num) (by norm_num)

noncomputable def v180 : ℝ := v99*v73
theorem b180 : Encloses v180 ((147:ℝ)/40) ((147:ℝ)/40) := by
  unfold v180
  exact weaken (mul_nonneg b99 b73 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v181 : ℝ := v101+v180
theorem b181 : Encloses v181 ((23:ℝ)/160) ((23:ℝ)/160) := by
  unfold v181
  exact weaken (add b101 b180) (by norm_num) (by norm_num)

noncomputable def v182 : ℝ := v11*v67
theorem b182 : Encloses v182 ((424956719421:ℝ)/250000000000) ((849913438941:ℝ)/500000000000) := by
  unfold v182
  exact weaken (mul_nonneg b11 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v183 : ℝ := v182*v176
theorem b183 : Encloses v183 ((138146193911:ℝ)/250000000000) ((276292387857:ℝ)/500000000000) := by
  unfold v183
  exact weaken (mul_nonneg b182 b176 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v184 : ℝ := v181+v183
theorem b184 : Encloses v184 ((174083693911:ℝ)/250000000000) ((348167387857:ℝ)/500000000000) := by
  unfold v184
  exact weaken (add b181 b183) (by norm_num) (by norm_num)

noncomputable def v185 : ℝ := v106*v67
theorem b185 : Encloses v185 ((424956719421:ℝ)/125000000000) ((849913438941:ℝ)/250000000000) := by
  unfold v185
  exact weaken (mul_nonneg b106 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v186 : ℝ := v185*v73
theorem b186 : Encloses v186 ((1359861502147:ℝ)/500000000000) ((679930751153:ℝ)/250000000000) := by
  unfold v186
  exact weaken (mul_nonneg b185 b73 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v187 : ℝ := v186*v168
theorem b187 : Encloses v187 ((597584222857:ℝ)/200000000000) ((2987921114643:ℝ)/1000000000000) := by
  unfold v187
  exact weaken (mul_nonneg b186 b168 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v188 : ℝ := v184-v187
theorem b188 : Encloses v188 ((-2291586338999:ℝ)/1000000000000) ((-2291586338571:ℝ)/1000000000000) := by
  unfold v188
  exact weaken (sub b184 b187) (by norm_num) (by norm_num)

noncomputable def v189 : ℝ := v73^2
theorem b189 : Encloses v189 ((16:ℝ)/25) ((16:ℝ)/25) := by
  unfold v189
  exact weaken (pow_nonneg b73 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v190 : ℝ := v3-v189
theorem b190 : Encloses v190 ((9:ℝ)/25) ((9:ℝ)/25) := by
  unfold v190
  exact weaken (sub b3 b189) (by norm_num) (by norm_num)

noncomputable def v191 : ℝ := v179/v190
theorem b191 : Encloses v191 ((2171908175263:ℝ)/1000000000000) ((2171908175581:ℝ)/1000000000000) := by
  unfold v191
  exact weaken (div_nonneg b179 b190 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v192 : ℝ := v188+v191
theorem b192 : Encloses v192 ((-14959770467:ℝ)/125000000000) ((-11967816299:ℝ)/100000000000) := by
  unfold v192
  exact weaken (add b188 b191) (by norm_num) (by norm_num)

theorem second_join : Encloses (lowGapSecond v73) ((-14959770467:ℝ)/125000000000) ((-11967816299:ℝ)/100000000000) := by
  convert b192 using 1 <;> norm_num [lowGapSecond, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192]

noncomputable def v193 : ℝ := (31:ℝ)/20
theorem b193 : Encloses v193 ((31:ℝ)/20) ((31:ℝ)/20) := by
  unfold v193
  exact exact_value _

noncomputable def v194 : ℝ := Real.artanh v7
theorem b194 : Encloses v194 ((31:ℝ)/20) ((31:ℝ)/20) := by
  unfold v194
  simpa only [v7, v193, lowCutoff, Real.artanh_tanh] using b193

noncomputable def v195 : ℝ := v3+v7
theorem b195 : Encloses v195 ((478446372529:ℝ)/250000000000) ((47844637253:ℝ)/25000000000) := by
  unfold v195
  exact weaken (add b3 b7) (by norm_num) (by norm_num)

noncomputable def v196 : ℝ := Real.log ((478446372529:ℝ)/250000000000)
theorem b196 : Encloses v196 ((32454160631:ℝ)/50000000000) ((649083212621:ℝ)/1000000000000) := by
  unfold v196
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (228446372529:ℝ)/728446372529) (by norm_num : (228446372529:ℝ)/728446372529 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (228446372529:ℝ)/728446372529) (by norm_num : (228446372529:ℝ)/728446372529 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v197 : ℝ := Real.log ((47844637253:ℝ)/25000000000)
theorem b197 : Encloses v197 ((324541606311:ℝ)/500000000000) ((649083212623:ℝ)/1000000000000) := by
  unfold v197
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (22844637253:ℝ)/72844637253) (by norm_num : (22844637253:ℝ)/72844637253 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (22844637253:ℝ)/72844637253) (by norm_num : (22844637253:ℝ)/72844637253 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v198 : ℝ := Real.log v195
theorem b198 : Encloses v198 ((32454160631:ℝ)/50000000000) ((649083212623:ℝ)/1000000000000) := by
  unfold v198
  exact IntervalBounds.log b195 (by norm_num) b196.1 b197.2

noncomputable def v199 : ℝ := v32-v198
theorem b199 : Encloses v199 ((688499499:ℝ)/15625000000) ((2203198397:ℝ)/50000000000) := by
  unfold v199
  exact weaken (sub b32 b198) (by norm_num) (by norm_num)

noncomputable def v200 : ℝ := v3-v7
theorem b200 : Encloses v200 ((2155362747:ℝ)/25000000000) ((21553627471:ℝ)/250000000000) := by
  unfold v200
  exact weaken (sub b3 b7) (by norm_num) (by norm_num)

noncomputable def v201 : ℝ := v200*v194
theorem b201 : Encloses v201 ((66816245157:ℝ)/500000000000) ((133632490321:ℝ)/1000000000000) := by
  unfold v201
  exact weaken (mul_nonneg b200 b194 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v202 : ℝ := v199+v201
theorem b202 : Encloses v202 ((710785833:ℝ)/4000000000) ((177696458261:ℝ)/1000000000000) := by
  unfold v202
  exact weaken (add b199 b201) (by norm_num) (by norm_num)

noncomputable def v203 : ℝ := h v7
theorem b203 : Encloses v203 ((710785833:ℝ)/4000000000) ((177696458261:ℝ)/1000000000000) := by
  unfold v203
  rw [h_log_formula (by linarith [b7.1]) (by linarith [b7.2])]
  convert b202 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202]

noncomputable def v204 : ℝ := v7^2
theorem b204 : Encloses v204 ((417501960973:ℝ)/500000000000) ((417501960977:ℝ)/500000000000) := by
  unfold v204
  exact weaken (pow_nonneg b7 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v205 : ℝ := v67*v204
theorem b205 : Encloses v205 ((709681054747:ℝ)/1000000000000) ((354840527419:ℝ)/500000000000) := by
  unfold v205
  exact weaken (mul_nonneg b67 b204 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v206 : ℝ := v71-v205
theorem b206 : Encloses v206 ((30807524459:ℝ)/50000000000) ((15403762233:ℝ)/25000000000) := by
  unfold v206
  exact weaken (sub b71 b205) (by norm_num) (by norm_num)

noncomputable def v207 : ℝ := v99*v7
theorem b207 : Encloses v207 ((209885104761:ℝ)/50000000000) ((4197702095239:ℝ)/1000000000000) := by
  unfold v207
  exact weaken (mul_nonneg b99 b7 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v208 : ℝ := v101+v207
theorem b208 : Encloses v208 ((33322604761:ℝ)/50000000000) ((666452095239:ℝ)/1000000000000) := by
  unfold v208
  exact weaken (add b101 b207) (by norm_num) (by norm_num)

noncomputable def v209 : ℝ := v11*v67
theorem b209 : Encloses v209 ((424956719421:ℝ)/250000000000) ((849913438941:ℝ)/500000000000) := by
  unfold v209
  exact weaken (mul_nonneg b11 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v210 : ℝ := v209*v203
theorem b210 : Encloses v210 ((151026607901:ℝ)/500000000000) ((302053215857:ℝ)/1000000000000) := by
  unfold v210
  exact weaken (mul_nonneg b209 b203 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v211 : ℝ := v208+v210
theorem b211 : Encloses v211 ((484252655511:ℝ)/500000000000) ((121063163887:ℝ)/125000000000) := by
  unfold v211
  exact weaken (add b208 b210) (by norm_num) (by norm_num)

noncomputable def v212 : ℝ := v106*v67
theorem b212 : Encloses v212 ((424956719421:ℝ)/125000000000) ((849913438941:ℝ)/250000000000) := by
  unfold v212
  exact weaken (mul_nonneg b106 b67 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v213 : ℝ := v212*v7
theorem b213 : Encloses v213 ((3106554273073:ℝ)/1000000000000) ((62131085469:ℝ)/20000000000) := by
  unfold v213
  exact weaken (mul_nonneg b212 b7 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v214 : ℝ := v213*v194
theorem b214 : Encloses v214 ((4815159123263:ℝ)/1000000000000) ((601894890481:ℝ)/125000000000) := by
  unfold v214
  exact weaken (mul_nonneg b213 b194 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v215 : ℝ := v211-v214
theorem b215 : Encloses v215 ((-1923326906413:ℝ)/500000000000) ((-3846653812167:ℝ)/1000000000000) := by
  unfold v215
  exact weaken (sub b211 b214) (by norm_num) (by norm_num)

noncomputable def v216 : ℝ := v7^2
theorem b216 : Encloses v216 ((417501960973:ℝ)/500000000000) ((417501960977:ℝ)/500000000000) := by
  unfold v216
  exact weaken (pow_nonneg b7 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v217 : ℝ := v3-v216
theorem b217 : Encloses v217 ((82498039023:ℝ)/500000000000) ((82498039027:ℝ)/500000000000) := by
  unfold v217
  exact weaken (sub b3 b216) (by norm_num) (by norm_num)

noncomputable def v218 : ℝ := v206/v217
theorem b218 : Encloses v218 ((1867167075869:ℝ)/500000000000) ((3734334152769:ℝ)/1000000000000) := by
  unfold v218
  exact weaken (div_nonneg b206 b217 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v219 : ℝ := v215+v218
theorem b219 : Encloses v219 ((-3509989409:ℝ)/31250000000) ((-56159829699:ℝ)/500000000000) := by
  unfold v219
  exact weaken (add b215 b218) (by norm_num) (by norm_num)

theorem second_end : Encloses (lowGapSecond v7) ((-3509989409:ℝ)/31250000000) ((-56159829699:ℝ)/500000000000) := by
  convert b219 using 1 <;> norm_num [lowGapSecond, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219]

noncomputable def v220 : ℝ := v3-v7
theorem b220 : Encloses v220 ((2155362747:ℝ)/25000000000) ((21553627471:ℝ)/250000000000) := by
  unfold v220
  exact weaken (sub b3 b7) (by norm_num) (by norm_num)

noncomputable def v221 : ℝ := v3+v7
theorem b221 : Encloses v221 ((478446372529:ℝ)/250000000000) ((47844637253:ℝ)/25000000000) := by
  unfold v221
  exact weaken (add b3 b7) (by norm_num) (by norm_num)

noncomputable def v222 : ℝ := v7^2
theorem b222 : Encloses v222 ((417501960973:ℝ)/500000000000) ((417501960977:ℝ)/500000000000) := by
  unfold v222
  exact weaken (pow_nonneg b7 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v223 : ℝ := v150*v222
theorem b223 : Encloses v223 ((639299877739:ℝ)/1000000000000) ((639299877747:ℝ)/1000000000000) := by
  unfold v223
  exact weaken (mul_nonneg b150 b222 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v224 : ℝ := v221-v223
theorem b224 : Encloses v224 ((1274485612369:ℝ)/1000000000000) ((1274485612381:ℝ)/1000000000000) := by
  unfold v224
  exact weaken (sub b221 b223) (by norm_num) (by norm_num)

noncomputable def v225 : ℝ := v220*v224
theorem b225 : Encloses v225 ((109879152419:ℝ)/1000000000000) ((54939576213:ℝ)/500000000000) := by
  unfold v225
  exact weaken (mul_nonneg b220 b224 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v226 : ℝ := v206*v203
theorem b226 : Encloses v226 ((27371939919:ℝ)/250000000000) ((27371939927:ℝ)/250000000000) := by
  unfold v226
  exact weaken (mul_nonneg b206 b203 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v227 : ℝ := v225-v226
theorem b227 : Encloses v227 ((391392711:ℝ)/1000000000000) ((1565571:ℝ)/4000000000) := by
  unfold v227
  exact weaken (sub b225 b226) (by norm_num) (by norm_num)

theorem gap_end : Encloses (lowGap lowCutoff) ((391392711:ℝ)/1000000000000) ((1565571:ℝ)/4000000000) := by
  convert b227 using 1 <;> norm_num [lowGap, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227]

theorem z0_enclosure : Encloses (TangentMinorant.z (2/5)) ((372401657413:ℝ)/1000000000000) ((186200828709:ℝ)/500000000000) := by
  convert b44 using 1 <;> norm_num [TangentMinorant.z, TangentMinorant.A, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227]

noncomputable def v228 : ℝ := v7^2
theorem b228 : Encloses v228 ((417501960973:ℝ)/500000000000) ((417501960977:ℝ)/500000000000) := by
  unfold v228
  exact weaken (pow_nonneg b7 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v229 : ℝ := v61-v228
theorem b229 : Encloses v229 ((7914460283:ℝ)/1000000000000) ((791446031:ℝ)/100000000000) := by
  unfold v229
  exact weaken (sub b61 b228) (by norm_num) (by norm_num)

theorem z1_slack : Encloses (TangentMinorant.z (2/3)-lowCutoff^2) ((7914460283:ℝ)/1000000000000) ((791446031:ℝ)/100000000000) := by
  convert b229 using 1 <;> norm_num [TangentMinorant.z, TangentMinorant.A, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229]

noncomputable def v230 : ℝ := v7^2
theorem b230 : Encloses v230 ((417501960973:ℝ)/500000000000) ((417501960977:ℝ)/500000000000) := by
  unfold v230
  exact weaken (pow_nonneg b7 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v231 : ℝ := v3-v230
theorem b231 : Encloses v231 ((82498039023:ℝ)/500000000000) ((82498039027:ℝ)/500000000000) := by
  unfold v231
  exact weaken (sub b3 b230) (by norm_num) (by norm_num)

noncomputable def v232 : ℝ := v72*v7
theorem b232 : Encloses v232 ((285557965661:ℝ)/500000000000) ((22844637253:ℝ)/40000000000) := by
  unfold v232
  exact weaken (mul_nonneg b72 b7 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v233 : ℝ := v3+v232
theorem b233 : Encloses v233 ((785557965661:ℝ)/500000000000) ((62844637253:ℝ)/40000000000) := by
  unfold v233
  exact weaken (add b3 b232) (by norm_num) (by norm_num)

noncomputable def v234 : ℝ := v3-v232
theorem b234 : Encloses v234 ((17155362747:ℝ)/40000000000) ((214442034339:ℝ)/500000000000) := by
  unfold v234
  exact weaken (sub b3 b232) (by norm_num) (by norm_num)

noncomputable def v235 : ℝ := v233/v234
theorem b235 : Encloses v235 ((3663264844891:ℝ)/1000000000000) ((915816211231:ℝ)/250000000000) := by
  unfold v235
  exact weaken (div_nonneg b233 b234 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v236 : ℝ := Real.log ((3663264844891:ℝ)/2000000000000)
theorem b236 : Encloses v236 ((12104152067:ℝ)/20000000000) ((605207603351:ℝ)/1000000000000) := by
  unfold v236
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (1663264844891:ℝ)/5663264844891) (by norm_num : (1663264844891:ℝ)/5663264844891 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (1663264844891:ℝ)/5663264844891) (by norm_num : (1663264844891:ℝ)/5663264844891 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v237 : ℝ := v3*v32
theorem b237 : Encloses v237 ((693147180559:ℝ)/1000000000000) ((8664339757:ℝ)/12500000000) := by
  unfold v237
  exact weaken (mul_nonneg b3 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v238 : ℝ := v236+v237
theorem b238 : Encloses v238 ((1298354783909:ℝ)/1000000000000) ((1298354783911:ℝ)/1000000000000) := by
  unfold v238
  exact weaken (add b236 b237) (by norm_num) (by norm_num)

noncomputable def v239 : ℝ := Real.log ((3663264844891:ℝ)/1000000000000)
theorem b239 : Encloses v239 ((1298354783909:ℝ)/1000000000000) ((1298354783911:ℝ)/1000000000000) := by
  unfold v239
  have he : Real.log ((3663264844891:ℝ)/1000000000000) = Real.log ((3663264844891:ℝ)/2000000000000) + (1:ℝ)*Real.log 2 := by
    rw [show ((3663264844891:ℝ)/1000000000000) = ((3663264844891:ℝ)/2000000000000) * (2:ℝ)^(1:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b238

noncomputable def v240 : ℝ := Real.log ((915816211231:ℝ)/500000000000)
theorem b240 : Encloses v240 ((605207603359:ℝ)/1000000000000) ((3782547521:ℝ)/6250000000) := by
  unfold v240
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (415816211231:ℝ)/1415816211231) (by norm_num : (415816211231:ℝ)/1415816211231 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (415816211231:ℝ)/1415816211231) (by norm_num : (415816211231:ℝ)/1415816211231 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v241 : ℝ := v3*v32
theorem b241 : Encloses v241 ((693147180559:ℝ)/1000000000000) ((8664339757:ℝ)/12500000000) := by
  unfold v241
  exact weaken (mul_nonneg b3 b32 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v242 : ℝ := v240+v241
theorem b242 : Encloses v242 ((649177391959:ℝ)/500000000000) ((16229434799:ℝ)/12500000000) := by
  unfold v242
  exact weaken (add b240 b241) (by norm_num) (by norm_num)

noncomputable def v243 : ℝ := Real.log ((915816211231:ℝ)/250000000000)
theorem b243 : Encloses v243 ((649177391959:ℝ)/500000000000) ((16229434799:ℝ)/12500000000) := by
  unfold v243
  have he : Real.log ((915816211231:ℝ)/250000000000) = Real.log ((915816211231:ℝ)/500000000000) + (1:ℝ)*Real.log 2 := by
    rw [show ((915816211231:ℝ)/250000000000) = ((915816211231:ℝ)/500000000000) * (2:ℝ)^(1:ℤ) by norm_num, Real.log_mul (by norm_num) (by positivity), Real.log_zpow]
    norm_num
  rw [he]
  exact b242

noncomputable def v244 : ℝ := Real.log v235
theorem b244 : Encloses v244 ((1298354783909:ℝ)/1000000000000) ((16229434799:ℝ)/12500000000) := by
  unfold v244
  exact IntervalBounds.log b235 (by norm_num) b239.1 b243.2

noncomputable def v245 : ℝ := v244/v11
theorem b245 : Encloses v245 ((324588695977:ℝ)/500000000000) ((16229434799:ℝ)/25000000000) := by
  unfold v245
  exact weaken (div_nonneg b244 b11 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v246 : ℝ := Real.artanh v232
theorem b246 : Encloses v246 ((324588695977:ℝ)/500000000000) ((16229434799:ℝ)/25000000000) := by
  unfold v246
  rw [Real.artanh_eq_half_log (by constructor <;> linarith [b232.1, b232.2])]
  convert b245 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, v240, v241, v242, v243, v244, v245] <;> ring

noncomputable def v247 : ℝ := v3+v232
theorem b247 : Encloses v247 ((785557965661:ℝ)/500000000000) ((62844637253:ℝ)/40000000000) := by
  unfold v247
  exact weaken (add b3 b232) (by norm_num) (by norm_num)

noncomputable def v248 : ℝ := Real.log ((785557965661:ℝ)/500000000000)
theorem b248 : Encloses v248 ((225893075577:ℝ)/500000000000) ((90357230231:ℝ)/200000000000) := by
  unfold v248
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (285557965661:ℝ)/1285557965661) (by norm_num : (285557965661:ℝ)/1285557965661 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (285557965661:ℝ)/1285557965661) (by norm_num : (285557965661:ℝ)/1285557965661 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v249 : ℝ := Real.log ((62844637253:ℝ)/40000000000)
theorem b249 : Encloses v249 ((112946537789:ℝ)/250000000000) ((451786151157:ℝ)/1000000000000) := by
  unfold v249
  have hl := Real.sum_range_le_log_div (by norm_num : 0 ≤ (22844637253:ℝ)/102844637253) (by norm_num : (22844637253:ℝ)/102844637253 < 1) 16
  have hu := Real.log_div_le_sum_range_add (by norm_num : 0 ≤ (22844637253:ℝ)/102844637253) (by norm_num : (22844637253:ℝ)/102844637253 < 1) 16
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

noncomputable def v250 : ℝ := Real.log v247
theorem b250 : Encloses v250 ((225893075577:ℝ)/500000000000) ((451786151157:ℝ)/1000000000000) := by
  unfold v250
  exact IntervalBounds.log b247 (by norm_num) b248.1 b249.2

noncomputable def v251 : ℝ := v32-v250
theorem b251 : Encloses v251 ((120680514701:ℝ)/500000000000) ((120680514703:ℝ)/500000000000) := by
  unfold v251
  exact weaken (sub b32 b250) (by norm_num) (by norm_num)

noncomputable def v252 : ℝ := v3-v232
theorem b252 : Encloses v252 ((17155362747:ℝ)/40000000000) ((214442034339:ℝ)/500000000000) := by
  unfold v252
  exact weaken (sub b3 b232) (by norm_num) (by norm_num)

noncomputable def v253 : ℝ := v252*v246
theorem b253 : Encloses v253 ((278421841153:ℝ)/1000000000000) ((139210920579:ℝ)/500000000000) := by
  unfold v253
  exact weaken (mul_nonneg b252 b246 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v254 : ℝ := v251+v253
theorem b254 : Encloses v254 ((103956574111:ℝ)/200000000000) ((129945717641:ℝ)/250000000000) := by
  unfold v254
  exact weaken (add b251 b253) (by norm_num) (by norm_num)

noncomputable def v255 : ℝ := h v232
theorem b255 : Encloses v255 ((103956574111:ℝ)/200000000000) ((129945717641:ℝ)/250000000000) := by
  unfold v255
  rw [h_log_formula (by linarith [b232.1]) (by linarith [b232.2])]
  convert b254 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, v240, v241, v242, v243, v244, v245, v246, v247, v248, v249, v250, v251, v252, v253, v254]

noncomputable def v256 : ℝ := v231*v255
theorem b256 : Encloses v256 ((85762135077:ℝ)/1000000000000) ((85762135083:ℝ)/1000000000000) := by
  unfold v256
  exact weaken (mul_nonneg b231 b255 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v257 : ℝ := v7^2
theorem b257 : Encloses v257 ((417501960973:ℝ)/500000000000) ((417501960977:ℝ)/500000000000) := by
  unfold v257
  exact weaken (pow_nonneg b7 (by norm_num) 2) (by norm_num) (by norm_num)

noncomputable def v258 : ℝ := v72*v257
theorem b258 : Encloses v258 ((32617340701:ℝ)/62500000000) ((260938725611:ℝ)/500000000000) := by
  unfold v258
  exact weaken (mul_nonneg b72 b257 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v259 : ℝ := v3-v258
theorem b259 : Encloses v259 ((239061274389:ℝ)/500000000000) ((29882659299:ℝ)/62500000000) := by
  unfold v259
  exact weaken (sub b3 b258) (by norm_num) (by norm_num)

noncomputable def v260 : ℝ := Real.artanh v7
theorem b260 : Encloses v260 ((31:ℝ)/20) ((31:ℝ)/20) := by
  unfold v260
  simpa only [v7, v193, lowCutoff, Real.artanh_tanh] using b193

noncomputable def v261 : ℝ := v3+v7
theorem b261 : Encloses v261 ((478446372529:ℝ)/250000000000) ((47844637253:ℝ)/25000000000) := by
  unfold v261
  exact weaken (add b3 b7) (by norm_num) (by norm_num)

noncomputable def v262 : ℝ := Real.log v261
theorem b262 : Encloses v262 ((32454160631:ℝ)/50000000000) ((649083212623:ℝ)/1000000000000) := by
  unfold v262
  exact IntervalBounds.log b261 (by norm_num) b196.1 b197.2

noncomputable def v263 : ℝ := v32-v262
theorem b263 : Encloses v263 ((688499499:ℝ)/15625000000) ((2203198397:ℝ)/50000000000) := by
  unfold v263
  exact weaken (sub b32 b262) (by norm_num) (by norm_num)

noncomputable def v264 : ℝ := v3-v7
theorem b264 : Encloses v264 ((2155362747:ℝ)/25000000000) ((21553627471:ℝ)/250000000000) := by
  unfold v264
  exact weaken (sub b3 b7) (by norm_num) (by norm_num)

noncomputable def v265 : ℝ := v264*v260
theorem b265 : Encloses v265 ((66816245157:ℝ)/500000000000) ((133632490321:ℝ)/1000000000000) := by
  unfold v265
  exact weaken (mul_nonneg b264 b260 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v266 : ℝ := v263+v265
theorem b266 : Encloses v266 ((710785833:ℝ)/4000000000) ((177696458261:ℝ)/1000000000000) := by
  unfold v266
  exact weaken (add b263 b265) (by norm_num) (by norm_num)

noncomputable def v267 : ℝ := h v7
theorem b267 : Encloses v267 ((710785833:ℝ)/4000000000) ((177696458261:ℝ)/1000000000000) := by
  unfold v267
  rw [h_log_formula (by linarith [b7.1]) (by linarith [b7.2])]
  convert b266 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, v240, v241, v242, v243, v244, v245, v246, v247, v248, v249, v250, v251, v252, v253, v254, v255, v256, v257, v258, v259, v260, v261, v262, v263, v264, v265, v266]

noncomputable def v268 : ℝ := v259*v267
theorem b268 : Encloses v268 ((84960683527:ℝ)/1000000000000) ((42480341767:ℝ)/500000000000) := by
  unfold v268
  exact weaken (mul_nonneg b259 b267 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

noncomputable def v269 : ℝ := v256-v268
theorem b269 : Encloses v269 ((801451543:ℝ)/1000000000000) ((200362889:ℝ)/250000000000) := by
  unfold v269
  exact weaken (sub b256 b268) (by norm_num) (by norm_num)

theorem local_margin_enclosure : Encloses ((1-lowCutoff^2)*h ((5:ℝ)/8*lowCutoff)-(1-(5:ℝ)/8*lowCutoff^2)*h lowCutoff) ((801451543:ℝ)/1000000000000) ((200362889:ℝ)/250000000000) := by
  convert b269 using 1 <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, v240, v241, v242, v243, v244, v245, v246, v247, v248, v249, v250, v251, v252, v253, v254, v255, v256, v257, v258, v259, v260, v261, v262, v263, v264, v265, v266, v267, v268, v269]

end LowCertificates

open LowCertificates in
theorem low_fixed_facts : LowFixedFacts := by
  have h_second_start := second_start
  have h_first := first_start
  have h_third := third_start
  have h_slack := slack_start
  have h_second_join := second_join
  have h_second_end := second_end
  have h_gap := gap_end
  have ha := b71
  have hb := b67
  have hr := b7
  norm_num only [v7, v71, v67, v72, v73] at *
  constructor <;> unfold IntervalBounds.Encloses at * <;> linarith

theorem low_z0_lt_start_sq : TangentMinorant.z (2/5) < ((5:ℝ)/8)^2 := by
  have h := LowCertificates.z0_enclosure.2
  norm_num at *
  linarith

theorem low_end_sq_lt_z1 : lowCutoff^2 < TangentMinorant.z (2/3) := by
  have h := LowCertificates.z1_slack.1
  norm_num at *
  linarith

theorem low_local_margin : (1:ℝ)/1400 <
    (1-lowCutoff^2)*h ((5:ℝ)/8*lowCutoff)-(1-(5:ℝ)/8*lowCutoff^2)*h lowCutoff := by
  have h := LowCertificates.local_margin_enclosure.1
  norm_num at *
  linarith

end MostInformativeBit
