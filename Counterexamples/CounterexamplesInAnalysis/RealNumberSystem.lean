import Mathlib

open Complex

section ComplexNotOrdered
variable [LinearOrder ℂ] [IsStrictOrderedRing ℂ]

theorem complex_field_not_ordered : False := by
  obtain h1 | h2 | h3 := lt_trichotomy I 0
  · have pos_neg_I := neg_pos.mpr h1
    have hi2 : 0 < (-I)^2  := sq_pos_of_pos pos_neg_I
    have hi4 : 0 < (-I)^4 := pow_pos pos_neg_I 4
    have eq : (-I)^2 + (-I)^4 = 0 := by
      field_simp
      refine neg_add_eq_zero.mpr ?_
      rw [@neg_pow']
      field_simp
      ring
    have falso : (0 : ℂ) < 0 := by
      nth_rw 2 [← eq]
      have := add_lt_add hi2 hi4
      rwa [zero_add] at this
    exact (lt_self_iff_false 0).mp falso
  · exact I_ne_zero h2
  · have hi2 : 0 < I^2  := sq_pos_of_pos h3
    have hi4 : 0 < I^4 := pow_pos h3 4
    have eq : I^2 + I^4 = 0 := by
      field_simp
    have falso : (0 : ℂ) < 0 := by
      nth_rw 2 [← eq]
      have := add_lt_add hi2 hi4
      rwa [zero_add] at this
    exact (lt_self_iff_false 0).mp falso

end ComplexNotOrdered

section TwoDistinctOrdersOnAField

def QSqrt2 := {r : ℝ | ∃ a b : ℚ, r = a + b *√2}

theorem qsrt2_unique_pair {a b c d : ℚ} : a + b *√2 = c + d*√2 → a = c ∧ b = d := by
  intro h
  have h_rearranged : (a - c) + (b - d) * √2 = 0 := by
    rw [@sub_add_eq_add_sub, sub_eq_zero, sub_mul, add_sub, sub_eq_iff_eq_add]
    exact h
  by_cases hbd : b = d
  · constructor
    · simp only [hbd, add_left_inj, Rat.cast_inj] at h
      exact h
    · exact hbd
  · have hbd_ne_zero : b - d ≠ 0 := by
      exact sub_ne_zero_of_ne hbd
    have sqrt2_rational : √2 = -↑(a - c) / ↑(b - d) := by
      have : (b - d) * √2 = -(a - c) := by
        ring_nf
        linarith
      refine CancelDenoms.cancel_factors_eq_div ?_ ?_
      simp only [← Rat.cast_sub] at this
      exact this
      exact Rat.cast_ne_zero.mpr hbd_ne_zero
    have sqrt2_in_range : √2 ∈ Set.range ((↑) : ℚ → ℝ) := by
      use (-((a - c) / (b - d)))
      rw [sqrt2_rational, Rat.cast_neg, Rat.cast_div, neg_div']
    exact absurd sqrt2_in_range irrational_sqrt_two

noncomputable abbrev QSqrt2_sub_field : Subfield ℝ where
  carrier := QSqrt2
  mul_mem' := by
    rintro r s ⟨a,b,hr⟩ ⟨c,d,hs⟩
    use (a*c + 2*b*d), (a*d + b*c)
    rw [hr, hs]
    ring_nf
    simp only [Nat.ofNat_nonneg, Real.sq_sqrt,
      Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    ring_nf
  one_mem' := by
    use 1,0; ring_nf
  add_mem' := by
    rintro r s ⟨a,b,hr⟩ ⟨c,d,hs⟩
    use a+c, b+d
    simp only [hr, hs, Rat.cast_add]
    ring_nf
  zero_mem' := by
    use 0,0; ring_nf
  neg_mem' := by
    rintro r ⟨a,b,hr⟩
    use -a,-b
    simp only [hr, Rat.cast_neg, mul_neg]
    ring_nf
  inv_mem' := by
    rintro r ⟨a,b,hr⟩
    by_cases hb : b = 0
    · use (1/a), 0
      rw [hr, hb]
      field_simp
    · use (a/(a^2 - 2*b^2)), (-b/(a^2 - 2*b^2))
      rw [hr]
      field_simp
      have eq : (√2)^2 = 2 := by field_simp
      nth_rw 4 [← eq]
      rw [← mul_pow, pow_two_sub_pow_two]
      rw [← sub_eq_add_neg, mul_comm √2]
      refine Eq.symm (IsUnit.div_mul_left ?_)
      refine Ne.isUnit ?_
      intro h
      rw [sub_eq_zero] at h
      have sqrt2_rational : √2 ∈ Set.range ((↑) : ℚ → ℝ) := by
        use (a/b)
        rw [@Rat.cast_div,h]
        field_simp
      exact irrational_sqrt_two sqrt2_rational

noncomputable def QSqrt2_field : Field QSqrt2 := Subfield.toField QSqrt2_sub_field

noncomputable instance : Field QSqrt2 := QSqrt2_field

noncomputable instance QSqrt2_order1 : LinearOrder QSqrt2 := by
  exact Subtype.instLinearOrder fun x ↦ x ∈ QSqrt2

noncomputable instance QSqrt2_order2 : LinearOrder QSqrt2 where
  le := by
    intro ⟨r, hr⟩ ⟨s,hs⟩
    set a := hr.choose with ha
    set b:= hr.choose_spec.choose with hb
    set c := hs.choose with hc
    set d := hs.choose_spec.choose with hd
    exact a + d*√2 ≤ c + b*√2
  lt := by
    intro ⟨r, hr⟩ ⟨s,hs⟩
    set a := hr.choose with ha
    set b:= hr.choose_spec.choose with hb
    set c := hs.choose with hc
    set d := hs.choose_spec.choose with hd
    exact a + d*√2 < c + b*√2
  le_refl := by
    intro ⟨r,hr⟩
    exact Preorder.le_refl (↑(Exists.choose hr) + ↑(Exists.choose_spec hr).choose * √2)
  le_trans := by
    intro ⟨r, hr⟩ ⟨s,hs⟩ ⟨t,ht⟩
    set a := hr.choose with ha
    set b:= hr.choose_spec.choose with hb
    set c := hs.choose with hc
    set d := hs.choose_spec.choose with hd
    set e := ht.choose with he
    set f := ht.choose_spec.choose with hf
    intro hrs hst
    simp only [← ha, ← hc, ← hd, ← hb, Subtype.mk_le_mk, ← he, ← hf] at hrs hst ⊢
    linarith
  lt_iff_le_not_ge := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    set a := hr.choose with ha
    set b:= hr.choose_spec.choose with hb
    set c := hs.choose with hc
    set d := hs.choose_spec.choose with hd
    simp only [← ha, ← hc, ← hd, ← hb, Subtype.mk_le_mk]
    exact lt_iff_le_not_ge
  le_antisymm := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    set a := hr.choose with ha
    set b:= hr.choose_spec.choose with hb
    have hab := hr.choose_spec.choose_spec
    simp only [← ha, ← hb] at hab
    set c := hs.choose with hc
    set d := hs.choose_spec.choose with hd
    have hcd := hs.choose_spec.choose_spec
    simp only [← hc, ← hd] at hcd
    intro hrs hsr
    simp only [Subtype.mk.injEq] at hrs hsr ⊢
    simp only [← ha, ← hc, ← hd, ← hb] at hrs hsr
    have ad_cb:= le_antisymm hrs hsr
    rw [hab,hcd]
    have := qsrt2_unique_pair ad_cb
    rw [this.1, this.2]
  le_total := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    set a := hr.choose with ha
    set b := hr.choose_spec.choose with hb
    set c := hs.choose with hc
    set d := hs.choose_spec.choose with hd
    simp only [← ha, ← hc, ← hd, ← hb]
    exact LinearOrder.le_total (↑a + ↑d * √2) (↑c + ↑b * √2)
  toDecidableLE := by
    apply Classical.decRel
  min := fun ⟨r, hr⟩ ⟨s, hs⟩ =>
    let a := hr.choose
    let b := hr.choose_spec.choose
    let c := hs.choose
    let d := hs.choose_spec.choose
    if a + d * √2 ≤ c + b * √2 then ⟨r, hr⟩ else ⟨s, hs⟩
  max := fun ⟨r, hr⟩ ⟨s, hs⟩ =>
    let a := hr.choose
    let b := hr.choose_spec.choose
    let c := hs.choose
    let d := hs.choose_spec.choose
    if a + d * √2 ≤ c + b * √2 then ⟨s, hs⟩ else ⟨r, hr⟩
  compare := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    by_cases h : hr.choose + hs.choose_spec.choose * √2 <
       hs.choose + hr.choose_spec.choose * √2
    · exact Ordering.lt
    · by_cases h' : hs.choose + hr.choose_spec.choose  * √2 =
         hr.choose + hs.choose_spec.choose * √2
      · exact Ordering.eq
      · exact Ordering.gt
  toDecidableEq := by
    apply Classical.decEq
  toDecidableLT := by
    apply Classical.decRel
  min_def := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    simp only
  max_def := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    simp only
  compare_eq_compareOfLessAndEq := by
    intro ⟨r, hr⟩ ⟨s, hs⟩
    by_cases h : hr.choose + hs.choose_spec.choose * √2 < hs.choose + hr.choose_spec.choose * √2
    · rw [compareOfLessAndEq]
      simp only [h]
      simp only [↓reduceDIte, ↓reduceIte]
    · by_cases h' : hs.choose + hr.choose_spec.choose * √2 = hr.choose + hs.choose_spec.choose * √2
      · rw [compareOfLessAndEq]
        simp only [h,h']
        simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Subtype.mk.injEq, left_eq_ite_iff,
          reduceCtorEq, imp_false, Decidable.not_not]
        have := qsrt2_unique_pair h'
        have hr_def := hr.choose_spec.choose_spec
        have hs_def := hs.choose_spec.choose_spec
        rw [hr_def, hs_def]
        congr 1
        · simp only [this.1]
        · congr 1
          simp only [this.2]
      · rw [compareOfLessAndEq]
        simp only [h, h']
        simp only [↓reduceDIte, ↓reduceIte, Subtype.mk.injEq, right_eq_ite_iff, reduceCtorEq,
          imp_false, ne_eq]
        intro hrs
        rw [hr.choose_spec.choose_spec, hs.choose_spec.choose_spec] at hrs
        have coeff_eq := qsrt2_unique_pair hrs
        apply h'
        congr 1
        · simp only [coeff_eq.1.symm]
        · congr 1
          simp only [coeff_eq.2.symm]

noncomputable def zero_QSqrt2 : QSqrt2 := ⟨0, 0, 0, by ring⟩
noncomputable def sqrt2_QSqrt2 : QSqrt2 := ⟨√2, 0, 1, by ring⟩

theorem order1_le_comparison :
  @LE.le QSqrt2 QSqrt2_order1.toLE zero_QSqrt2 sqrt2_QSqrt2 := by
  simp only [zero_QSqrt2, sqrt2_QSqrt2, QSqrt2_order1]
  exact le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

theorem order2_le_comparison :
  ¬(@LE.le QSqrt2 QSqrt2_order2.toLE zero_QSqrt2 sqrt2_QSqrt2) := by
  simp only [zero_QSqrt2, sqrt2_QSqrt2, QSqrt2_order2]
  intro ineq
  have zero_mem : (0 : ℝ) ∈ QSqrt2 := ⟨0, 0, by ring⟩
  have sqrt2_mem : √2 ∈ QSqrt2 := ⟨0, 1, by ring⟩
  have zero_eq1 : 0 + 0 * √2 = (0 : ℝ) := by ring
  have sqrt2_eq1 : 0 + 1 * √2 = √2 := by ring
  have zero_eq2 := zero_mem.choose_spec.choose_spec
  have sqrt2_eq2 := sqrt2_mem.choose_spec.choose_spec
  have zero_coeffs_eq : ↑(0 : ℚ) + ↑(0 : ℚ) * √2 =
    ↑(Exists.choose zero_mem) + ↑(Exists.choose_spec zero_mem).choose * √2 := by
    simp only [Rat.cast_zero, zero_eq1]
    exact zero_eq2
  have sqrt2_coeffs_eq : ↑(0 : ℚ) + ↑(1 : ℚ) * √2 =
    ↑(Exists.choose sqrt2_mem) + ↑(Exists.choose_spec sqrt2_mem).choose * √2 := by
    simp only [Rat.cast_zero, Rat.cast_one, sqrt2_eq1]
    exact sqrt2_eq2
  have zero_unique := qsrt2_unique_pair zero_coeffs_eq
  have sqrt2_unique := qsrt2_unique_pair sqrt2_coeffs_eq
  conv at ineq =>
    lhs
    simp [← zero_unique.1, ← sqrt2_unique.2]
  conv at ineq =>
    rhs
    simp [← sqrt2_unique.1, ← zero_unique.2]
  have sqrt2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  exact not_le_of_gt sqrt2_pos ineq

end TwoDistinctOrdersOnAField
