import Mathlib

/-!
# A Conditional Irrationality Criterion for ∑ φ(n)/2^n

This file formalizes the paper "A Conditional Irrationality Criterion for ∑ φ(n)/2^n"
by Wilkie Hoare (March 2026).

The main result (Theorem 1.1) states that if a certain combinatorial criterion is satisfied
for every positive integer t, then S = ∑_{n≥1} φ(n)/2^n is irrational.

## Main Results

* `prop_2_1` : If S = A/(2^r · b) with b | (2^t - 1), then I_{N,t} ∈ ℤ for N ≥ r.
* `tail_bound` : The tail after J terms is bounded by (2N + t + 2J + 4)/2^J.
* `thm_2_3` : The main criterion for a fixed t.
* `thm_1_1` : If the criterion holds for every t ≥ 1, then S is irrational.
-/

open scoped BigOperators

noncomputable section

/-! ## Definitions -/

/-- S = ∑_{n≥0} φ(n)/2^n. Since φ(0) = 0, this equals ∑_{n≥1} φ(n)/2^n. -/
def S_totient : ℝ := ∑' n, (Nat.totient n : ℝ) / (2 : ℝ) ^ n

/-- The tail sum T_N = ∑_{j≥1} φ(N+j)/2^j. -/
def tailSum (N : ℕ) : ℝ := ∑' j, (Nat.totient (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

/-- The integer part A_N = ∑_{n=1}^{N} φ(n) · 2^{N-n}. -/
def integerPart (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N, (Nat.totient (i + 1) : ℤ) * (2 : ℤ) ^ (N - 1 - i)

/-- d_j(N, t) = φ(N+t+j) - φ(N+j), the difference of totient values. -/
def d_coeff (N t j : ℕ) : ℤ :=
  (Nat.totient (N + t + j) : ℤ) - (Nat.totient (N + j) : ℤ)

/-- I_{N,t} = T_{N+t} - T_N, the difference of tail sums. -/
def I_diff (N t : ℕ) : ℝ := tailSum (N + t) - tailSum N

/-- Distance from a real number to the nearest integer:
    intDist(x) = min(frac(x), 1 - frac(x)). -/
def intDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

/-! ## Properties of intDist -/

lemma intDist_nonneg (x : ℝ) : 0 ≤ intDist x := by
  exact le_min ( Int.fract_nonneg x ) ( sub_nonneg.2 ( Int.fract_lt_one x |> le_of_lt ) )

lemma intDist_add_int (x : ℝ) (n : ℤ) : intDist (x + ↑n) = intDist x := by
  unfold intDist; aesop;

lemma intDist_le_abs_sub (x : ℝ) (n : ℤ) : intDist x ≤ |x - ↑n| := by
  unfold intDist;
  -- Let $k = \lfloor x \rfloor - n$. We consider two cases: $k \geq 0$ and $k < 0$.
  set k : ℤ := ⌊x⌋ - n
  by_cases hk : k ≥ 0;
  · simp +zetaDelta at *;
    exact Or.inl ( by rw [ abs_of_nonneg ] <;> linarith [ Int.fract_add_floor x, show ( n : ℝ ) ≤ ⌊x⌋ by exact_mod_cast hk, Int.fract_nonneg x, Int.fract_lt_one x ] );
  · cases abs_cases ( x - n ) <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · exact Or.inr ( by cases abs_cases ( x - n ) <;> linarith [ Int.fract_add_floor x, show ( ⌊x⌋ : ℝ ) ≤ n - 1 by exact_mod_cast Int.le_sub_one_of_lt ( by aesop ) ] );
    · exact Classical.or_iff_not_imp_left.2 fun h => by linarith [ Int.fract_add_floor x, show ( ⌊x⌋ : ℝ ) + 1 ≤ n by exact_mod_cast by linarith ] ;

/-! ## Summability -/

lemma summable_totient_div_pow :
    Summable (fun n => (Nat.totient n : ℝ) / (2 : ℝ) ^ n) := by
  have h_summable : Summable (fun n : ℕ => (n : ℝ) / 2^n) := by
    refine' summable_of_ratio_norm_eventually_le _ _ <;> norm_num at *;
    exacts [ 3 / 4, by norm_num, ⟨ 2, fun n hn => by rw [ abs_of_nonneg ( by positivity ) ] ; rw [ div_le_iff₀ ( by positivity ) ] ; induction hn <;> norm_num [ pow_succ' ] at * ; ring_nf at * ; nlinarith ⟩ ];
  exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by gcongr ; exact_mod_cast Nat.totient_le n ) h_summable

lemma summable_tailSum (N : ℕ) :
    Summable (fun j => (Nat.totient (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  have h_summable : Summable (fun n : ℕ => ((Nat.totient n) : ℝ) / (2 : ℝ) ^ n) := by
    exact summable_totient_div_pow;
  have h_shift : Summable (fun j : ℕ => (Nat.totient (j + N + 1) : ℝ) / (2 : ℝ) ^ (j + N + 1)) := by
    exact h_summable.comp_injective fun a b h => by simpa using h;
  convert h_shift.mul_left ( 2 ^ N ) using 2 ; ring;
  -- Combine and simplify the exponents of 2.
  field_simp
  ring;
  norm_num [ ← mul_pow ]

/-! ## Scaling Identity: 2^N · S = A_N + T_N -/

/-- Base case: S = tailSum 0. -/
lemma S_eq_tailSum_zero : S_totient = tailSum 0 := by
  simp only [S_totient, tailSum]
  rw [Summable.tsum_eq_zero_add summable_totient_div_pow]
  simp [Nat.totient_zero]

lemma integerPart_succ (N : ℕ) :
    integerPart (N + 1) = 2 * integerPart N + (Nat.totient (N + 1) : ℤ) := by
  simp [integerPart, Finset.sum_range_succ];
  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ Nat.sub_sub ] ; rcases eq_or_ne i N with rfl | hi' <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  rw [ show N - i = N - ( 1 + i ) + 1 by omega, pow_succ' ] ; ring

lemma tailSum_succ (N : ℕ) :
    2 * tailSum N = (Nat.totient (N + 1) : ℝ) + tailSum (N + 1) := by
  unfold tailSum; rw [ Summable.tsum_eq_zero_add ] ; norm_num; ring;
  · rw [ ← tsum_mul_right ] ; congr ; ext ; ring;
  · convert summable_tailSum N using 1

theorem scaling_identity (N : ℕ) :
    (2 : ℝ) ^ N * S_totient = ↑(integerPart N) + tailSum N := by
  induction' N with N ih <;> norm_num [ pow_succ, mul_assoc, mul_add, integerPart_succ, tailSum_succ ] at *;
  · -- Since $S = \text{tailSum } 0$ and $\text{integerPart } 0 = 0$, we have $S = 0 + \text{tailSum } 0$.
    simp [S_eq_tailSum_zero, integerPart];
  · linarith [ tailSum_succ N ]

/-! ## Proposition 2.1 -/

theorem prop_2_1 {A : ℤ} {r : ℕ} {b : ℕ} (hb_pos : 0 < b)
    (hS : S_totient = (A : ℝ) / ((2 : ℝ) ^ r * (b : ℝ)))
    {t : ℕ} (ht_pos : 0 < t) (hbt : (b : ℤ) ∣ ((2 : ℤ) ^ t - 1))
    {N : ℕ} (hN : r ≤ N) :
    ∃ k : ℤ, I_diff N t = (k : ℝ) := by
  -- By the scaling identity, we have $2^N \cdot S = A_N + T_N$ and $2^{N+t} \cdot S = A_{N+t} + T_{N+t}$.
  have h1 : (2 : ℝ) ^ N * S_totient = ↑(integerPart N) + tailSum N := by
    exact?
  have h2 : (2 : ℝ) ^ (N + t) * S_totient = ↑(integerPart (N + t)) + tailSum (N + t) := by
    exact?;
  -- So $I_{N, t} = T_{N+t} - T_N = (2^{N+t} - 2^N)S + (A_N - A_{N+t})$.
  have h3 : I_diff N t = (2 ^ (N + t) - 2 ^ N) * S_totient + (integerPart N - integerPart (N + t)) := by
    unfold I_diff; linarith;
  -- Substitute $S_totient = A / ((2 : ℝ) ^ r * (b : ℝ))$ into the expression for $I_{N, t}$.
  rw [h3, hS]
  field_simp;
  obtain ⟨ k, hk ⟩ := hbt;
  norm_cast at *;
  norm_num [ pow_add, Int.subNatNat_eq_coe ] at *;
  exact ⟨ k * A * 2 ^ ( N - r ) + ( integerPart N - integerPart ( N + t ) ), by rw [ show ( 2 ^ N : ℤ ) = 2 ^ r * 2 ^ ( N - r ) by rw [ ← pow_add, Nat.add_sub_of_le hN ] ] ; linear_combination hk * A * 2 ^ r * 2 ^ ( N - r ) ⟩

/-! ## Lemma 2.2: Tail Bound -/

lemma abs_d_coeff_le (N t j : ℕ) :
    |(d_coeff N t j : ℝ)| ≤ 2 * ↑N + ↑t + 2 * ↑j := by
  simp [d_coeff];
  rw [ abs_le ];
  constructor <;> linarith [ show ( Nat.totient ( N + t + j ) : ℝ ) ≤ N + t + j by exact_mod_cast Nat.totient_le _, show ( Nat.totient ( N + j ) : ℝ ) ≤ N + j by exact_mod_cast Nat.totient_le _, show ( Nat.totient ( N + t + j ) : ℝ ) ≥ 0 by positivity, show ( Nat.totient ( N + j ) : ℝ ) ≥ 0 by positivity ]

lemma summable_d_coeff_div_pow (N t : ℕ) :
    Summable (fun j => (d_coeff N t (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  convert Summable.sub ( summable_tailSum ( N + t ) ) ( summable_tailSum N ) using 1 ; norm_num [ d_coeff ] ; ring;
  exact funext fun _ => by ring;

lemma I_diff_eq_tsum (N t : ℕ) :
    I_diff N t = ∑' j, (d_coeff N t (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) := by
  convert Summable.tsum_sub ( summable_tailSum ( N + t ) ) ( summable_tailSum N ) using 1;
  · rw [ Summable.tsum_sub ];
    · rfl;
    · convert summable_tailSum ( N + t ) using 1;
    · convert summable_tailSum N using 1;
  · rw [ ← Summable.tsum_sub ] ; congr ; ext ; unfold d_coeff ; push_cast ; ring;
    · convert summable_tailSum ( N + t ) using 1;
    · convert summable_tailSum N using 1

lemma tsum_geom_shift (k : ℕ) :
    ∑' (j : ℕ), (1 : ℝ) / (2 : ℝ) ^ (j + k + 1) = 1 / (2 : ℝ) ^ k := by
  ring_nf;
  rw [ tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one ] <;> ring <;> norm_num

lemma tsum_linear_geom_shift (k : ℕ) :
    ∑' (j : ℕ), (↑(j + k + 1) : ℝ) / (2 : ℝ) ^ (j + k + 1) = (↑k + 2) / (2 : ℝ) ^ k := by
  -- We'll use the fact that ∑' j : ℕ, (j : ℝ) / 2^j = 2.
  have h_sum_j : ∑' j : ℕ, (j : ℝ) / 2 ^ j = 2 := by
    -- We'll use the fact that $\sum_{j=0}^{\infty} j x^j = \frac{x}{(1-x)^2}$ for $|x| < 1$.
    have h_geo_series : ∀ x : ℝ, |x| < 1 → ∑' j : ℕ, (j : ℝ) * x ^ j = x / (1 - x) ^ 2 := by
      exact?;
    convert h_geo_series ( 1 / 2 ) ( by norm_num [ abs_of_pos ] ) using 1 <;> norm_num [ div_eq_mul_inv ];
    aesop;
  have h_split : ∑' j : ℕ, (j + k + 1 : ℝ) / 2 ^ (j + k + 1) = (∑' j : ℕ, (j : ℝ) / 2 ^ (j + k + 1)) + (∑' j : ℕ, (k + 1 : ℝ) / 2 ^ (j + k + 1)) := by
    rw [ ← Summable.tsum_add ] ; congr ; ext j ; ring;
    · convert Summable.mul_left ( 1 / 2 ^ ( k + 1 ) ) ( show Summable fun j : ℕ => ( j : ℝ ) / 2 ^ j from by contrapose! h_sum_j; erw [ tsum_eq_zero_of_not_summable h_sum_j ] ; norm_num ) using 2 ; ring;
    · ring_nf;
      exact Summable.add ( Summable.mul_right _ <| Summable.mul_right _ <| Summable.mul_left _ <| summable_geometric_of_lt_one ( by norm_num ) <| by norm_num ) ( Summable.mul_right _ <| Summable.mul_right _ <| summable_geometric_of_lt_one ( by norm_num ) <| by norm_num );
  -- We'll use the fact that $\sum_{j=0}^{\infty} \frac{j}{2^{j+k+1}} = \frac{1}{2^{k+1}} \sum_{j=0}^{\infty} \frac{j}{2^j} = \frac{1}{2^{k+1}} \cdot 2 = \frac{1}{2^k}$.
  have h_sum_j_shift : ∑' j : ℕ, (j : ℝ) / 2 ^ (j + k + 1) = 1 / 2 ^ k := by
    convert congr_arg ( · * ( 1 / 2 ^ ( k + 1 ) : ℝ ) ) h_sum_j using 1 <;> ring;
    rw [ ← tsum_mul_left ] ; rw [ ← tsum_mul_right ] ; congr ; ext j ; ring;
  simp_all +decide [ div_eq_mul_inv, pow_add, tsum_mul_left ] ; ring;
  rw [ tsum_geometric_of_lt_one ] <;> norm_num ; ring

theorem tail_bound (N t J : ℕ) :
    |I_diff N t - ∑ j ∈ Finset.range J, (d_coeff N t (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)|
      ≤ ((2 * ↑N + ↑t + 2 * ↑J + 4 : ℝ)) / (2 : ℝ) ^ J := by
  -- By Lemma I_diff_eq_tsum, we can rewrite the left-hand side.
  have h₁ : abs ((I_diff N t) - (∑ j ∈ Finset.range J, ((d_coeff N t (j + 1)) : ℝ) / (2 : ℝ) ^ (j + 1))) = abs (∑' (j : ℕ), ((d_coeff N t (j + J + 1)) : ℝ) / (2 : ℝ) ^ (j + J + 1)) := by
    rw [ I_diff_eq_tsum N t, ← Summable.sum_add_tsum_nat_add J ( summable_d_coeff_div_pow N t ) ] ; aesop;
  -- By Lemma abs_d_coeff_le, we can bound each term in the sum.
  have h₂ : ∀ j : ℕ, abs ((d_coeff N t (j + J + 1)) / (2 : ℝ) ^ (j + J + 1)) ≤ (2 * N + t + 2 * (j + J + 1)) / (2 : ℝ) ^ (j + J + 1) := by
    intros j
    have h_abs : abs ((d_coeff N t (j + J + 1) : ℝ)) ≤ 2 * N + t + 2 * (j + J + 1) := by
      convert abs_d_coeff_le N t ( j + J + 1 ) using 1 ; push_cast ; ring;
    simpa only [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( j + J + 1 ) ) ] using div_le_div_of_nonneg_right h_abs ( by positivity );
  -- By Lemma tsum_linear_geom_shift, we can bound the sum.
  have h₃ : ∑' (j : ℕ), (2 * N + t + 2 * (j + J + 1) : ℝ) / (2 : ℝ) ^ (j + J + 1) = (2 * N + t + 2 * J + 4) / (2 : ℝ) ^ J := by
    -- We can split the sum into two separate sums and factor out constants.
    have h_split : ∑' (j : ℕ), (2 * N + t + 2 * (j + J + 1) : ℝ) / (2 : ℝ) ^ (j + J + 1) = (2 * N + t) * ∑' (j : ℕ), (1 : ℝ) / (2 : ℝ) ^ (j + J + 1) + 2 * ∑' (j : ℕ), (j + J + 1 : ℝ) / (2 : ℝ) ^ (j + J + 1) := by
      rw [ ← tsum_mul_left, ← tsum_mul_left ];
      rw [ ← Summable.tsum_add ] ; congr ; ext j ; ring;
      · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( J + 1 ) |>.2 <| summable_geometric_two;
      · have h_summable : Summable (fun j : ℕ => (j + J + 1 : ℝ) / (2 : ℝ) ^ (j + J + 1)) := by
          have := tsum_linear_geom_shift ( J : ℕ );
          contrapose! this;
          rw [ tsum_eq_zero_of_not_summable ] <;> norm_num ; positivity;
          convert this using 1;
        exact h_summable.mul_left 2;
    have := tsum_geom_shift J; have := tsum_linear_geom_shift J; simp_all +decide [ pow_add, div_eq_mul_inv, tsum_mul_left ] ; ring;
  refine' h₁ ▸ le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
  · refine' Summable.of_nonneg_of_le ( fun j => abs_nonneg _ ) ( fun j => h₂ j ) _;
    exact ( by contrapose! h₃; erw [ tsum_eq_zero_of_not_summable h₃ ] ; positivity );
  · refine' le_trans ( Summable.tsum_le_tsum h₂ _ _ ) _;
    · refine' Summable.of_nonneg_of_le ( fun j => abs_nonneg _ ) ( fun j => h₂ j ) _;
      exact ( by contrapose! h₃; erw [ tsum_eq_zero_of_not_summable h₃ ] ; positivity );
    · exact ( by contrapose! h₃; erw [ tsum_eq_zero_of_not_summable h₃ ] ; positivity );
    · rw [h₃]

/-! ## Theorem 2.3: Main Criterion -/

lemma partial_sum_intDist_eq {N t m J : ℕ} (hm : m ≤ J)
    (hdiv : ∀ j : ℕ, m < j → j ≤ J → (2 ^ j : ℤ) ∣ d_coeff N t j) :
    intDist (∑ i ∈ Finset.range J, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1)) =
    intDist (∑ i ∈ Finset.range m, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1)) := by
  -- The sum $\sum_{i=m}^{J-1} \frac{d_{i+1}}{2^{i+1}}$ is an integer, call it $K$.
  obtain ⟨K, hK⟩ : ∃ K : ℤ, ∑ i ∈ Finset.Ico m J, ((d_coeff N t (i + 1)) : ℝ) / 2 ^ (i + 1) = K := by
    use ∑ i ∈ Finset.Ico m J, (d_coeff N t (i + 1)) / 2 ^ (i + 1);
    push_cast [ Finset.sum_div _ _ _ ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Int.cast_div ( hdiv _ ( by linarith [ Finset.mem_Ico.mp hi ] ) ( by linarith [ Finset.mem_Ico.mp hi ] ) ) ( by positivity ) ] ; norm_num;
  rw [ ← Finset.sum_range_add_sum_Ico _ hm ];
  rw [ hK, intDist_add_int ]

theorem thm_2_3 {t : ℕ} (ht : 0 < t)
    (hyp : ∀ N₀ : ℕ, ∃ N m J : ℕ, N₀ ≤ N ∧ 1 ≤ m ∧ m ≤ J ∧
      (∀ j : ℕ, m < j → j ≤ J → (2 ^ j : ℤ) ∣ d_coeff N t j) ∧
      intDist (∑ i ∈ Finset.range m, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1))
        > ((2 * ↑N + ↑t + 2 * ↑J + 4 : ℝ)) / (2 : ℝ) ^ J) :
    ∀ (A : ℤ) (r : ℕ) (b : ℕ), 0 < b → (b : ℤ) ∣ ((2 : ℤ) ^ t - 1) →
      S_totient ≠ (A : ℝ) / ((2 : ℝ) ^ r * (b : ℝ)) := by
  intro A r b hb_pos hbt hS
  obtain ⟨N, m, J, hN, hm, hJ, hdiv, hdist⟩ := hyp r
  have h_int : ∃ k : ℤ, I_diff N t = k := by
    exact prop_2_1 hb_pos hS ht hbt hN
  have h_tail : |I_diff N t - ∑ j ∈ Finset.range J, (d_coeff N t (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)| ≤ (2 * N + t + 2 * J + 4 : ℝ) / (2 : ℝ) ^ J := by
    exact tail_bound N t J
  have h_dist : intDist (∑ i ∈ Finset.range J, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1)) ≤ (2 * N + t + 2 * J + 4 : ℝ) / (2 : ℝ) ^ J := by
    obtain ⟨ k, hk ⟩ := h_int; simp_all +decide [ abs_le ] ;
    exact le_trans ( intDist_le_abs_sub _ k ) ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ;
  have h_part : intDist (∑ i ∈ Finset.range J, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1)) = intDist (∑ i ∈ Finset.range m, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1)) := by
    apply_rules [ partial_sum_intDist_eq ]
  have h_final : intDist (∑ i ∈ Finset.range m, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1)) > (2 * N + t + 2 * J + 4 : ℝ) / (2 : ℝ) ^ J := by
    convert hdist using 1
  linarith [h_part, h_final]

/-! ## Helper lemmas for Theorem 1.1 -/

lemma nat_two_pow_odd_decomp (n : ℕ) (hn : 0 < n) :
    ∃ r b : ℕ, 0 < b ∧ ¬ 2 ∣ b ∧ n = 2 ^ r * b := by
  exact ⟨ Nat.factorization n 2, n / 2 ^ Nat.factorization n 2, Nat.div_pos ( Nat.le_of_dvd hn ( Nat.ordProj_dvd _ _ ) ) ( pow_pos ( by decide ) _ ), Nat.not_dvd_ordCompl ( by norm_num ) ( by aesop ), by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ] ⟩

lemma exists_pow_sub_one_dvd (b : ℕ) (hb : 0 < b) (hb_odd : ¬ 2 ∣ b) :
    ∃ t : ℕ, 0 < t ∧ (b : ℤ) ∣ ((2 : ℤ) ^ t - 1) := by
  -- By Euler's theorem, since $\gcd(2, b) = 1$, we have $2^{\phi(b)} \equiv 1 \pmod{b}$.
  have h_euler : 2 ^ Nat.totient b ≡ 1 [ZMOD (b : ℤ)] := by
    simpa [ ← Int.natCast_modEq_iff ] using Nat.ModEq.pow_totient ( Nat.prime_two.coprime_iff_not_dvd.mpr hb_odd );
  exact ⟨ b.totient, Nat.totient_pos.mpr hb, h_euler.symm.dvd ⟩

lemma rat_as_dyadic_odd (q : ℚ) :
    ∃ (A : ℤ) (r : ℕ) (b : ℕ), 0 < b ∧ ¬ 2 ∣ b ∧
      (q : ℝ) = (A : ℝ) / ((2 : ℝ) ^ r * (b : ℝ)) := by
  -- By Lemma `nat_two_pow_odd_decomp`, there exist r and b such that q.den = 2^r * b, with b odd and positive.
  obtain ⟨r, b, hb_pos, hb_odd, hden⟩ : ∃ r b : ℕ, 0 < b ∧ ¬ 2 ∣ b ∧ q.den = 2 ^ r * b := by
    exact nat_two_pow_odd_decomp q.den q.pos |> fun ⟨ r, b, hb1, hb2, hb3 ⟩ => ⟨ r, b, hb1, hb2, hb3 ⟩ ;
  exact ⟨ q.num, r, b, hb_pos, hb_odd, by simp +decide [ hden, Rat.cast_def ] ⟩

/-! ## Theorem 1.1: Main Result -/

theorem thm_1_1
    (hyp : ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N m J : ℕ, N₀ ≤ N ∧ 1 ≤ m ∧ m ≤ J ∧
      (∀ j : ℕ, m < j → j ≤ J → (2 ^ j : ℤ) ∣ d_coeff N t j) ∧
      intDist (∑ i ∈ Finset.range m, (d_coeff N t (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1))
        > ((2 * ↑N + ↑t + 2 * ↑J + 4 : ℝ)) / (2 : ℝ) ^ J) :
    Irrational S_totient := by
  intro h_rat;
  -- By assumption, there exist integers $A$, $r$, and $b$ such that $S = A / (2^r * b)$ with $b$ odd and positive.
  obtain ⟨A, r, b, hb_pos, hb_odd, hS⟩ : ∃ A : ℤ, ∃ r : ℕ, ∃ b : ℕ, 0 < b ∧ ¬ 2 ∣ b ∧ (S_totient : ℝ) = (A : ℝ) / ((2 : ℝ) ^ r * (b : ℝ)) := by
    obtain ⟨q, hq⟩ : ∃ q : ℚ, S_totient = q := by
      simpa [ eq_comm ] using h_rat;
    have := @rat_as_dyadic_odd q; aesop;
  -- By Lemma 2.2, there exists a positive integer $t$ such that $b \mid (2^t - 1)$.
  obtain ⟨t, ht_pos, ht_div⟩ : ∃ t : ℕ, 0 < t ∧ (b : ℤ) ∣ ((2 : ℤ) ^ t - 1) := exists_pow_sub_one_dvd b hb_pos hb_odd;
  exact absurd ( thm_2_3 ht_pos ( fun N₀ => hyp t ht_pos N₀ ) A r b hb_pos ht_div hS ) ( by aesop )

/-! ## Corollary 2.5 -/

/-- C_m(N,t) = ∑_{j=1}^{m} 2^{m-j} · d_j(N,t). -/
def C_sum (N t m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range m, (2 : ℤ) ^ (m - 1 - j) * d_coeff N t (j + 1)

theorem corollary_2_5 (N t m : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.range m, (d_coeff N t (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) =
    (C_sum N t m : ℝ) / (2 : ℝ) ^ m := by
  norm_num [ C_sum ] at *;
  rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ div_eq_div_iff ] <;> first | positivity | ring;
  simp +decide [ mul_assoc, ← pow_add, add_tsub_cancel_of_le ( show i ≤ m - 1 from Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ), add_comm, hm ];
  exact Or.inl ( by rw [ ← pow_succ, Nat.sub_add_cancel hm ] )

end