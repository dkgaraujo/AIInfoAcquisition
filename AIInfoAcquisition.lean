-- This module serves as the root of the `AIInfoAcquisition` library.
-- Import modules here that should be built as part of the library.
import «AIInfoAcquisition».Basic

-- text below suggested by ChatGPT
import data.real.basic
import data.matrix.notation
import algebra.module.basic
import tactic

-- Define the parameters and variables
variables {N : ℕ} (d s : matrix (fin N) (fin N) ℝ)
variables (tau : fin N → ℝ)

-- Define the softmax function
def softmax (θ : matrix (fin N) (fin N) ℝ) (i j : fin N) : ℝ :=
  real.exp (θ i j) / (finset.univ.sum (λ k, real.exp (θ i k)))

-- Define the indifference equations
def indifference_d (θ : matrix (fin N) (fin N) ℝ) (i j : fin N) (t_d : matrix (fin N) (fin N) ℝ) : Prop :=
  ∑ k, softmax θ i k * (θ i j * real.exp (tau i)) = t_d i j

def indifference_s (θ : matrix (fin N) (fin N) ℝ) (i j : fin N) (t_s : matrix (fin N) (fin N) ℝ) : Prop :=
  ∑ k, softmax θ k i * (θ j i * real.exp (tau i)) = t_s i j

-- Define the theorem
theorem optimal_thresholds_exist :
  ∃ (d* s* : matrix (fin N) (fin N) ℝ),
  (∀ i j, indifference_d d* i j (λ i j, d i j)) ∧
  (∀ i j, indifference_s s* i j (λ i j, s i j)) :=
begin
  -- We start by using the Bolzano-Weierstrass theorem to argue that a bounded sequence has a convergent subsequence.
  -- First, we need to define a sequence of matrices representing potential thresholds.
  let seq_d : ℕ → matrix (fin N) (fin N) ℝ := λ n, d,
  let seq_s : ℕ → matrix (fin N) (fin N) ℝ := λ n, s,

  -- By Bolzano-Weierstrass, there exist convergent subsequences for both seq_d and seq_s
  have conv_d : ∃ (subseq_d : ℕ → ℕ), subseq_d.strict_mono ∧ (tendsto (λ n, seq_d (subseq_d n)) at_top (nhds d)) :=
    exists_seq_tendsto seq_d d,
  have conv_s : ∃ (subseq_s : ℕ → ℕ), subseq_s.strict_mono ∧ (tendsto (λ n, seq_s (subseq_s n)) at_top (nhds s)) :=
    exists_seq_tendsto seq_s s,

  -- Extract the convergent subsequences and their limits
  cases conv_d with subseq_d hd,
  cases conv_s with subseq_s hs,

  -- Define the limit points of these convergent subsequences as the optimal thresholds
  let d_star := d,
  let s_star := s,

  -- Now we need to show that these limit points satisfy the indifference conditions
  use [d_star, s_star],

  split,
  { -- Proof for indifference_d
    intros i j,
    unfold indifference_d,
    have h_lim_d : ∀ i j, tendsto (λ n, seq_d (subseq_d n) i j) at_top (nhds (d_star i j)),
    { intros i j,
      exact tendsto_pi_nhds.mpr (λ i, tendsto_pi_nhds.mpr (λ j, hd)) },

    -- Apply the limit to the indifference equation
    apply tendsto_nhds_unique,
    { apply tendsto_sum,
      intro k,
      apply tendsto.mul,
      { apply tendsto_softmax,
        exact h_lim_d i k },
      { exact tendsto_const_nhds } },
    { exact h_lim_d i j },
    { rw ←h_lim_d,
      exact h_lim_d i j } },
  { -- Proof for indifference_s
    intros i j,
    unfold indifference_s,
    have h_lim_s : ∀ i j, tendsto (λ n, seq_s (subseq_s n) i j) at_top (nhds (s_star i j)),
    { intros i j,
      exact tendsto_pi_nhds.mpr (λ i, tendsto_pi_nhds.mpr (λ j, hs)) },

    -- Apply the limit to the indifference equation
    apply tendsto_nhds_unique,
    { apply tendsto_sum,
      intro k,
      apply tendsto.mul,
      { apply tendsto_softmax,
        exact h_lim_s k i },
      { exact tendsto_const_nhds } },
    { exact h_lim_s j i },
    { rw ←h_lim_s,
      exact h_lim_s j i } }
end