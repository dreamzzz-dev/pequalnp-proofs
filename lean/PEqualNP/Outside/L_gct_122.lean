import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser

open Finset Module PEqualNP.Gct.Helpers

namespace PEqualNP.Outside.L_gct_122

lemma polar {m : ℕ} (W : Submodule ℂ (Fin m → ℂ)) (w : Fin m → ℂ)
    (h : ∀ u ∈ W, ∑ i, w i * u i ^ 2 = 0) (u v : Fin m → ℂ) (hu : u ∈ W) (hv : v ∈ W) :
    ∑ i, w i * (u i * v i) = 0 := by
  have eqn : (2 : ℂ) * (∑ i, w i * (u i * v i)) =
      (∑ i, w i * (u+v) i ^ 2) - (∑ i, w i * u i ^ 2) - (∑ i, w i * v i ^ 2) := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    ring
  rw [h _ (W.add_mem hu hv), h _ hu, h _ hv] at eqn
  simpa using eqn

lemma mixed {m : ℕ} (W : Submodule ℂ (Fin m → ℂ))
    (h : ∀ u ∈ W, ∑ i, u i ^ 4 = 0) (u v z t : Fin m → ℂ)
    (hu : u ∈ W) (hv : v ∈ W) (hz : z ∈ W) (ht : t ∈ W) :
    ∑ i, (u i * v i) * (z i * t i) = 0 := by
  have squares (a b : Fin m → ℂ) (ha : a ∈ W) (hb : b ∈ W) :
      ∑ i, b i ^ 2 * a i ^ 2 = 0 := by
    have eqn : (12 : ℂ) * (∑ i, b i ^ 2 * a i ^ 2) =
        (∑ i, (a+b) i ^ 4) + (∑ i, (a-b) i ^ 4) -
        2 * (∑ i, a i ^ 4) - 2 * (∑ i, b i ^ 4) := by
      simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [h _ (W.add_mem ha hb), h _ (W.sub_mem ha hb), h _ ha, h _ hb] at eqn
    simpa using eqn
  apply polar W (fun i => u i * v i) _ z t hz ht
  intro b hb
  simpa only [mul_comm] using polar W (fun i => b i ^ 2) (fun a ha => squares a b ha hb) u v hu hv

lemma square_rank {m : ℕ} (W : Submodule ℂ (Fin m → ℂ)) :
    finrank ℂ W ≤ finrank ℂ (W * W) := by
  classical
  obtain ⟨e, he, heunit⟩ := Kneser.Asm.exists_isUnit_of_support _
    (Kneser.Asm.support_sup_offSupp W W)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp he
  have hin : W.map (LinearMap.mulLeft ℂ e) ≤ W * W := by
    rintro _ ⟨v,hv,rfl⟩
    change e * v ∈ W * W
    have hz : b * v = 0 := by
      funext i
      by_cases hvi : v i = 0
      · simp [hvi]
      · have hbi := (Kneser.Asm.mem_offSupp.mp hb) i ⟨v,hv,hvi⟩ ⟨v,hv,hvi⟩
        simp [hbi]
    rw [← hab, add_mul, hz, add_zero]
    exact Submodule.mul_mem_mul ha hv
  simpa only [Kneser.ETr.finrank_map_mulLeft heunit] using Submodule.finrank_mono hin

lemma bound {m : ℕ} (W : Submodule ℂ (Fin m → ℂ))
    (h2 : ∀ u ∈ W, ∑ i, u i ^ 2 = 0) (h4 : ∀ u ∈ W, ∑ i, u i ^ 4 = 0) :
    3 * finrank ℂ W ≤ m := by
  classical
  by_cases hW : W = ⊥
  · rw [hW, finrank_bot, mul_zero]
    exact Nat.zero_le _
  let V := W * W
  have trace_zero (v : Fin m → ℂ) (hv : v ∈ V) : ∑ i, v i = 0 := by
    refine Submodule.mul_induction_on hv ?_ ?_
    · intro a ha b hb
      simpa using polar W 1 (by simpa using h2) a b ha hb
    · intro a b ha hb
      simp [sum_add_distrib, ha, hb]
  have perp (v : Fin m → ℂ) (hv : v ∈ V) : ∀ z ∈ V, ∑ i, v i * z i = 0 := by
    refine Submodule.mul_induction_on hv ?_ ?_
    · intro a ha b hb z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro c hc d hd
        exact mixed W h4 a b c d ha hb hc hd
      · intro c d hc hd
        simp only [Pi.add_apply, mul_add, sum_add_distrib, hc, hd, add_zero]
    · intro a b ha hb z hz
      simp [add_mul, sum_add_distrib, ha z hz, hb z hz]
  have hinf : V ⊓ stab V = ⊥ := by
    apply eq_bot_iff.mpr
    rintro x ⟨hx, hs⟩
    change x = 0
    funext j
    obtain ⟨e, he, heval⟩ := exists_indicator hs j
    have hsum := trace_zero _ (he _ hx)
    let A := (univ : Finset (Fin m)).filter (fun i => x i = x j)
    have hcard : 0 < A.card := card_pos.mpr ⟨j, by simp [A]⟩
    have heq : (∑ i, (e*x) i) = (A.card : ℂ) * x j := by
      simp only [Pi.mul_apply, heval, ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      calc ∑ i ∈ A, x i = ∑ _i ∈ A, x j := by
               apply sum_congr rfl
               intro i hi
               exact (mem_filter.mp hi).2
           _ = _ := by simp
    rw [heq] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left (by exact_mod_cast hcard.ne')
  have hdim := perp_bound (V ⊔ stab V) V (by
    intro v hv z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    simp only [Pi.add_apply, add_mul, sum_add_distrib, perp a ha z hz, zero_add]
    exact trace_zero _ (hb _ hz))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V (stab V)
  rw [hinf, finrank_bot, add_zero] at hsup
  have hk := PEqualNP.Gct.L065 m W W (stab V) hW hW (fun _ => Iff.rfl)
  have hprod := square_rank W
  change _ ≤ finrank ℂ V at hprod
  change _ ≤ finrank ℂ V + _ at hk
  rw [hsup, Fintype.card_fin] at hdim
  omega

end PEqualNP.Outside.L_gct_122

theorem PEqualNP.Outside.L_gct_122 : ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m := by
  intro m X h2 h4
  exact PEqualNP.Outside.L_gct_122.bound X h2 h4
