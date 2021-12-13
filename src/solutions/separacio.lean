import topology.basic

open topological_space set filter
localized "notation `𝓝` := nhds" in topological_space

noncomputable theory
open classical

variables {X : Type} [topological_space X] [nonempty X]

class t0_space (X : Type) [topological_space X] :=
(t0 : ∀ x y, x ≠ y → ∃ (U : set X), is_open U ∧ (x ∈ U ∨ y ∈ U) )

class t1_space (X : Type) [topological_space X] : Prop :=
(t1 : ∀ x y, x ≠ y → ∃ (U : set X), is_open U ∧ x ∈ U ∧ y ∉ U)

instance t1_space.t0_space [t1_space X] : t0_space X :=
begin
  --sorry
  fconstructor,
  intros x y hxy,
  obtain ⟨U, hU, hh⟩  := t1_space.t1 x y hxy,
  use U,
  split,
  { exact hU },
  { exact or.inl hh.left }
  --sorry
end

lemma t1_iff_singleton_closed : t1_space X ↔ ∀ x, is_closed ({x} : set X) :=
begin
  --sorry
  split,
  {
    introI,
    intro x,
    rw ← is_open_compl_iff,
    have p : ⋃₀ {U : set X | (x ∉ U) ∧ (is_open U)} = {x}ᶜ,
    { apply subset.antisymm; intros t ht,
      { rcases ht with ⟨A, ⟨hxA, hA⟩, htA⟩,
        rw [mem_compl_eq, mem_singleton_iff],
        intro h,
        exact hxA (by rwa h at htA) },
      { obtain ⟨U, hU, hh⟩ := t1_space.t1 t x (mem_compl_singleton_iff.mp ht),
        use U,
        split,
        { exact ⟨hh.2, hU⟩ },
        { exact hh.1 } } },
    rw ← p,
    apply is_open_sUnion,
    intros B hB,
    exact hB.2,
  },
  {
    intro h,
    fconstructor,
    intros x y hxy,
    use {y}ᶜ,
    split,
    { exact is_open_compl_iff.mpr (h y) },
    split,
    { exact mem_compl_singleton_iff.mpr hxy },
    { exact not_not.mpr rfl }
  }
  --sorry
end

lemma t1_iff_neighborhood_is_singleton : t1_space X ↔ ∀ (x : X), ⋂₀ (𝓝 x).sets = {x} :=
begin
  split,
  {
    introI,
    intro x,
    apply subset.antisymm; intros t ht,
    {
      sorry
    },
    {
      sorry
    }
  },
  {
    intro h1,
    fconstructor,
    intros x y hxy,
    by_contradiction,
    push_neg at h,
    sorry
  }
end

class t2_space (X : Type) [topological_space X] : Prop :=
(t2 : ∀ x y, x ≠ y → ∃ (U V: set X) (hU : is_open U) (hV: is_open V) (hUV : U ∩ V = ∅), x ∈ U ∧ y ∈ V)

instance t2_space.t1_space [t2_space X] : t1_space X :=
begin
  --sorry
  fconstructor,
  intros x y hxy,
  obtain ⟨U, V, hU, hV, hUV, h⟩ := t2_space.t2 x y hxy,
  use U,
  split,
  { exact hU },
  split,
  { exact h.1 },
  { intro con,
    have ht : y ∈ (∅ : set X),
    {
      rw ← hUV,
      exact ⟨con, h.2⟩
    },
    exact not_mem_empty y ht }
  --sorry
end

variables (f : filter X) (x : X)

def filter_lim (f : filter X) (x : X) := f ≤ 𝓝 x ∧ f ≠ ⊥

lemma t2_iff_unicity : t2_space X ↔ ∀ (x y : X) (f : filter X) (hx : filter_lim f x) (hy : filter_lim f y), x=y :=
begin
  --sorry
  split,
  {
    introI,
    intros x y f hx hy,
    by_contradiction hxy,
    obtain ⟨U, V, hU, hV, hUV, hh⟩ := t2_space.t2 x y hxy,
    have hhU : U ∈ f,
    { exact le_def.1 hx.1 U (is_open.mem_nhds hU hh.left) },
    have hhV : V ∈ f,
    { exact le_def.1 hy.1 V (is_open.mem_nhds hV hh.right) },
    obtain hf := filter.inter_sets f hhU hhV,
    rw hUV at hf,
    exact hx.2 (empty_mem_iff_bot.1 hf)
  },
  {
    intro h1,
    fconstructor,
    intros x y hxy,
    by_contra,
    push_neg at h,
    have : 𝓝 x ⊓ 𝓝 y ≠ ⊥,
    { intro t,
      rw ← empty_mem_iff_bot at t,
      rw mem_inf_iff at t,
      obtain ⟨U₁, hU₁, V₁, hV₁, hUV₁⟩ := t,
      obtain ⟨U, hU, hU_op, hxU⟩ := mem_nhds_iff.1 hU₁,
      obtain ⟨V, hV, hV_op, hyV⟩ := mem_nhds_iff.1 hV₁,
      have : U ∩ V = ∅,
      { have : U ∩ V ⊆ ∅,
        { rw hUV₁,
          exact inter_subset_inter hU hV },
        exact subset_eq_empty this rfl },
      exact (h U V hU_op hV_op this hxU) hyV },
    have hx : 𝓝 x ⊓ 𝓝 y ≤ 𝓝 x,
    { apply le_def.2,
      intros T hT,
      exact mem_inf_of_left hT },
    have hy : 𝓝 x ⊓ 𝓝 y ≤ 𝓝 y,
    { apply le_def.2,
      intros T hT,
      exact mem_inf_of_right hT },
    exact hxy (h1 x y (𝓝 x ⊓ 𝓝 y) ⟨hx, this⟩ ⟨hy, this⟩),
  }
  --sorry
end