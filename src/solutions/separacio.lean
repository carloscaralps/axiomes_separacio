import topology.basic

open topological_space set filter
localized "notation `𝓝` := nhds" in topological_space
localized "notation `𝓝[` s `] ` x:100 := nhds_within x s" in topological_space

noncomputable theory
open classical

variables {X : Type} [topological_space X] [nonempty X]

class t0_space (X : Type) [topological_space X] : Prop :=
(t0 : ∀ x y, x ≠ y → ∃ (U : set X), is_open U ∧ ((x ∈ U ∧ y ∉ U) ∨ (x ∉ U ∧ y ∈ U)) )

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
  { exact or.inl hh }
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

def limit_unicity (X : Type) [topological_space X] [nonempty X] := 
      ∀ (x y : X) (f : filter X) (hx : filter_lim f x) (hy : filter_lim f y), x=y

lemma t2_iff_unicity : t2_space X ↔ limit_unicity X :=
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

def regular_space (X : Type) [topological_space X] := ∀ (x : X) (F : set X) (hF : is_closed F) (hxF : x ∉ F), 
  ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), x ∈ U ∧ F ⊆ V

class t3_space (X : Type) [topological_space X] extends t1_space X : Prop :=
(regular : regular_space X)

instance t3_space.t2_space [t3_space X] : t2_space X :=
begin
  --sorry
  fconstructor,
  intros x y hxy,
  obtain hsingleton := (@t1_iff_singleton_closed X _ _).1 t3_space.to_t1_space,
  obtain ⟨U, V, hU, hV, hUV, h⟩ := t3_space.regular x {y} (hsingleton y) hxy,
  obtain hyV := singleton_subset_iff.mp h.2,
  exact ⟨U, V, hU, hV, hUV, h.1, hyV⟩,
  --sorry
end


lemma inter_is_not_is_empty_intersection {X : Type} {x : X} {U V : set X}
  (hxU : x ∈ U) (hUV : U ∩ V = ∅ ) : x ∉ V := disjoint_left.1 (disjoint_iff_inter_eq_empty.2 hUV) hxU

lemma t3_iff_t0_regular : t3_space X ↔ t0_space X ∧ regular_space X :=
begin
  --sorry
  split,
  {
    introI,
    split,
    { exact t1_space.t0_space },
    { exact t3_space.regular }
  },
  {
    intro h,
    haveI := h.1,
    exact { t1:= 
    begin
      intros x y hxy,
      obtain ⟨U, hU, hh⟩ := t0_space.t0 x y hxy,
      cases hh,
      { exact ⟨U, hU, hh⟩ },
      {
        have h_not_in_com : y ∉ Uᶜ,
        { intro t,
          exact (not_mem_of_mem_compl t) hh.2 },
        obtain ⟨V, T, hV, hT, hVT, hhh⟩ := h.2 y Uᶜ (is_closed_compl_iff.mpr hU) h_not_in_com,
        use T,
        split,
        { exact hT },
        split,
        { exact hhh.2 hh.1 },
        { exact inter_is_not_is_empty_intersection hhh.1 hVT }
      }
    end, regular := h.2 },
  }
  --sorry
end

lemma regular_iff_filter_def : regular_space X ↔ ∀{s:set X} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥ :=
begin
  --sorry
  split; intro h,
  {
    intros F x hF hxF,
    obtain ⟨U, V, hU, hV, hUV, hh⟩ := h x F hF hxF,
    use V,
    split,
    { exact hV },
    split,
    { exact hh.2 },
    { rw ← empty_mem_iff_bot,
      have : ∅ ∈ 𝓝 x ⊓ principal V,
      {
        rw mem_inf_iff,
        use U,
        split,
        { exact is_open.mem_nhds hU hh.1 },
        use V,
        split,
        { exact mem_principal_self V },
        { exact eq.symm hUV }
      },
      exact this }
  },
  {
    intros x F hF hxF,
    obtain ⟨U, hU, hh⟩ := h hF hxF,
    rw [← empty_mem_iff_bot] at hh,
    have hexU : ∅ ∈ 𝓝 x ⊓ principal U,
    { exact hh.2 },
    rw mem_inf_iff at hexU,
    obtain ⟨T₁, hT₁, V, hV, hTV₁⟩ := hexU,
    obtain ⟨T, hTT₁, hT⟩ := mem_nhds_iff.1 hT₁,
    use T,
    use U,
    split,
    { exact hT.1 },
    split,
    { exact hU },
    split,
    { have : T ∩ U ⊆ ∅,
      { rw hTV₁,
        exact inter_subset_inter hTT₁ (mem_principal.mp hV) },
      exact subset_eq_empty this rfl },
    { exact ⟨hT.2, hh.1⟩ }
  }
  --sorry
end

