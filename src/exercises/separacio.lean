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
  sorry
end

lemma t1_iff_singleton_closed : t1_space X ↔ ∀ x, is_closed ({x} : set X) :=
begin
  sorry
end

class t2_space (X : Type) [topological_space X] : Prop :=
(t2 : ∀ x y, x ≠ y → ∃ (U V: set X) (hU : is_open U) (hV: is_open V) (hUV : U ∩ V = ∅), x ∈ U ∧ y ∈ V)

instance t2_space.t1_space [t2_space X] : t1_space X :=
begin
  sorry
end

variables (f : filter X) (x : X)

def filter_lim (f : filter X) (x : X) := f ≤ 𝓝 x ∧ f ≠ ⊥

def limit_unicity (X : Type) [topological_space X] [nonempty X] := 
      ∀ (x y : X) (f : filter X) (hx : filter_lim f x) (hy : filter_lim f y), x=y

lemma t2_iff_unicity : t2_space X ↔ limit_unicity X :=
begin
  sorry
end

class t2_5_space (X : Type) [topological_space X] : Prop :=
(t2_5 : ∀ x y  (h : x ≠ y), ∃ (U V: set X), is_open U ∧  is_open V ∧
                                            closure U ∩ closure V = ∅ ∧ x ∈ U ∧ y ∈ V)

instance t2_5_space.t2_space [t2_5_space X] : t2_space X :=
begin
  sorry
end

def regular_space (X : Type) [topological_space X] := ∀ (x : X) (F : set X) (hF : is_closed F) (hxF : x ∉ F), 
  ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), x ∈ U ∧ F ⊆ V

class t3_space (X : Type) [topological_space X] extends t1_space X : Prop :=
(regular : regular_space X)

instance t3_space.t2_space [t3_space X] : t2_space X :=
begin
  sorry
end

instance t2_space.t2_5_space [t3_space X] : t2_5_space X :=
begin
  sorry
end

lemma inter_is_not_is_empty_intersection {X : Type} {x : X} {U V : set X}
  (hxU : x ∈ U) (hUV : U ∩ V = ∅ ) : x ∉ V := disjoint_left.1 (disjoint_iff_inter_eq_empty.2 hUV) hxU

lemma t3_iff_t0_regular : t3_space X ↔ t0_space X ∧ regular_space X :=
begin
  sorry
end

lemma regular_iff_filter_def : regular_space X ↔ ∀{s:set X} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥ :=
begin
  sorry
end

lemma t3_iff_open_closure : t3_space X ↔ t1_space X ∧ (∀ (x : X) (U : set X) (hx : x ∈ U) (hU : is_open U), 
    ∃ (V : set X) (hV : is_open V), x ∈ V ∧ closure V ⊆ U) :=
begin
  sorry
end

def normal_space (X : Type) [topological_space X] := ∀ (F T : set X) (hF : is_closed F) (hT : is_closed T) (hFT : F ∩ T = ∅),
        ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), F ⊆ U ∧ T ⊆ V

class t4_space (X : Type) [topological_space X] extends t1_space X : Prop :=
(normal : normal_space X)

instance t4_space.t3_space [t4_space X] : t3_space X :=
begin
  sorry
end

lemma t4_iff_open_closure : t4_space X ↔ t1_space X ∧ (∀ (U K : set X) (hK : is_closed K) (hU : is_open U) (hKU: K ⊆ U),
        ∃ (V : set X) (hV : is_open V), K ⊆ V ∧ closure V ⊆ U) :=
begin
  sorry
end
