import Mathlib

open scoped Topology

/--
Connected open subsets of `ℂ` are path-connected.
-/
lemma isConnected_isOpen_pathConnected_complex {V : Set ℂ}
    (hV : IsOpen V) (hC : IsConnected V) : IsPathConnected V :=
  (hV.isConnected_iff_isPathConnected).mp hC
