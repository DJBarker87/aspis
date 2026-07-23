import ComponentBSamplerMixingEvaluateUnified20260722
import Mathlib

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.MultilinearEvalProofs

open ComponentBGenerated

abbrev M31 := aspis_core.field.M31
abbrev QM31 := aspis_core.field.QM31

def blend {R : Type} [Ring R] (z left right : R) : R :=
  left + z * (right - left)

end ComponentBGenerated.MultilinearEvalProofs
