import AspisFormal.Pool.V7PackedLimbDecoder

/-! Literal canonical `(c0.a,c0.b,c1.a,c1.b)` integer representation. -/

set_option autoImplicit false

namespace AspisPool.V7CanonicalQM31

open AspisPool.V7PackedLimbDecoder

structure CanonicalQM31 where
  c0a : CanonicalM31
  c0b : CanonicalM31
  c1a : CanonicalM31
  c1b : CanonicalM31

end AspisPool.V7CanonicalQM31
