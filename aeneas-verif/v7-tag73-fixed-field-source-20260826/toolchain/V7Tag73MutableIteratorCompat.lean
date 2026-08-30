import Aeneas.Std

open Aeneas Aeneas.Std Result

/-- Type-correct view used only to construct Rust's `Enumerate` adapter. The
generated loop uses `IteratorEnumerateMut.next`, which retains the write-back
function. This is the same executable mutable-iterator model used by the
frozen V5 and V7 Merkle source bridges. -/
def core.slice.iter.IteratorIterMut.next_without_writeback
    {T : Type} (iter : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T) := do
  let (value, next, _) ← core.slice.iter.IteratorIterMut.next iter
  ok (value, next)

/-- Exact `Enumerate<IterMut<T>>::next` model, including the backward function
which writes a replacement item into the corresponding mutable slice slot. -/
def core.iter.adapters.enumerate.IteratorEnumerateMut.next
    {T : Type}
    (self : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut T)) :
    Result
      (Option (Std.Usize × T) ×
        core.iter.adapters.enumerate.Enumerate
          (core.slice.iter.IterMut T) ×
        (core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.IterMut T) →
          Option (Std.Usize × T) →
          core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.IterMut T))) := do
  let (value, nextIter, writeBack) ←
    core.slice.iter.IteratorIterMut.next self.iter
  let nextSelf := { self with iter := nextIter }
  match value with
  | none =>
      ok (none, nextSelf,
        fun current replacement =>
          { current with
            iter := writeBack current.iter (replacement.map Prod.snd) })
  | some item => do
      let nextCount ← self.count + 1#usize
      ok (some (self.count, item), { nextSelf with count := nextCount },
        fun current replacement =>
          { current with
            iter := writeBack current.iter (replacement.map Prod.snd) })

/-- Forward/backward form of `Iterator::enumerate` for a mutable slice
iterator. -/
def core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate
    {T : Type} (iter : core.slice.iter.IterMut T) :
    Result
      (core.iter.adapters.enumerate.Enumerate
          (core.slice.iter.IterMut T) ×
        (core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.IterMut T) →
          core.slice.iter.IterMut T)) :=
  ok ({ iter := iter, count := 0#usize }, fun current => current.iter)
