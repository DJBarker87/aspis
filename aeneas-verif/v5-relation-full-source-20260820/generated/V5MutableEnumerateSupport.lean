import Aeneas.Std

namespace V5MutableEnumerateSupport

open Aeneas Aeneas.Std Result ControlFlow Error

abbrev MutEnumerate (T : Type) :=
  core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)

/-- Pure model of moving an `IterMut` into `enumerate`, together with the
backward function that returns the mutated iterator after the loop. -/
def enumerate {T : Type} (iter : core.slice.iter.IterMut T) :
    Result (MutEnumerate T × (MutEnumerate T → core.slice.iter.IterMut T)) :=
  .ok ({ iter := iter, count := 0#usize }, fun result => result.iter)

/-- `Enumerate::next` specialized to an `IterMut`.  The ordinary iterator
trait cannot express the backward function required to write a changed item
back through a mutable iterator, so this model lifts the already checked
`IteratorIterMut.next` model and preserves that function explicitly. -/
def next {T : Type} (self : MutEnumerate T) :
    Result ((Option (Std.Usize × T)) × MutEnumerate T ×
      (MutEnumerate T → Option (Std.Usize × T) → MutEnumerate T)) := do
  let (item, iter, iterBack) ← core.slice.iter.IteratorIterMut.next self.iter
  match item with
  | none =>
      .ok (none, { iter := iter, count := self.count },
        fun result returned =>
          { result with
            iter := iterBack result.iter (returned.map Prod.snd) })
  | some value =>
      let nextCount ← self.count + 1#usize
      .ok (some (self.count, value), { iter := iter, count := nextCount },
        fun result returned =>
          { result with
            iter := iterBack result.iter (returned.map Prod.snd) })

end V5MutableEnumerateSupport
