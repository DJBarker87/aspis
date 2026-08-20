import Relation.Funs

/-!
# Standard-library support used by the complete V5 relation extraction

The production verifier contains `iter_mut().enumerate()` loops.  Aeneas's
generic `Iterator` record cannot carry the backward function needed to write a
mutated element through `IterMut`, so the checked snapshot specializes that
one adapter.  The theorems below expose its exact behavior.  They also record
that the supplied fixed-array iterator visits the array in increasing order.
-/

namespace AspisV5RelationGeneratedSupportProof

open Aeneas Aeneas.Std Result ControlFlow Error

theorem mutable_enumerate_start_exact {T : Type}
    (iterator : core.slice.iter.IterMut T) :
    V5MutableEnumerateSupport.enumerate iterator =
      .ok ({ iter := iterator, count := 0#usize }, fun result => result.iter) := by
  rfl

theorem mutable_enumerate_next_some_exact {T : Type}
    (self : V5MutableEnumerateSupport.MutEnumerate T)
    (value : T) (iterator : core.slice.iter.IterMut T)
    (iteratorBack : core.slice.iter.IterMut T → Option T →
      core.slice.iter.IterMut T)
    (nextCount : Std.Usize)
    (innerNext :
      core.slice.iter.IteratorIterMut.next self.iter =
        .ok (some value, iterator, iteratorBack))
    (countNext : self.count + 1#usize = ok nextCount) :
    V5MutableEnumerateSupport.next self =
      .ok (some (self.count, value),
        { iter := iterator, count := nextCount },
        fun result returned =>
          { result with
            iter := iteratorBack result.iter (returned.map Prod.snd) }) := by
  simp [V5MutableEnumerateSupport.next, innerNext, countNext]

theorem mutable_enumerate_next_none_exact {T : Type}
    (self : V5MutableEnumerateSupport.MutEnumerate T)
    (iterator : core.slice.iter.IterMut T)
    (iteratorBack : core.slice.iter.IterMut T → Option T →
      core.slice.iter.IterMut T)
    (innerNext :
      core.slice.iter.IteratorIterMut.next self.iter =
        .ok (none, iterator, iteratorBack)) :
    V5MutableEnumerateSupport.next self =
      .ok (none, { iter := iterator, count := self.count },
        fun result returned =>
          { result with
            iter := iteratorBack result.iter (returned.map Prod.snd) }) := by
  simp [V5MutableEnumerateSupport.next, innerNext]

open V5RelationFullGenerated

theorem fixed_array_into_iter_exact {T : Type} {N : Std.Usize}
    (array : Array T N) :
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter array =
      .ok { array := array, index := 0 } := by
  rfl

theorem fixed_array_next_some_exact {T : Type} {N : Std.Usize}
    (iterator : core.array.iter.IntoIter T N)
    (inBounds : iterator.index < iterator.array.val.length) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iterator =
      .ok (some iterator.array.val[iterator.index],
        { iterator with index := iterator.index + 1 }) := by
  have h : iterator.index < N.val := by simpa using inBounds
  simp [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    h]

theorem fixed_array_next_none_exact {T : Type} {N : Std.Usize}
    (iterator : core.array.iter.IntoIter T N)
    (exhausted : ¬ iterator.index < iterator.array.val.length) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iterator =
      .ok (none, iterator) := by
  have h : ¬ iterator.index < N.val := by simpa using exhausted
  simp [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    h]

#print axioms mutable_enumerate_start_exact
#print axioms mutable_enumerate_next_some_exact
#print axioms mutable_enumerate_next_none_exact
#print axioms fixed_array_into_iter_exact
#print axioms fixed_array_next_some_exact
#print axioms fixed_array_next_none_exact

end AspisV5RelationGeneratedSupportProof
