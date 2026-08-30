import AspisFormal.K1.V7Tag73UniqueRestorationRequests

/-!
# A finite root-transition sweep client for Tag-73 extraction

The deployed future-free verifier records a bounded list of transitions, but
the exact indices of squeeze transitions depend on the accepted execution.
The extractor must not guess a transcript role from a raw SHA coordinate:
an adversary may have queried that coordinate first.  Instead, the concrete
dispatcher accepts a verifier-transition index, derives the corresponding
pair of squeeze inputs from the stored snapshot, and replays the same-tape
prover to the first occurrence of either input.

This file constructs the finite client needed to exercise that dispatcher.
One sweep requests every root transition in a fixed half-open interval.
Nonexistent and non-squeeze indices fail closed and the client continues;
genuine squeeze indices create the controlled restoration nodes needed by the
K1.3--K1.5 probability arguments.  Repeated sweeps are supported because
ordinary extraction needs multiple independent responses at the same root
challenge and root nodes are immutable.

The construction is reply-insensitive.  Its exact request count and
replay-base-safe discipline are proved structurally, with no success,
probability, transcript-role, or extraction premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ConcreteRootSweepClient

open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73UniqueRestorationRequests

universe u

/-- Prepend requests for the root transitions
`start, start + 1, ..., start + count - 1` to an arbitrary client tail.
Every reply takes the same continuation. -/
def prependRootTransitionSweep {Result : Type u} (start : Nat) :
    (count : Nat) → ConcreteRestorationClient Result →
      ConcreteRestorationClient Result
  | 0, tail => tail
  | count + 1, tail =>
      .restore
        { nodeId := 0, verifierTransitionIndex := start }
        (fun _reply => prependRootTransitionSweep (start + 1) count tail)

@[simp] theorem prependRootTransitionSweep_zero
    {Result : Type u} (start : Nat)
    (tail : ConcreteRestorationClient Result) :
    prependRootTransitionSweep start 0 tail = tail := by
  rfl

@[simp] theorem prependRootTransitionSweep_succ
    {Result : Type u} (start count : Nat)
    (tail : ConcreteRestorationClient Result) :
    prependRootTransitionSweep start (count + 1) tail =
      .restore { nodeId := 0, verifierTransitionIndex := start }
        (fun _reply => prependRootTransitionSweep (start + 1) count tail) := by
  rfl

/-- Repeat a complete root interval sweep.  Each round starts again at index
zero, which is valid because every request is based on the immutable root. -/
def repeatRootTransitionSweep {Result : Type u} (transitionCount : Nat) :
    (rounds : Nat) → ConcreteRestorationClient Result →
      ConcreteRestorationClient Result
  | 0, tail => tail
  | rounds + 1, tail =>
      prependRootTransitionSweep 0 transitionCount
        (repeatRootTransitionSweep transitionCount rounds tail)

@[simp] theorem repeatRootTransitionSweep_zero
    {Result : Type u} (transitionCount : Nat)
    (tail : ConcreteRestorationClient Result) :
    repeatRootTransitionSweep transitionCount 0 tail = tail := by
  rfl

@[simp] theorem repeatRootTransitionSweep_succ
    {Result : Type u} (transitionCount rounds : Nat)
    (tail : ConcreteRestorationClient Result) :
    repeatRootTransitionSweep transitionCount (rounds + 1) tail =
      prependRootTransitionSweep 0 transitionCount
        (repeatRootTransitionSweep transitionCount rounds tail) := by
  rfl

/-- A reply-branch-independent certificate that a client issues exactly
`count` requests and then returns the named result.  This is a static property
of the extractor program, not a claim that any restoration request succeeds. -/
inductive ExactRequestCount {Result : Type u} (result : Result) :
    Nat → ConcreteRestorationClient Result → Prop where
  | pure : ExactRequestCount result 0 (.pure result)
  | restore (request : ConcreteRestorationRequest)
      (next : ConcreteRestorationReply → ConcreteRestorationClient Result)
      {count : Nat}
      (tails : ∀ reply, ExactRequestCount result count (next reply)) :
      ExactRequestCount result (count + 1) (.restore request next)

theorem prepend_root_transition_sweep_exact_request_count
    {Result : Type u} (result : Result) (start count : Nat) :
    ExactRequestCount result count
      (prependRootTransitionSweep start count (.pure result)) := by
  induction count generalizing start with
  | zero => exact .pure
  | succ count ih =>
      apply ExactRequestCount.restore
      intro reply
      exact ih (start + 1)

/-- Prepending a sweep adds exactly its interval length to any already
certified reply-insensitive client tail. -/
theorem prepend_root_transition_sweep_adds_exact_request_count
    {Result : Type u} {result : Result} {tailCount : Nat}
    {tail : ConcreteRestorationClient Result}
    (tailExact : ExactRequestCount result tailCount tail)
    (start count : Nat) :
    ExactRequestCount result (count + tailCount)
      (prependRootTransitionSweep start count tail) := by
  induction count generalizing start with
  | zero => simpa using tailExact
  | succ count ih =>
      have tails : ∀ (_reply : ConcreteRestorationReply),
          ExactRequestCount result (count + tailCount)
            (prependRootTransitionSweep (start + 1) count tail) := by
        intro reply
        exact ih (start + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ExactRequestCount.restore
          { nodeId := 0, verifierTransitionIndex := start }
          (fun _reply => prependRootTransitionSweep (start + 1) count tail)
          tails)

theorem repeat_root_transition_sweep_exact_request_count
    {Result : Type u} (result : Result) (transitionCount rounds : Nat) :
    ExactRequestCount result (rounds * transitionCount)
      (repeatRootTransitionSweep transitionCount rounds (.pure result)) := by
  induction rounds with
  | zero => simpa using (ExactRequestCount.pure (result := result))
  | succ rounds ih =>
      simpa [Nat.succ_mul, Nat.add_comm] using
        prepend_root_transition_sweep_adds_exact_request_count ih 0
          transitionCount

/-- A root sweep satisfies the operational scheduling rule regardless of its
tail: every generated request names node zero. -/
theorem prepend_root_transition_sweep_replay_base_safe
    {Result : Type u} (start count : Nat)
    (tail : ConcreteRestorationClient Result)
    (tailSafe : ReplayBaseSafeConcreteClient tail) :
    ReplayBaseSafeConcreteClient
      (prependRootTransitionSweep start count tail) := by
  induction count generalizing start with
  | zero => simpa using tailSafe
  | succ count ih =>
      apply ReplayBaseSafeConcreteClient.restore
      · exact root_restoration_request_is_replay_base_safe start
      · intro reply
        exact ih (start + 1)

theorem repeat_root_transition_sweep_replay_base_safe
    {Result : Type u} (transitionCount rounds : Nat)
    (tail : ConcreteRestorationClient Result)
    (tailSafe : ReplayBaseSafeConcreteClient tail) :
    ReplayBaseSafeConcreteClient
      (repeatRootTransitionSweep transitionCount rounds tail) := by
  induction rounds with
  | zero => simpa using tailSafe
  | succ rounds ih =>
      exact prepend_root_transition_sweep_replay_base_safe 0 transitionCount
        _ ih

/-- The production-shaped sweep client: inspect the complete deployed
1511-transition cap for each requested extraction round, then return the fixed
accumulator extractor supplied independently of the hidden tape. -/
def deployedRootSweepClient {Result : Type u} (rounds : Nat)
    (result : Result) : ConcreteRestorationClient Result :=
  repeatRootTransitionSweep 1511 rounds (.pure result)

theorem deployed_root_sweep_client_exact_request_count
    {Result : Type u} (rounds : Nat) (result : Result) :
    ExactRequestCount result (rounds * 1511)
      (deployedRootSweepClient rounds result) := by
  exact repeat_root_transition_sweep_exact_request_count result 1511 rounds

theorem deployed_root_sweep_client_replay_base_safe
    {Result : Type u} (rounds : Nat) (result : Result) :
    ReplayBaseSafeConcreteClient (deployedRootSweepClient rounds result) := by
  apply repeat_root_transition_sweep_replay_base_safe
  exact ReplayBaseSafeConcreteClient.pure result

#print axioms prepend_root_transition_sweep_exact_request_count
#print axioms prepend_root_transition_sweep_adds_exact_request_count
#print axioms repeat_root_transition_sweep_exact_request_count
#print axioms prepend_root_transition_sweep_replay_base_safe
#print axioms repeat_root_transition_sweep_replay_base_safe
#print axioms deployed_root_sweep_client_exact_request_count
#print axioms deployed_root_sweep_client_replay_base_safe

end AspisK1.V7Tag73ConcreteRootSweepClient
