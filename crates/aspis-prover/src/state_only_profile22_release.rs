//! Fixed-boundary publication for the profile-22 honest prover.
//!
//! Complete proof attempts and every controlled failure stay on a private
//! side of this state machine.  At the caller-selected public boundary the
//! controller invokes exactly one channel operation with either proof bytes
//! or one undifferentiated abort symbol.  It never sends a retry count,
//! failure reason, progress event, partial proof, root, nonce, or checkpoint.
//!
//! The wallet is responsible for making this channel the *only* externally
//! observable interface of the worker and for invoking `release` at the
//! selected boundary.  The clock prevents early publication; it cannot make
//! a late caller run in the past, so late invocation belongs in the caller's
//! `epsilon_side` timing model.  This module neither claims nor
//! provides protection against local hardware, scheduler, filesystem, power,
//! or process side channels.  In particular, the attempt worker and durable
//! nonce ledger must remain local and must not emit their own telemetry.

use std::thread;
use std::time::{Duration, SystemTime};

use crate::state_only_good22::Profile22AttemptsExhausted;
use crate::state_only_profile22::Profile22FirstGoodCandidate;

/// The complete public result released at the configured boundary.
///
/// `Abort` deliberately has no payload.  In particular there is no retry
/// count, timing class, rank failure, entropy error, build error, or PoW
/// error for a channel implementation to serialize.
#[derive(Debug, PartialEq, Eq)]
pub enum Profile22PublicRelease {
    Proof(Vec<u8>),
    Abort,
}

/// Injectable clock used by the fixed-release state machine.
///
/// Implementations must make `wait_until` return only once `now() >= target`.
/// The production implementation below uses wall-clock `SystemTime`; tests
/// use a deterministic logical clock.
pub trait Profile22ReleaseClock {
    type Instant: Copy + Ord;

    fn now(&self) -> Self::Instant;
    fn wait_until(&mut self, target: Self::Instant);
}

/// The sole public output edge of the controller.
///
/// This operation is intentionally infallible at the interface boundary.  A
/// concrete wallet channel must internally define what publishing means and
/// must not turn transport-specific error details into a second public event.
pub trait Profile22ReleaseChannel {
    fn publish(&mut self, release: Profile22PublicRelease);
}

/// Production wall clock for a caller-selected public `SystemTime` epoch.
///
/// Waiting in short chunks avoids assuming that the wall clock cannot be
/// adjusted while an attempt is running.  OS wake-up jitter is not hidden or
/// bounded by this type and is outside the theorem claimed by this module.
#[derive(Clone, Copy, Debug, Default)]
pub struct Profile22SystemReleaseClock;

impl Profile22ReleaseClock for Profile22SystemReleaseClock {
    type Instant = SystemTime;

    fn now(&self) -> Self::Instant {
        SystemTime::now()
    }

    fn wait_until(&mut self, target: Self::Instant) {
        const MAX_SLEEP: Duration = Duration::from_millis(250);
        loop {
            let Ok(remaining) = target.duration_since(SystemTime::now()) else {
                break;
            };
            if remaining.is_zero() {
                break;
            }
            thread::sleep(remaining.min(MAX_SLEEP));
        }
    }
}

pub(crate) trait FixedReleaseCandidate: Sized {
    fn production_ready(&self) -> bool;
    fn scrub(&mut self);
    fn into_public_bytes(self) -> Vec<u8>;
}

impl FixedReleaseCandidate for Profile22FirstGoodCandidate {
    fn production_ready(&self) -> bool {
        Profile22FirstGoodCandidate::production_ready(self)
    }

    fn scrub(&mut self) {
        Profile22FirstGoodCandidate::scrub(self);
    }

    fn into_public_bytes(self) -> Vec<u8> {
        self.into_released_bytes()
    }
}

pub(crate) enum FixedReleaseState<C> {
    Waiting,
    Proof(C),
    Abort,
    Released,
}

pub(crate) struct FixedReleaseCore<I, C>
where
    I: Copy + Ord,
    C: FixedReleaseCandidate,
{
    boundary: I,
    state: FixedReleaseState<C>,
}

impl<I, C> FixedReleaseCore<I, C>
where
    I: Copy + Ord,
    C: FixedReleaseCandidate,
{
    pub(crate) fn new(boundary: I) -> Self {
        Self {
            boundary,
            state: FixedReleaseState::Waiting,
        }
    }

    /// Record one private worker completion.  The public-boundary timer wins
    /// an exact timestamp tie: only `completed_at < boundary` is eligible.
    /// A completion at/after the boundary, a duplicate completion, or a
    /// non-production candidate is scrubbed and can only produce the same
    /// abort.
    pub(crate) fn record_completion<E>(&mut self, completed_at: I, completion: Result<C, E>) {
        let before_boundary = completed_at < self.boundary;
        match completion {
            Ok(candidate)
                if before_boundary
                    && matches!(self.state, FixedReleaseState::Waiting)
                    && candidate.production_ready() =>
            {
                self.state = FixedReleaseState::Proof(candidate);
            }
            Ok(mut candidate) => {
                candidate.scrub();
                if before_boundary && matches!(self.state, FixedReleaseState::Waiting) {
                    self.state = FixedReleaseState::Abort;
                }
            }
            Err(_) => {
                if before_boundary && matches!(self.state, FixedReleaseState::Waiting) {
                    self.state = FixedReleaseState::Abort;
                }
            }
        }
    }

    pub(crate) fn release<CLOCK, CHANNEL>(
        mut self,
        clock: &mut CLOCK,
        channel: &mut CHANNEL,
    ) -> Profile22ReleaseComplete
    where
        CLOCK: Profile22ReleaseClock<Instant = I>,
        CHANNEL: Profile22ReleaseChannel,
    {
        clock.wait_until(self.boundary);
        assert!(
            clock.now() >= self.boundary,
            "Profile22ReleaseClock violated wait_until contract"
        );

        // Mark the controller released before entering caller channel code.
        // Consuming `self` also makes a second publication impossible through
        // the safe API, even if the channel retains the payload.
        let state = core::mem::replace(&mut self.state, FixedReleaseState::Released);
        let release = match state {
            FixedReleaseState::Proof(candidate) => {
                Profile22PublicRelease::Proof(candidate.into_public_bytes())
            }
            FixedReleaseState::Waiting | FixedReleaseState::Abort => Profile22PublicRelease::Abort,
            FixedReleaseState::Released => unreachable!("consumed controller released twice"),
        };
        channel.publish(release);
        Profile22ReleaseComplete(())
    }
}

impl<I, C> Drop for FixedReleaseCore<I, C>
where
    I: Copy + Ord,
    C: FixedReleaseCandidate,
{
    fn drop(&mut self) {
        if let FixedReleaseState::Proof(candidate) = &mut self.state {
            candidate.scrub();
        }
    }
}

/// Sealed production controller around the profile-22 first-good result.
///
/// Construct this before starting the private attempt worker.  The wallet's
/// private event loop calls `record_first_good_completion` if that worker
/// finishes.  Independently, its public-boundary event calls `release`, which
/// consumes the controller and performs exactly one channel invocation.  If
/// no valid mined proof is buffered by then, the invocation is `Abort`.
///
/// The first-good builder remains
/// `build_hiding_atomic_state_only_profile22_first_good_v3`; this wrapper does
/// not alter its transcript, proof bytes, verifier, or CU.
pub struct Profile22FixedReleaseController<I>
where
    I: Copy + Ord,
{
    core: FixedReleaseCore<I, Profile22FirstGoodCandidate>,
}

impl<I> Profile22FixedReleaseController<I>
where
    I: Copy + Ord,
{
    pub fn new(boundary: I) -> Self {
        Self {
            core: FixedReleaseCore::new(boundary),
        }
    }

    /// Buffer a completed first-good result without producing public output.
    /// The completion timestamp comes from the injected clock, not from the
    /// attempt worker or its proof.
    pub fn record_first_good_completion<CLOCK>(
        &mut self,
        clock: &CLOCK,
        completion: Result<Profile22FirstGoodCandidate, Profile22AttemptsExhausted>,
    ) where
        CLOCK: Profile22ReleaseClock<Instant = I>,
    {
        self.core.record_completion(clock.now(), completion);
    }

    /// Wait for the configured boundary and publish exactly one proof/abort
    /// outcome.  Consuming the controller prevents a second release.
    ///
    /// The wallet must invoke this method on its boundary event.  This method
    /// prevents publication before the selected instant, but a late call
    /// publishes late; that scheduler delay belongs in the wallet's
    /// `epsilon_side` model.  An exact completion/boundary tie deterministically
    /// releases `Abort` because the boundary event wins.
    pub fn release<CLOCK, CHANNEL>(
        self,
        clock: &mut CLOCK,
        channel: &mut CHANNEL,
    ) -> Profile22ReleaseComplete
    where
        CLOCK: Profile22ReleaseClock<Instant = I>,
        CHANNEL: Profile22ReleaseChannel,
    {
        self.core.release(clock, channel)
    }
}

/// Opaque success token: it contains neither the selected branch nor any
/// retry/failure detail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile22ReleaseComplete(());

#[cfg(test)]
mod tests {
    use std::cell::{Cell, RefCell};
    use std::rc::Rc;

    use super::*;
    use crate::state_only_good22::{
        run_profile22_first_good, PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS,
    };

    #[derive(Clone)]
    struct TestCandidate {
        private_attempt: usize,
        public_bytes: Vec<u8>,
        ready: bool,
        scrub_count: Rc<Cell<usize>>,
    }

    impl FixedReleaseCandidate for TestCandidate {
        fn production_ready(&self) -> bool {
            self.ready
        }

        fn scrub(&mut self) {
            self.public_bytes.fill(0);
            self.private_attempt = 0;
            self.scrub_count.set(self.scrub_count.get() + 1);
        }

        fn into_public_bytes(mut self) -> Vec<u8> {
            let bytes = core::mem::take(&mut self.public_bytes);
            self.scrub();
            bytes
        }
    }

    #[derive(Clone)]
    struct TestClock {
        now: Rc<Cell<u64>>,
        waits: Rc<RefCell<Vec<u64>>>,
    }

    impl TestClock {
        fn new(now: u64) -> Self {
            Self {
                now: Rc::new(Cell::new(now)),
                waits: Rc::new(RefCell::new(Vec::new())),
            }
        }

        fn set(&self, now: u64) {
            self.now.set(now);
        }
    }

    impl Profile22ReleaseClock for TestClock {
        type Instant = u64;

        fn now(&self) -> Self::Instant {
            self.now.get()
        }

        fn wait_until(&mut self, target: Self::Instant) {
            self.waits.borrow_mut().push(target);
            self.now.set(self.now.get().max(target));
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    enum PublicTraceEntry {
        Proof { at: u64, bytes: Vec<u8> },
        Abort { at: u64 },
    }

    struct TestChannel {
        now: Rc<Cell<u64>>,
        trace: Vec<PublicTraceEntry>,
    }

    impl TestChannel {
        fn for_clock(clock: &TestClock) -> Self {
            Self {
                now: Rc::clone(&clock.now),
                trace: Vec::new(),
            }
        }
    }

    impl Profile22ReleaseChannel for TestChannel {
        fn publish(&mut self, release: Profile22PublicRelease) {
            let at = self.now.get();
            self.trace.push(match release {
                Profile22PublicRelease::Proof(bytes) => PublicTraceEntry::Proof { at, bytes },
                Profile22PublicRelease::Abort => PublicTraceEntry::Abort { at },
            });
        }
    }

    fn candidate(attempt: usize, scrub_count: &Rc<Cell<usize>>) -> TestCandidate {
        TestCandidate {
            private_attempt: attempt,
            // The test intentionally holds the public payload fixed so any
            // differing channel shape would be retry-index leakage.
            public_bytes: vec![0x22, 0x16],
            ready: true,
            scrub_count: Rc::clone(scrub_count),
        }
    }

    fn release_trace(
        completion: Result<TestCandidate, Profile22AttemptsExhausted>,
        completion_at: u64,
    ) -> Vec<PublicTraceEntry> {
        let mut core = FixedReleaseCore::new(1_000);
        core.record_completion(completion_at, completion);
        let mut clock = TestClock::new(0);
        let mut channel = TestChannel::for_clock(&clock);
        core.release(&mut clock, &mut channel);
        assert_eq!(&*clock.waits.borrow(), &[1_000]);
        channel.trace
    }

    #[test]
    fn good_attempts_one_through_sixteen_have_one_identical_boundary_release() {
        let expected = vec![PublicTraceEntry::Proof {
            at: 1_000,
            bytes: vec![0x22, 0x16],
        }];

        for selected_attempt in 1..=PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS {
            let scrub_count = Rc::new(Cell::new(0));
            let mut attempt = 0usize;
            let first_good = run_profile22_first_good(
                || {
                    attempt += 1;
                    Ok(attempt)
                },
                |index| Ok(candidate(index, &scrub_count)),
                |candidate| Ok(candidate.private_attempt == selected_attempt),
                |candidate| candidate.scrub(),
            )
            .expect("selected attempt is within the fixed cap");

            let trace = release_trace(Ok(first_good), 100);
            assert_eq!(trace, expected, "selected attempt {selected_attempt}");
            assert_eq!(scrub_count.get(), selected_attempt);
        }
    }

    #[test]
    fn all_bad_and_every_controlled_error_have_the_same_generic_release() {
        let expected = vec![PublicTraceEntry::Abort { at: 1_000 }];

        let mut generated = 0usize;
        let all_bad: Result<TestCandidate, _> = run_profile22_first_good(
            || {
                generated += 1;
                Ok(generated)
            },
            |index| Ok(candidate(index, &Rc::new(Cell::new(0)))),
            |_| Ok(false),
            |candidate| candidate.scrub(),
        );
        assert_eq!(generated, PROFILE22_GOOD_SCHEDULE_MAX_ATTEMPTS);
        assert_eq!(release_trace(all_bad, 100), expected);

        let generation_error: Result<TestCandidate, _> = run_profile22_first_good(
            || -> Result<usize, ()> { Err(()) },
            |_: usize| unreachable!(),
            |_| unreachable!(),
            |_| {},
        );
        assert_eq!(release_trace(generation_error, 100), expected);

        let build_error: Result<TestCandidate, _> =
            run_profile22_first_good(|| Ok(1usize), |_| Err(()), |_| Ok(true), |_| {});
        assert_eq!(release_trace(build_error, 100), expected);

        let decision_scrubs = Rc::new(Cell::new(0));
        let decision_error = run_profile22_first_good(
            || Ok(1usize),
            |index| Ok(candidate(index, &decision_scrubs)),
            |_| Err(()),
            |candidate| candidate.scrub(),
        );
        assert_eq!(release_trace(decision_error, 100), expected);
        assert_eq!(decision_scrubs.get(), 1);
    }

    #[test]
    fn early_completion_wins_but_exact_and_late_completion_abort() {
        let early_scrubs = Rc::new(Cell::new(0));
        assert_eq!(
            release_trace(Ok(candidate(1, &early_scrubs)), 999),
            vec![PublicTraceEntry::Proof {
                at: 1_000,
                bytes: vec![0x22, 0x16],
            }]
        );

        let exact_scrubs = Rc::new(Cell::new(0));
        assert_eq!(
            release_trace(Ok(candidate(1, &exact_scrubs)), 1_000),
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );
        assert_eq!(exact_scrubs.get(), 1);

        let late_scrubs = Rc::new(Cell::new(0));
        assert_eq!(
            release_trace(Ok(candidate(1, &late_scrubs)), 1_001),
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );
        assert_eq!(late_scrubs.get(), 1);

        let no_completion: Result<TestCandidate, _> = Err(Profile22AttemptsExhausted);
        assert_eq!(
            release_trace(no_completion, 1_001),
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );
    }

    #[test]
    fn non_production_candidate_and_dropped_buffer_are_scrubbed() {
        let not_ready_scrubs = Rc::new(Cell::new(0));
        let mut not_ready = candidate(1, &not_ready_scrubs);
        not_ready.ready = false;
        assert_eq!(
            release_trace(Ok(not_ready), 100),
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );
        assert_eq!(not_ready_scrubs.get(), 1);

        let dropped_scrubs = Rc::new(Cell::new(0));
        {
            let mut core = FixedReleaseCore::new(1_000);
            core.record_completion(
                100,
                Ok::<TestCandidate, Profile22AttemptsExhausted>(candidate(1, &dropped_scrubs)),
            );
        }
        assert_eq!(dropped_scrubs.get(), 1);
    }

    #[test]
    fn injected_clock_records_completion_time_and_channel_sees_only_boundary() {
        // Exercise the public clock-driven shape with the generic core.  The
        // production wrapper differs only in its sealed proof candidate type.
        let scrubs = Rc::new(Cell::new(0));
        let mut core = FixedReleaseCore::new(50);
        let mut clock = TestClock::new(7);
        core.record_completion(
            clock.now(),
            Ok::<TestCandidate, Profile22AttemptsExhausted>(candidate(3, &scrubs)),
        );
        clock.set(11);
        let mut channel = TestChannel::for_clock(&clock);
        core.release(&mut clock, &mut channel);
        assert_eq!(
            channel.trace,
            vec![PublicTraceEntry::Proof {
                at: 50,
                bytes: vec![0x22, 0x16],
            }]
        );
    }
}
