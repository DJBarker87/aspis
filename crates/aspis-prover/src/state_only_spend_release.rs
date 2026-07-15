//! Fixed-boundary publication for the production Spend Good worker.
//!
//! Complete proof attempts and every controlled failure stay on the private
//! side of this state machine. At the caller-selected public boundary the
//! controller invokes exactly one channel operation with either proof bytes
//! or one undifferentiated abort symbol: timing, exact-boundary tie
//! handling, single-publication, generic abort, and drop-time scrubbing all
//! live in one generic core. The candidate type is opaque: only the mined
//! cap-17 Good worker can construct it.
//!
//! The wallet is responsible for making this channel the *only* externally
//! observable interface of the worker and for invoking `release` at the
//! selected boundary. The clock prevents early publication; it cannot make
//! a late caller run in the past, so late invocation belongs in the caller's
//! `epsilon_side` timing model. This module neither claims nor provides
//! protection against local hardware, scheduler, filesystem, power, or
//! process side channels.

use std::thread;
use std::time::{Duration, SystemTime};

use crate::state_only_good_spend::SpendAttemptsExhausted;
use crate::state_only_spend::SpendFirstGoodCandidate;

#[derive(Debug, PartialEq, Eq)]
pub enum SpendPublicRelease {
    Proof(Vec<u8>),
    Abort,
}

pub trait SpendReleaseClock {
    type Instant: Copy + Ord;

    fn now(&self) -> Self::Instant;
    fn wait_until(&mut self, target: Self::Instant);
}

pub trait SpendReleaseChannel {
    fn publish(&mut self, release: SpendPublicRelease);
}

#[derive(Clone, Copy, Debug, Default)]
pub struct SpendSystemReleaseClock;

impl SpendReleaseClock for SpendSystemReleaseClock {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendReleaseComplete(());

pub(crate) trait FixedReleaseCandidate: Sized {
    fn production_ready(&self) -> bool;
    fn scrub(&mut self);
    fn into_public_bytes(self) -> Vec<u8>;
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

    pub(crate) fn release<CLOCK, CHANNEL>(mut self, clock: &mut CLOCK, channel: &mut CHANNEL)
    where
        CLOCK: SpendReleaseClock<Instant = I>,
        CHANNEL: SpendReleaseChannel,
    {
        clock.wait_until(self.boundary);
        assert!(
            clock.now() >= self.boundary,
            "SpendReleaseClock violated wait_until contract"
        );

        // Mark the controller released before entering caller channel code.
        // Consuming `self` also makes a second publication impossible through
        // the safe API, even if the channel retains the payload.
        let state = core::mem::replace(&mut self.state, FixedReleaseState::Released);
        let release = match state {
            FixedReleaseState::Proof(candidate) => {
                SpendPublicRelease::Proof(candidate.into_public_bytes())
            }
            FixedReleaseState::Waiting | FixedReleaseState::Abort => SpendPublicRelease::Abort,
            FixedReleaseState::Released => unreachable!("consumed controller released twice"),
        };
        channel.publish(release);
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

impl FixedReleaseCandidate for SpendFirstGoodCandidate {
    fn production_ready(&self) -> bool {
        SpendFirstGoodCandidate::production_ready(self)
    }

    fn scrub(&mut self) {
        SpendFirstGoodCandidate::scrub(self);
    }

    fn into_public_bytes(self) -> Vec<u8> {
        self.into_released_bytes()
    }
}

/// Sealed controller whose only public edge is one proof-or-abort event at
/// the caller-selected boundary. Attempt counts, selectors, Good failures,
/// PoW failures, roots, and partial proofs never cross this boundary.
pub struct SpendFixedReleaseController<I>
where
    I: Copy + Ord,
{
    core: FixedReleaseCore<I, SpendFirstGoodCandidate>,
}

impl<I> SpendFixedReleaseController<I>
where
    I: Copy + Ord,
{
    pub fn new(boundary: I) -> Self {
        Self {
            core: FixedReleaseCore::new(boundary),
        }
    }

    pub fn record_first_good_completion<CLOCK>(
        &mut self,
        clock: &CLOCK,
        completion: Result<SpendFirstGoodCandidate, SpendAttemptsExhausted>,
    ) where
        CLOCK: SpendReleaseClock<Instant = I>,
    {
        self.core.record_completion(clock.now(), completion);
    }

    pub fn release<CLOCK, CHANNEL>(
        self,
        clock: &mut CLOCK,
        channel: &mut CHANNEL,
    ) -> SpendReleaseComplete
    where
        CLOCK: SpendReleaseClock<Instant = I>,
        CHANNEL: SpendReleaseChannel,
    {
        self.core.release(clock, channel);
        SpendReleaseComplete(())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::{Cell, RefCell};
    use std::rc::Rc;

    use super::*;

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

    impl SpendReleaseClock for TestClock {
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

    impl SpendReleaseChannel for TestChannel {
        fn publish(&mut self, release: SpendPublicRelease) {
            assert!(self.trace.is_empty(), "Spend adapter published twice");
            let at = self.now.get();
            self.trace.push(match release {
                SpendPublicRelease::Proof(bytes) => PublicTraceEntry::Proof { at, bytes },
                SpendPublicRelease::Abort => PublicTraceEntry::Abort { at },
            });
        }
    }

    fn candidate(
        bytes: &[u8],
        ready: bool,
        scrub_count: &Rc<Cell<usize>>,
    ) -> SpendFirstGoodCandidate {
        SpendFirstGoodCandidate::synthetic_release_test(
            bytes.to_vec(),
            ready,
            Rc::clone(scrub_count),
        )
    }

    #[test]
    fn early_ready_completion_releases_one_proof_at_the_boundary_and_scrubs() {
        let scrub_count = Rc::new(Cell::new(0));
        let mut controller = SpendFixedReleaseController::new(1_000);
        let mut clock = TestClock::new(100);
        let mut channel = TestChannel::for_clock(&clock);

        controller
            .record_first_good_completion(&clock, Ok(candidate(&[0x23, 0x16], true, &scrub_count)));
        assert!(channel.trace.is_empty());
        assert_eq!(scrub_count.get(), 0);
        let _ = controller.release(&mut clock, &mut channel);

        assert_eq!(&*clock.waits.borrow(), &[1_000]);
        assert_eq!(
            channel.trace,
            vec![PublicTraceEntry::Proof {
                at: 1_000,
                bytes: vec![0x23, 0x16],
            }]
        );
        assert_eq!(scrub_count.get(), 1);
    }

    #[test]
    fn exact_boundary_and_late_completions_abort_and_scrub_candidates() {
        for completed_at in [1_000, 1_001] {
            let scrub_count = Rc::new(Cell::new(0));
            let mut controller = SpendFixedReleaseController::new(1_000);
            let mut clock = TestClock::new(completed_at);
            let mut channel = TestChannel::for_clock(&clock);

            controller
                .record_first_good_completion(&clock, Ok(candidate(&[0x23], true, &scrub_count)));
            assert_eq!(scrub_count.get(), 1);
            let _ = controller.release(&mut clock, &mut channel);

            assert_eq!(
                channel.trace,
                vec![PublicTraceEntry::Abort { at: completed_at }]
            );
            assert_eq!(scrub_count.get(), 1);
        }
    }

    #[test]
    fn no_completion_and_opaque_worker_failure_each_release_one_abort() {
        let empty = SpendFixedReleaseController::new(1_000);
        let mut empty_clock = TestClock::new(0);
        let mut empty_channel = TestChannel::for_clock(&empty_clock);
        let _ = empty.release(&mut empty_clock, &mut empty_channel);
        assert_eq!(
            empty_channel.trace,
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );

        let mut failed = SpendFixedReleaseController::new(1_000);
        let mut failed_clock = TestClock::new(100);
        let mut failed_channel = TestChannel::for_clock(&failed_clock);
        failed.record_first_good_completion(&failed_clock, Err(SpendAttemptsExhausted));
        let _ = failed.release(&mut failed_clock, &mut failed_channel);
        assert_eq!(
            failed_channel.trace,
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );
    }

    #[test]
    fn nonproduction_candidate_is_scrubbed_and_can_only_release_abort() {
        let scrub_count = Rc::new(Cell::new(0));
        let mut controller = SpendFixedReleaseController::new(1_000);
        let mut clock = TestClock::new(100);
        let mut channel = TestChannel::for_clock(&clock);

        controller.record_first_good_completion(
            &clock,
            Ok(candidate(&[0xde, 0xad], false, &scrub_count)),
        );
        assert_eq!(scrub_count.get(), 1);
        let _ = controller.release(&mut clock, &mut channel);

        assert_eq!(channel.trace, vec![PublicTraceEntry::Abort { at: 1_000 }]);
        assert_eq!(scrub_count.get(), 1);
    }

    #[test]
    fn duplicate_completion_scrubs_the_loser_and_publishes_the_first_once() {
        let first_scrubs = Rc::new(Cell::new(0));
        let second_scrubs = Rc::new(Cell::new(0));
        let mut controller = SpendFixedReleaseController::new(1_000);
        let mut clock = TestClock::new(100);
        let mut channel = TestChannel::for_clock(&clock);

        controller
            .record_first_good_completion(&clock, Ok(candidate(&[0x01], true, &first_scrubs)));
        clock.set(200);
        controller
            .record_first_good_completion(&clock, Ok(candidate(&[0x02], true, &second_scrubs)));
        assert_eq!(first_scrubs.get(), 0);
        assert_eq!(second_scrubs.get(), 1);

        let _ = controller.release(&mut clock, &mut channel);
        assert_eq!(
            channel.trace,
            vec![PublicTraceEntry::Proof {
                at: 1_000,
                bytes: vec![0x01],
            }]
        );
        assert_eq!(first_scrubs.get(), 1);
        assert_eq!(second_scrubs.get(), 1);
    }

    #[test]
    fn dropping_a_buffered_controller_scrubs_without_publishing() {
        let scrub_count = Rc::new(Cell::new(0));
        let clock = TestClock::new(100);
        let mut controller = SpendFixedReleaseController::new(1_000);
        controller.record_first_good_completion(&clock, Ok(candidate(&[0x23], true, &scrub_count)));
        assert_eq!(scrub_count.get(), 0);
        drop(controller);
        assert_eq!(scrub_count.get(), 1);
    }
}
