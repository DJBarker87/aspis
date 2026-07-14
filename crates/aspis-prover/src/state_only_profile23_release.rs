//! Fixed-boundary publication for the production Profile23 Good worker.
//!
//! The common controller is shared with Profile22 so timing, exact-boundary
//! tie handling, single-publication, generic abort, and drop-time scrubbing
//! have one implementation. The candidate type remains distinct and opaque:
//! only the mined cap-17 Good23 worker can construct it. Profile23 exposes
//! distinct channel/result types so a wallet cannot accidentally route its
//! proof through a Profile22-tagged publication edge.

use std::thread;
use std::time::{Duration, SystemTime};

use crate::state_only_good23::Profile23AttemptsExhausted;
use crate::state_only_profile22_release::{
    FixedReleaseCandidate, FixedReleaseCore, Profile22PublicRelease, Profile22ReleaseChannel,
    Profile22ReleaseClock,
};
use crate::state_only_profile23::Profile23FirstGoodCandidate;

#[derive(Debug, PartialEq, Eq)]
pub enum Profile23PublicRelease {
    Proof(Vec<u8>),
    Abort,
}

pub trait Profile23ReleaseClock {
    type Instant: Copy + Ord;

    fn now(&self) -> Self::Instant;
    fn wait_until(&mut self, target: Self::Instant);
}

pub trait Profile23ReleaseChannel {
    fn publish(&mut self, release: Profile23PublicRelease);
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Profile23SystemReleaseClock;

impl Profile23ReleaseClock for Profile23SystemReleaseClock {
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
pub struct Profile23ReleaseComplete(());

struct ClockAdapter<'a, C>(&'a mut C);

impl<C> Profile22ReleaseClock for ClockAdapter<'_, C>
where
    C: Profile23ReleaseClock,
{
    type Instant = C::Instant;

    fn now(&self) -> Self::Instant {
        self.0.now()
    }

    fn wait_until(&mut self, target: Self::Instant) {
        self.0.wait_until(target);
    }
}

struct ChannelAdapter<'a, C>(&'a mut C);

impl<C> Profile22ReleaseChannel for ChannelAdapter<'_, C>
where
    C: Profile23ReleaseChannel,
{
    fn publish(&mut self, release: Profile22PublicRelease) {
        self.0.publish(match release {
            Profile22PublicRelease::Proof(proof) => Profile23PublicRelease::Proof(proof),
            Profile22PublicRelease::Abort => Profile23PublicRelease::Abort,
        });
    }
}

impl FixedReleaseCandidate for Profile23FirstGoodCandidate {
    fn production_ready(&self) -> bool {
        Profile23FirstGoodCandidate::production_ready(self)
    }

    fn scrub(&mut self) {
        Profile23FirstGoodCandidate::scrub(self);
    }

    fn into_public_bytes(self) -> Vec<u8> {
        self.into_released_bytes()
    }
}

/// Sealed controller whose only public edge is one proof-or-abort event at
/// the caller-selected boundary. Attempt counts, selectors, Good failures,
/// PoW failures, roots, and partial proofs never cross this boundary.
pub struct Profile23FixedReleaseController<I>
where
    I: Copy + Ord,
{
    core: FixedReleaseCore<I, Profile23FirstGoodCandidate>,
}

impl<I> Profile23FixedReleaseController<I>
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
        completion: Result<Profile23FirstGoodCandidate, Profile23AttemptsExhausted>,
    ) where
        CLOCK: Profile23ReleaseClock<Instant = I>,
    {
        self.core.record_completion(clock.now(), completion);
    }

    pub fn release<CLOCK, CHANNEL>(
        self,
        clock: &mut CLOCK,
        channel: &mut CHANNEL,
    ) -> Profile23ReleaseComplete
    where
        CLOCK: Profile23ReleaseClock<Instant = I>,
        CHANNEL: Profile23ReleaseChannel,
    {
        let mut clock = ClockAdapter(clock);
        let mut channel = ChannelAdapter(channel);
        let _ = self.core.release(&mut clock, &mut channel);
        Profile23ReleaseComplete(())
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

    impl Profile23ReleaseClock for TestClock {
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

    impl Profile23ReleaseChannel for TestChannel {
        fn publish(&mut self, release: Profile23PublicRelease) {
            assert!(self.trace.is_empty(), "Profile23 adapter published twice");
            let at = self.now.get();
            self.trace.push(match release {
                Profile23PublicRelease::Proof(bytes) => PublicTraceEntry::Proof { at, bytes },
                Profile23PublicRelease::Abort => PublicTraceEntry::Abort { at },
            });
        }
    }

    fn candidate(
        bytes: &[u8],
        ready: bool,
        scrub_count: &Rc<Cell<usize>>,
    ) -> Profile23FirstGoodCandidate {
        Profile23FirstGoodCandidate::synthetic_release_test(
            bytes.to_vec(),
            ready,
            Rc::clone(scrub_count),
        )
    }

    #[test]
    fn early_ready_completion_releases_one_proof_at_the_boundary_and_scrubs() {
        let scrub_count = Rc::new(Cell::new(0));
        let mut controller = Profile23FixedReleaseController::new(1_000);
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
            let mut controller = Profile23FixedReleaseController::new(1_000);
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
        let empty = Profile23FixedReleaseController::new(1_000);
        let mut empty_clock = TestClock::new(0);
        let mut empty_channel = TestChannel::for_clock(&empty_clock);
        let _ = empty.release(&mut empty_clock, &mut empty_channel);
        assert_eq!(
            empty_channel.trace,
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );

        let mut failed = Profile23FixedReleaseController::new(1_000);
        let mut failed_clock = TestClock::new(100);
        let mut failed_channel = TestChannel::for_clock(&failed_clock);
        failed.record_first_good_completion(&failed_clock, Err(Profile23AttemptsExhausted));
        let _ = failed.release(&mut failed_clock, &mut failed_channel);
        assert_eq!(
            failed_channel.trace,
            vec![PublicTraceEntry::Abort { at: 1_000 }]
        );
    }

    #[test]
    fn nonproduction_candidate_is_scrubbed_and_can_only_release_abort() {
        let scrub_count = Rc::new(Cell::new(0));
        let mut controller = Profile23FixedReleaseController::new(1_000);
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
        let mut controller = Profile23FixedReleaseController::new(1_000);
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
        let mut controller = Profile23FixedReleaseController::new(1_000);
        controller.record_first_good_completion(&clock, Ok(candidate(&[0x23], true, &scrub_count)));
        assert_eq!(scrub_count.get(), 0);
        drop(controller);
        assert_eq!(scrub_count.get(), 1);
    }
}
