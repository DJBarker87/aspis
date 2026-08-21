use super::adapter_selected_circle_fiber_points_shared;
use aspis_core::circle_fri::{
    selected_circle_fiber_points_shared, BaseCirclePoint, CircleFriError,
};

const RELEASED_QUERY_COUNT: usize = 18;
const RELEASED_LAYER0_QUERY_COUNT: usize = 1 << 17;

fn arbitrary_released_queries() -> [u32; RELEASED_QUERY_COUNT] {
    let queries: [u32; RELEASED_QUERY_COUNT] = kani::any();
    let mut index = 0usize;
    while index < queries.len() {
        kani::assume(queries[index] < RELEASED_LAYER0_QUERY_COUNT as u32);
        if index > 0 {
            kani::assume(queries[index - 1] < queries[index]);
        }
        index += 1;
    }
    queries
}

/// Exact point calculation for one arbitrary released fiber.
#[kani::proof]
#[kani::unwind(20)]
fn released_single_circle_point_is_valid_and_equal() {
    let fiber: u32 = kani::any();
    kani::assume(fiber < RELEASED_LAYER0_QUERY_COUNT as u32);
    let fibers = [fiber];
    let production = selected_circle_fiber_points_shared(19, &fibers);
    let (adapter, valid) = adapter_selected_circle_fiber_points_shared(19, &fibers);

    assert!(valid && production == Ok(adapter));
}

fn released_selected_point_observation() -> (
    Result<Vec<BaseCirclePoint>, CircleFriError>,
    Vec<BaseCirclePoint>,
    bool,
) {
    let queries = arbitrary_released_queries();
    let production = selected_circle_fiber_points_shared(19, &queries);
    let (adapter, valid) = adapter_selected_circle_fiber_points_shared(19, &queries);
    (production, adapter, valid)
}

/// Both implementations accept and return exactly 18 points.
#[kani::proof]
#[kani::unwind(20)]
fn released_selected_circle_point_shapes_are_exact() {
    let (production, adapter, valid) = released_selected_point_observation();
    let production_shape_is_exact = match &production {
        Ok(points) => points.len() == RELEASED_QUERY_COUNT,
        Err(_) => false,
    };
    assert!(valid && production_shape_is_exact && adapter.len() == RELEASED_QUERY_COUNT);
}

/// Direct equality at each position of both unchanged 18-point functions.
/// Each assertion is selected as a separate CBMC property during replay.
#[kani::proof]
#[kani::unwind(20)]
fn released_selected_circle_points_equal_at_each_ordinal() {
    let (production, adapter, valid) = released_selected_point_observation();
    kani::assume(valid && production.is_ok());
    let production = production.unwrap();
    kani::assume(production.len() == RELEASED_QUERY_COUNT && adapter.len() == RELEASED_QUERY_COUNT);

    assert_eq!(production[0], adapter[0]);
    assert_eq!(production[1], adapter[1]);
    assert_eq!(production[2], adapter[2]);
    assert_eq!(production[3], adapter[3]);
    assert_eq!(production[4], adapter[4]);
    assert_eq!(production[5], adapter[5]);
    assert_eq!(production[6], adapter[6]);
    assert_eq!(production[7], adapter[7]);
    assert_eq!(production[8], adapter[8]);
    assert_eq!(production[9], adapter[9]);
    assert_eq!(production[10], adapter[10]);
    assert_eq!(production[11], adapter[11]);
    assert_eq!(production[12], adapter[12]);
    assert_eq!(production[13], adapter[13]);
    assert_eq!(production[14], adapter[14]);
    assert_eq!(production[15], adapter[15]);
    assert_eq!(production[16], adapter[16]);
    assert_eq!(production[17], adapter[17]);
}
