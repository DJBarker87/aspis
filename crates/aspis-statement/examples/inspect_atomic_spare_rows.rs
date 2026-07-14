use aspis_statement::{
    build_state_only_cell_map_v4, merkle_boundary_layout, state_only_required_old_cells_v4,
    TraceCell,
};

fn main() {
    let map = build_state_only_cell_map_v4().unwrap();
    let mut boundary = Vec::new();
    for item in merkle_boundary_layout() {
        boundary.push(map.map(item.path_bit).unwrap());
        for old in item
            .current
            .into_iter()
            .chain(item.left)
            .chain(item.right)
            .chain(item.sibling)
        {
            boundary.push(map.map(old).unwrap());
        }
    }
    let occupied = state_only_required_old_cells_v4()
        .into_iter()
        .filter_map(|cell| map.map(cell))
        .filter(|cell| !boundary.contains(cell))
        .collect::<Vec<TraceCell>>();
    for item in merkle_boundary_layout() {
        let base = map.map(item.path_bit).unwrap().row;
        let row = (base + 1) ^ 12;
        let used = (0..16)
            .filter(|column| {
                occupied.contains(&TraceCell {
                    row,
                    column: *column,
                })
            })
            .collect::<Vec<_>>();
        let free = (0..16)
            .filter(|column| !used.contains(column))
            .collect::<Vec<_>>();
        println!(
            "level={} base={base} spare={row} used={used:?} free={free:?}",
            item.level
        );
    }
}
