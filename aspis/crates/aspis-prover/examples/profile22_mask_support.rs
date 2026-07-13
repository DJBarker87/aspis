use aspis_statement::atomic_state_only_registry::atomic_state_only_relation_free_mask_cells_v3;

fn main() {
    let cells = atomic_state_only_relation_free_mask_cells_v3().expect("atomic mask layout");
    let mut rows = vec![Vec::<usize>::new(); 16];
    for cell in cells {
        rows[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, support) in rows.iter().enumerate() {
        let mut intervals = Vec::new();
        let mut start = support[0];
        let mut previous = start;
        for &row in &support[1..] {
            if row != previous + 1 {
                intervals.push((start, previous));
                start = row;
            }
            previous = row;
        }
        intervals.push((start, previous));
        println!(
            "column={column} count={} last_inactive_candidate={} intervals={intervals:?}",
            support.len(),
            support.last().unwrap(),
        );
    }
    let common = (0..1024)
        .filter(|row| {
            rows.iter()
                .all(|support| support.binary_search(row).is_ok())
        })
        .collect::<Vec<_>>();
    let mut intervals = Vec::new();
    if let Some(&first) = common.first() {
        let mut start = first;
        let mut previous = first;
        for &row in &common[1..] {
            if row != previous + 1 {
                intervals.push((start, previous));
                start = row;
            }
            previous = row;
        }
        intervals.push((start, previous));
    }
    println!(
        "common_count={} common_intervals={intervals:?}",
        common.len()
    );
}
