use std::{env, fs, path::PathBuf};

const P: u64 = 2_147_483_647;
const CIRCLE_LOG_ORDER: u32 = 31;
const CIRCLE_MASK: u64 = (1u64 << CIRCLE_LOG_ORDER) - 1;

#[derive(Clone, Copy)]
struct Point {
    x: u64,
    y: u64,
}

fn add(a: Point, b: Point) -> Point {
    Point {
        x: (a.x * b.x + P - a.y * b.y % P) % P,
        y: (a.x * b.y + a.y * b.x) % P,
    }
}

fn pow(mut point: Point, mut exponent: u64) -> Point {
    let mut result = Point { x: 1, y: 0 };
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = add(result, point);
        }
        point = add(point, point);
        exponent >>= 1;
    }
    result
}

fn inverse(mut value: u64) -> u32 {
    let mut exponent = P - 2;
    let mut result = 1u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result * value % P;
        }
        value = value * value % P;
        exponent >>= 1;
    }
    result as u32
}

fn bit_reverse(index: usize, log_size: u32) -> usize {
    index.reverse_bits() >> (usize::BITS - log_size)
}

fn initial(log_size: u32) -> u64 {
    1u64 << (CIRCLE_LOG_ORDER - (log_size + 2))
}

fn step(log_size: u32) -> u64 {
    1u64 << (CIRCLE_LOG_ORDER - log_size)
}

fn group_point(exponent: u64) -> Point {
    pow(
        Point {
            x: 2,
            y: 1_268_011_823,
        },
        exponent & CIRCLE_MASK,
    )
}

fn circle_point(log_size: u32, stored_index: usize) -> Point {
    let natural = bit_reverse(stored_index, log_size);
    let half_size = 1usize << (log_size - 1);
    let (index, conjugate) = if natural < half_size {
        (natural, false)
    } else {
        (natural - half_size, true)
    };
    let mut point = group_point(initial(log_size - 1) + step(log_size - 1) * index as u64);
    if conjugate && point.y != 0 {
        point.y = P - point.y;
    }
    point
}

fn line_x(log_size: u32, stored_index: usize) -> u64 {
    let natural = bit_reverse(stored_index, log_size);
    group_point(initial(log_size) + step(log_size) * natural as u64).x
}

fn write_array(output: &mut String, name: &str, values: &[u32]) {
    output.push_str(&format!("pub const {name}: [u32; {}] = [\n", values.len()));
    for chunk in values.chunks(12) {
        output.push_str("    ");
        for value in chunk {
            output.push_str(&format!("{value},"));
        }
        output.push('\n');
    }
    output.push_str("];\n");
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let mut output = String::new();
    for (domain_log_size, prefix) in [
        (12u32, "FIXED"),
        (14u32, "RATE16"),
        (15u32, "RATE32"),
        (19u32, "RATE512"),
    ] {
        let fiber_count = 1usize << (domain_log_size - 2);
        let mut circle_x = Vec::with_capacity(fiber_count);
        let mut circle_y = Vec::with_capacity(fiber_count);
        for fiber in 0..fiber_count {
            let point = circle_point(domain_log_size, 4 * fiber);
            circle_x.push(inverse(2 * point.x % P));
            circle_y.push(inverse(2 * point.y % P));
        }

        let mut later = [Vec::new(), Vec::new(), Vec::new()];
        for (layer, values) in later.iter_mut().enumerate() {
            let log_size = domain_log_size - 2 - 2 * layer as u32;
            let fibers = (1usize << log_size) / 4;
            for fiber in 0..fibers {
                values.push(inverse(2 * line_x(log_size, 4 * fiber) % P));
                values.push(inverse(2 * line_x(log_size, 4 * fiber + 2) % P));
                values.push(inverse(2 * line_x(log_size - 1, 2 * fiber) % P));
            }
        }
        let final_log_size = domain_log_size - 8;
        let final_x = (0..1usize << final_log_size)
            .map(|index| line_x(final_log_size, index) as u32)
            .collect::<Vec<_>>();

        write_array(&mut output, &format!("{prefix}_CIRCLE_INV_2X"), &circle_x);
        write_array(&mut output, &format!("{prefix}_CIRCLE_INV_2Y"), &circle_y);
        write_array(&mut output, &format!("{prefix}_LINE1_INV"), &later[0]);
        write_array(&mut output, &format!("{prefix}_LINE2_INV"), &later[1]);
        write_array(&mut output, &format!("{prefix}_LINE3_INV"), &later[2]);
        write_array(&mut output, &format!("{prefix}_FINAL_X"), &final_x);
    }
    let path = PathBuf::from(env::var_os("OUT_DIR").unwrap()).join("circle_tables.rs");
    fs::write(path, output).unwrap();
}
