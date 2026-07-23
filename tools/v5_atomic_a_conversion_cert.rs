// Read-only certificate emitter for v5 Component A edge (a).
//
// This standalone program RECOMPUTES (it does not import or mutate) the two
// coefficient tables defined in `crates/aspis-prover/src/v5_mask.rs`:
//
//   * `natural_line_basis_polynomials(m)` — coeff of x^j in the natural line
//     basis N_i(x); this is the Lean `naturalCoeffMatrix` (transposed:
//     natLine[i][j] = (naturalLinePoly i).coeff j).
//   * `ordinary_monomials_in_natural_line_basis(m)` — the ordinary->natural
//     conversion actually applied by `m31_block_mask_in_natural_basis`; this is
//     the Lean `monomialToNatural` (= naturalCoeffMatrix^{-1}).
//
// It emits the leading K x K block of `natLine` as a Lean `List (List ℕ)`
// literal (canonical residues mod P = 2^31 - 1) so the Lean side can kernel-check
// natLine[i][j] = (naturalLinePoly (ZMod P) i).coeff j against the mechanised
// natural basis, entry by entry.  No native_decide is used on the Lean side; the
// block size is bounded by in-kernel Chebyshev tractability, reported honestly.
//
// It is NOT wired into any Cargo build (top-level tools/ is not a workspace
// member).  Build & run:
//   rustc -O tools/v5_atomic_a_conversion_cert.rs -o /tmp/cert && /tmp/cert 8

const P: u64 = (1 << 31) - 1; // M31 prime 2^31 - 1

#[inline]
fn add(a: u64, b: u64) -> u64 { (a + b) % P }
#[inline]
fn sub(a: u64, b: u64) -> u64 { (a + P - b % P) % P }
#[inline]
fn mul(a: u64, b: u64) -> u64 { (a * b) % P }
#[inline]
fn double(a: u64) -> u64 { add(a, a) }

fn pow(mut a: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    a %= P;
    while e > 0 {
        if e & 1 == 1 { r = mul(r, a); }
        a = mul(a, a);
        e >>= 1;
    }
    r
}
#[inline]
fn inv(a: u64) -> u64 { pow(a, P - 2) } // Fermat inverse

// Faithful re-implementation of `natural_line_basis_polynomials`.
fn natural_line_basis_polynomials(size: usize) -> Vec<Vec<u64>> {
    let log_size = (usize::BITS - (size - 1).leading_zeros()) as usize;
    let mut factors: Vec<Vec<u64>> = Vec::with_capacity(log_size);
    factors.push(vec![0, 1]); // x
    for bit in 1..log_size {
        let previous = factors[bit - 1].clone();
        let mut squared = vec![0u64; 2 * previous.len() - 1];
        for (l, &a) in previous.iter().enumerate() {
            for (r, &b) in previous.iter().enumerate() {
                squared[l + r] = add(squared[l + r], mul(a, b));
            }
        }
        for v in squared.iter_mut() { *v = double(*v); }
        squared[0] = sub(squared[0], 1);
        factors.push(squared);
    }
    let mut basis: Vec<Vec<u64>> = Vec::with_capacity(size);
    basis.push(vec![1]);
    for index in 1..size {
        let bit = index.trailing_zeros() as usize;
        let prefix = basis[index ^ (1usize << bit)].clone();
        let factor = &factors[bit];
        let mut poly = vec![0u64; prefix.len() + factor.len() - 1];
        for (l, &a) in prefix.iter().enumerate() {
            for (r, &b) in factor.iter().enumerate() {
                poly[l + r] = add(poly[l + r], mul(a, b));
            }
        }
        basis.push(poly);
    }
    basis
}

// Faithful re-implementation of `ordinary_monomials_in_natural_line_basis`.
fn ordinary_monomials_in_natural_line_basis(size: usize) -> Vec<Vec<u64>> {
    let basis = natural_line_basis_polynomials(size);
    (0..size)
        .map(|degree| {
            let mut residual = vec![0u64; size];
            residual[degree] = 1;
            let mut coefficients = vec![0u64; size];
            for pivot in (0..=degree).rev() {
                let diagonal = basis[pivot][pivot];
                let scale = mul(residual[pivot], inv(diagonal));
                coefficients[pivot] = scale;
                for (monomial, &value) in basis[pivot].iter().enumerate() {
                    residual[monomial] = sub(residual[monomial], mul(scale, value));
                }
            }
            assert!(residual.iter().all(|&v| v == 0), "residual nonzero at degree {degree}");
            coefficients
        })
        .collect()
}

// Cross-check: Conv * NatCoeffMatrix = I  (over M31), a Rust-internal audit.
fn verify_mutual_inverse(size: usize) {
    let basis = natural_line_basis_polynomials(size); // natLine[i][j] = coeff x^j of N_i
    let conv = ordinary_monomials_in_natural_line_basis(size); // conv[degree][idx]
    // natural[idx] = sum_degree ordinary[degree]*conv[degree][idx]; reconstruct monomial.
    // Check: for each degree, sum_idx conv[degree][idx]*N_idx == x^degree.
    for degree in 0..size {
        let mut recon = vec![0u64; size];
        for idx in 0..size {
            let w = conv[degree][idx];
            for (mono, &coeff) in basis[idx].iter().enumerate() {
                recon[mono] = add(recon[mono], mul(w, coeff));
            }
        }
        for mono in 0..size {
            let expect = if mono == degree { 1 } else { 0 };
            assert_eq!(recon[mono], expect, "inverse check failed at ({degree},{mono})");
        }
    }
    eprintln!("[ok] Conv is the exact inverse of the natural-basis coeff matrix for size {size}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(8);
    let full = 48usize;
    verify_mutual_inverse(full);

    let basis = natural_line_basis_polynomials(full);

    // Emit the leading k x k block of natLine[i][j] (j = monomial degree),
    // padded with zeros to width k, as a Lean List (List Nat) literal.
    println!("-- AUTO-EMITTED by tools/v5_atomic_a_conversion_cert.rs (recompute; read-only)");
    println!("-- natLineCoeff[i]! j = (naturalLinePoly (ZMod P) i).coeff j, i,j < {k}");
    println!("def natLineCoeffLit : List (List Nat) := [");
    for i in 0..k {
        let mut row = vec![0u64; k];
        for (j, &c) in basis[i].iter().enumerate() {
            if j < k { row[j] = c; }
        }
        let entries: Vec<String> = row.iter().map(|v| v.to_string()).collect();
        let comma = if i + 1 < k { "," } else { "" };
        println!("  [{}]{}", entries.join(", "), comma);
    }
    println!("]");

    // Also dump the full 48x48 natLine and conv tables to stderr for provenance.
    eprintln!("--- full natural_line_basis_polynomials(48) (row i = N_i coeffs) ---");
    for (i, row) in basis.iter().enumerate() {
        eprintln!("N_{i}: {:?}", row);
    }
}
