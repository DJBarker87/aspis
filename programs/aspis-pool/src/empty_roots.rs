//! Pinned Pool V1 recursive empty roots.
//!
//! The permanent host KAT compares every entry to recursive construction via
//! `aspis_statement::pool_v1_empty_roots()`.

use aspis_core::field::M31;
use aspis_statement::poseidon2::{Digest, DIGEST_ELEMS};

use aspis_statement::pool_v1::POOL_V1_TREE_DEPTH;

pub const POOL_V1_EMPTY_ROOTS: [Digest; POOL_V1_TREE_DEPTH + 1] = [
    [M31::ZERO; DIGEST_ELEMS],
    [
        M31(1438900896),
        M31(782233260),
        M31(1544844157),
        M31(891350894),
        M31(986827501),
        M31(300047813),
        M31(266092546),
        M31(1155026732),
    ],
    [
        M31(141619947),
        M31(1448060902),
        M31(524379093),
        M31(1944458907),
        M31(1832113773),
        M31(579270723),
        M31(752346270),
        M31(1038346536),
    ],
    [
        M31(1119858538),
        M31(128294437),
        M31(939091034),
        M31(659145897),
        M31(1933666768),
        M31(903679201),
        M31(1182639487),
        M31(1398246146),
    ],
    [
        M31(1057897051),
        M31(1132946363),
        M31(794377079),
        M31(1971564389),
        M31(1255722275),
        M31(926653737),
        M31(2031728153),
        M31(2024887573),
    ],
    [
        M31(1410054462),
        M31(673771449),
        M31(940847521),
        M31(274330358),
        M31(1719505495),
        M31(1690439941),
        M31(203201419),
        M31(1855504616),
    ],
    [
        M31(1442759752),
        M31(1540325866),
        M31(188964047),
        M31(101815282),
        M31(1883549730),
        M31(1774537487),
        M31(1306717763),
        M31(561084592),
    ],
    [
        M31(244193611),
        M31(984304317),
        M31(1467689208),
        M31(2063463197),
        M31(1766003332),
        M31(1300835127),
        M31(1578947755),
        M31(745931587),
    ],
    [
        M31(673192756),
        M31(38070812),
        M31(1453532835),
        M31(1340577407),
        M31(368420458),
        M31(1834405704),
        M31(270061815),
        M31(711700631),
    ],
    [
        M31(27092219),
        M31(1272373356),
        M31(998194489),
        M31(1458413288),
        M31(887470405),
        M31(1204987730),
        M31(864453460),
        M31(553704718),
    ],
    [
        M31(1972918328),
        M31(1234090299),
        M31(977162835),
        M31(1704494754),
        M31(1617603773),
        M31(1819200880),
        M31(906453206),
        M31(1653526885),
    ],
    [
        M31(418360492),
        M31(472096212),
        M31(871749117),
        M31(98906847),
        M31(2026788776),
        M31(1504737042),
        M31(407274798),
        M31(1800828893),
    ],
    [
        M31(986339640),
        M31(660349625),
        M31(1012157959),
        M31(454024326),
        M31(987656904),
        M31(622864739),
        M31(1150440730),
        M31(1280042062),
    ],
    [
        M31(2118470693),
        M31(1706590589),
        M31(2128512933),
        M31(167263577),
        M31(409542414),
        M31(1323179656),
        M31(1880070613),
        M31(2053396184),
    ],
    [
        M31(260546973),
        M31(1375125357),
        M31(1584234519),
        M31(1097072342),
        M31(1685367984),
        M31(1070989054),
        M31(2113798037),
        M31(958210542),
    ],
    [
        M31(1239966481),
        M31(992485427),
        M31(1397515674),
        M31(466658549),
        M31(2071909237),
        M31(712995354),
        M31(2047452742),
        M31(1680224983),
    ],
    [
        M31(1796237568),
        M31(1862343136),
        M31(1954463912),
        M31(1190686266),
        M31(364700025),
        M31(46960257),
        M31(671215600),
        M31(1214723477),
    ],
    [
        M31(1127845264),
        M31(662862400),
        M31(84021756),
        M31(995080286),
        M31(1419670571),
        M31(1966281459),
        M31(837284626),
        M31(2083375353),
    ],
    [
        M31(1321679286),
        M31(782621548),
        M31(1415820264),
        M31(74436574),
        M31(776350425),
        M31(323154748),
        M31(429051705),
        M31(1299980413),
    ],
    [
        M31(1519171444),
        M31(1235587172),
        M31(1671492368),
        M31(1449613582),
        M31(547369941),
        M31(1621086153),
        M31(266860322),
        M31(450526803),
    ],
    [
        M31(19381883),
        M31(1308966873),
        M31(251977766),
        M31(474343397),
        M31(2069732268),
        M31(1863820229),
        M31(152153379),
        M31(665567443),
    ],
];

/// Recursive empty roots for the distinct pair-leaf storage format.  A pair
/// leaf's canonical empty value is `H(0, 0)`, hence levels 0 through 19 are
/// exactly ordinary-tree levels 1 through 20.  The last entry is the frozen
/// ordinary level-21 root.
pub const POOL_V1_PAIR_EMPTY_ROOTS: [Digest; POOL_V1_TREE_DEPTH + 1] = [
    POOL_V1_EMPTY_ROOTS[1],
    POOL_V1_EMPTY_ROOTS[2],
    POOL_V1_EMPTY_ROOTS[3],
    POOL_V1_EMPTY_ROOTS[4],
    POOL_V1_EMPTY_ROOTS[5],
    POOL_V1_EMPTY_ROOTS[6],
    POOL_V1_EMPTY_ROOTS[7],
    POOL_V1_EMPTY_ROOTS[8],
    POOL_V1_EMPTY_ROOTS[9],
    POOL_V1_EMPTY_ROOTS[10],
    POOL_V1_EMPTY_ROOTS[11],
    POOL_V1_EMPTY_ROOTS[12],
    POOL_V1_EMPTY_ROOTS[13],
    POOL_V1_EMPTY_ROOTS[14],
    POOL_V1_EMPTY_ROOTS[15],
    POOL_V1_EMPTY_ROOTS[16],
    POOL_V1_EMPTY_ROOTS[17],
    POOL_V1_EMPTY_ROOTS[18],
    POOL_V1_EMPTY_ROOTS[19],
    POOL_V1_EMPTY_ROOTS[20],
    [
        M31(1201428963),
        M31(1296676114),
        M31(441891487),
        M31(1910121140),
        M31(602621674),
        M31(1294160489),
        M31(1878016864),
        M31(855887413),
    ],
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_table_matches_recursive_poseidon_v3_construction() {
        assert_eq!(
            POOL_V1_EMPTY_ROOTS,
            aspis_statement::pool_v1::pool_v1_empty_roots()
        );
    }

    #[test]
    fn pair_table_is_exact_shifted_recursive_poseidon_v3_construction() {
        assert_eq!(POOL_V1_PAIR_EMPTY_ROOTS[0], POOL_V1_EMPTY_ROOTS[1]);
        for level in 0..POOL_V1_TREE_DEPTH {
            assert_eq!(
                POOL_V1_PAIR_EMPTY_ROOTS[level + 1],
                aspis_statement::pool_v1::pool_v1_tree_parent(
                    &POOL_V1_PAIR_EMPTY_ROOTS[level],
                    &POOL_V1_PAIR_EMPTY_ROOTS[level],
                )
            );
        }
    }
}
