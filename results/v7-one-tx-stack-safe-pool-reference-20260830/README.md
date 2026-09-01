# Stack-safe Pool SBF reference

This is the independently focused Linux x86_64 / platform-tools v1.48 Pool
artifact built from production source commit
`6bc7d3caf181be23a8a6ac7769497c965cd7273d` before the release-wide dual build.
It is retained only as a byte-exact third reference for that dual build.

- artifact: `aspis_pool.so`
- bytes: `526056`
- SHA-256: `0bbe441f0e13c2f61e2369674628b06c9d538192514b4e9a92d229479956586d`
- focused build source: `/home/dombarker/project-offloads/aspis-v7-pool-checkpoint-stack-20260830.x6G9VF`
- maximum observed stack offsets: planner `2912` bytes; decode helper `3024` bytes
- stack limit: `4096` bytes

This file does not by itself establish reproducibility. The release gate still
requires independent source copies A and B to reproduce the same bytes under
the frozen Linux toolchain and zero-swap cgroup.
