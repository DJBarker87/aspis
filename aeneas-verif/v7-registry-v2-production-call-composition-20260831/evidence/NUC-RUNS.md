# Focused NUC run evidence

Host workspace:

```text
/home/dombarker/project-offloads/aspis-v7-production-call-compose-20260831.dzN7UE
```

Lean dependency workspace:

```text
/home/dombarker/project-offloads/aspis-v7-registry-v2-projection-certificate-20260831/tmp/aspis-v7-registry-v2-deployment-lean.6ESquc
```

Toolchain:

```text
Charon 0.1.223
Aeneas d860ac47-tag73-variantfn-namespace-r1
Lean 4.31.0
```

| Unit | Invocation | Wall | Peak RSS | Swap | Exit |
|---|---|---:|---:|---:|---:|
| `aspis-v7-production-call-charon-codecs-02` | `08219fc8000e4a9893dae92fffa41374` | 14.68 s | 518,492 KiB | 0 | 0 |
| `aspis-v7-production-call-aeneas-codecs-02` | `bfda9ce1f18d43a0bbb3291d0ee30f8e` | 1.93 s | 152,064 KiB | 0 | 0 |
| `aspis-v7-production-codecs-types-renamed-01` | `4c2d53af82b44c74b4d164cc341de0b1` | 1.99 s | 2,601,936 KiB | 0 | 0 |
| `aspis-v7-production-codecs-externals-renamed-01` | `032288f7f2814f90a16b02e7c8a62de1` | 1.19 s | 2,557,328 KiB | 0 | 0 |
| `aspis-v7-production-codecs-funs-renamed-02` | `0d6d840844ab49c59efbbfa411505899` | 2.26 s | 2,641,340 KiB | 0 | 0 |
| `aspis-v7-production-codecs-bridge-renamed-02` | `6e2ea604490c496c9136deda19ac8971` | 1.40 s | 2,560,204 KiB | 0 | 0 |
| `aspis-v7-production-compose-deployment-olean-01` | `69945a06171048b19ccbe4a8804af565` | 2.74 s | 2,582,900 KiB | 0 | 0 |
| `aspis-v7-production-compose-capstone-06` | `511fa5fd2fcb4693bb0182bfda9e85ba` | 1.27 s | 2,565,384 KiB | 0 | 0 |

Every large-host command ran in its own systemd scope with
`MemorySwapMax=0`; the Lean jobs used a 6 GiB hard cap. Worst measured peak was
2,641,340 KiB. No job approached the repository's 12 GiB split/restart rule.
