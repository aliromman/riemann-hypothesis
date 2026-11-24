# Stock builds and proof checks

The ordinary Linux builds and the native comparison used the same published source tree, toolchain and Mathlib pin. The stock job records each source, archive, compiler output, declaration comparison and independent kernel replay. [Source and inputs](https://github.com/aliromman/riemann-hypothesis/tree/6e5030c3846bcf157ddad686d7750447f8f70346/ci/stock-batch-1266/results/45446269669) · [Independent public-object readback](bounded-workloads/original-sources.json)

The fresh stock test covered 72 requested roots, 140 project modules and 95 edited files. Lake compiled 99 modules and compared 9,540 declarations. The ordinary public and two IR files for all 95 edits matched the pinned serializer. On these edits the public files used 493,824 fewer bytes and the IR bodies used 503,448 fewer bytes. The editor metadata grew by 984 bytes and the private files by 20,800. Stock Lean replayed three roots.

A three-module clean build with identical source, compiler inputs and package pins had taken 8.350 seconds on the previous measured baseline and 7.708 seconds with the private imports removed. This was a five-pair Linux timing for that workload. The earlier four individual timings and two sandboxed proofs have the same inputs on this revision. [Earlier workload identities](bounded-workloads/stock879/identical-inputs.json)

On a separate 21-module panel, generated C and the number of direct calls to Mathlib module initializers both fell. [Generated C and input identities](generated-c)

The pinned Comparator exported an affected proof from source inside Bubblewrap on Ubuntu. Lean default, Lean paranoid and nanoda accepted the proof. The three other previously measured sandbox workloads have identical source and dependency inputs on this batch. The default nine-target build and the complete five-claim sandboxed solution export remain community checks. [Sandbox source, controls and kernel logs](https://github.com/aliromman/riemann-hypothesis/tree/ec29eed2be2f35a51f82053da385d6ca8ec328c7/ci/source-sandbox/results/45446517890)
