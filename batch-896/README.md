# Community batch 896

This directory compares `c9883164b0b3d762cee21f889d03d59a53b3ba3b` and the exact pull request 977 revision in `binding.json`. Both use Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. Each row in `source-rows.jsonl.gz` contains the SHA-256 of both actual Git source files, original member count, scope changes, line counts and byte delta. Run the repository readers directly with the portable reproduction script.

```sh
python3 ../audit_source.py c9883164b0b3d762cee21f889d03d59a53b3ba3b 9db9c372b954b858261870086c953c60d07a2890 --repo /path/to/riemann-hypothesis --output reproduced-rows.jsonl.gz
cmp source-rows.jsonl.gz reproduced-rows.jsonl.gz
```

`selection.json` lists the 209 files returned to focused open proposals, 291 clumps made available by upstream's 230-PR batch and the 17 earlier source candidates returned to upstream after exact private proof comparisons. Those checks compared types and serialized proof values. Public and IR bytes alone did not detect these differences. In a diagnosed example, the equation theorem `GlobalTheory.eigenSeriesCoeff.eq_def` had different source offsets in a `_recApp` annotation. Erasing metadata made the two expressions structurally equal. The file retained its upstream source. The preserved archived-header byte count in `binding.json` excludes one newline per record.

`dependencies.json` gives the direct and transitive downstream module counts derived from this parent's module graph. Its 374,593 project imports were also compared with the headers of all 60,629 official compiled project modules. The 60,630 source files under `src/` include the independent Challenge file.

`composition.json` identifies the two branch heads and the local merge tree. For each shared file, `composition-source.jsonl.gz` gives the path and four SHA-256 values for the parent, import branch, scope branch and combined source. The combined source is the import branch's header followed by the scope branch's body. The native sample covers 18 roots and all 51 affected files in their dependency cones. Eleven unchanged root cones reuse the earlier paired compilation after checking their source and loaded inputs. Twenty-three module pairs were compiled again against the new batch. The rows in `composition-native.jsonl` retain both public and IR hashes, declaration counts and proof comparison results. These results cover the sampled cones. A complete source build of the combined branches is a separate check.

The complete native input records and the independently checked Linux theorem examples are linked from the pull request. The default-target stock Lake build and the full five-claim Comparator export need the larger community runner.
