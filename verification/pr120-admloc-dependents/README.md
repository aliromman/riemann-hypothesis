# Check the scope of the AdmLoc instances

Upstream PR #911 scopes the two high-priority tensor and function module instances in `GlobalTheory.AdmLoc`. It also removes their former erasures from five consumers. Roy7 suggested testing the provider. A global reduction in priority caused the intended module structure to time out in `ResBound`. The scoped change passed the Satake and `ResBound` controls. [Supporting PR](https://github.com/leanprover-community/riemann-hypothesis/pull/911) · [Roy7's discussion](https://github.com/leanprover-community/riemann-hypothesis/issues/599#issuecomment-7125176754) · [Provider controls](../pr120-admloc-priority)

All five direct erasure users build together with the new source. The targeted build used 11,870 project source files and finished all 42,037 Lake jobs. The five modules and the provider also passed individual kernel replay. An exact comparison of stored expressions found public type changes in three of the five modules. All five changed type expressions were definitionally equal in both kernel environments. All 63 public declaration and axiom records passed, and the single computational definition retained its body. [Two-environment comparison](five-result.json) [Build and kernel results](five-build-and-kernel.json)

Both revisions also built the 467 modules in `467/modules.txt`. The run verified 12,065 Git source blobs per revision. The final Lake check found all 42,427 jobs up to date on each side. All 3,526 public declarations have the same axiom records. The comparison found 146 different stored types, 61 different definition bodies, and three different recursor rules. Lean's kernel accepted all 210 changes in both environments. Four definitions use compiler-generated proof helpers whose names changed. For those four, the checker expanded the helpers, proved conversion to the owning expression, and checked the two expanded terms in each environment. Of 2,272 theorems, 2,095 retained their stored proof terms. [Machine results and per-module records](467/result.json)

The first object scan flagged five modules. Three recursor comparisons mixed their metadata with the rule bodies, and four definition comparisons encountered a generated proof name with a different type in the other module. The three recursor rules now have separate conversion checks. The raw conversion records retain the four failed direct comparisons. The two proof-helper records contain the successful kernel checks. A second complete object scan agreed on all 467 modules. The full target list has 1,121 more modules.

## Repeat the dependent checks

Use two clean checkouts with the locked packages and Lean 4.37.0-rc1. Check out `d27f71347abceb76cd37dc8a5fccbe556ec2be90` in the stock checkout and `26c70f301cc7fb498680f61144ac55f604069506` in the candidate. Existing builds can be reused. Set `tools` to this directory.

```sh
python3 "$tools/run_dependents.py" --stock "$stock" --candidate "$candidate" --out "$out"
```

The full command builds 11 terminal targets that include `Main`. They cover all 1,588 affected modules and require 60,728 project sources. The tool compares every affected public declaration, its binder modes, computational definitions, and recorded axioms. It checks type and definition differences with Lean's kernel in the stock and candidate environments. The result includes counts for changed raw theorem proofs. It exits with an error if the public declaration check fails. The protected five-statement Comparator has a separate upstream procedure.

To repeat the 467-module run, add `--modules "$tools/467/modules.txt"`. To require up-to-date Lake artifacts, add `--no-build`. For a project containing only the required source closure, supply `--source-repo` with a repository that contains both pinned commits. This mode reads the transitive imports with Lean, checks every source against its Git blob, and checks the build configuration and dependency revisions.
