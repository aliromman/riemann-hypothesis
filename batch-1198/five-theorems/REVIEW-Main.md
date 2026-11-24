# Check the five compiled declarations from the public job

The root ZIP contains the five compiler outputs for the actual candidate `Main`. The source of these five declarations is unchanged. The stock community receipt for each checked parent assigns the same archive to `Main`. The commands below compare the original bytes, the full declaration tables and all five proof expressions. They require about one megabyte of scratch space in addition to the downloaded root ZIP and an installed compiler.

Put the pinned Lean installation on `PATH`. Set `ROOT_ZIP` to the path of the original Actions ZIP. Check that file against the SHA-256 published by GitHub for the selected run. Run the following commands in an empty directory.

```sh
set -eu
lean --version | grep -F 'commit 0b77e12952ad39077d80d8bd6b66d601f225c321'
mkdir parent tables
unzip -q "$ROOT_ZIP" 'rh-root/roots/Main*'
curl -fsSL -o Main.ltar https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/0cb082362c7194a6.art
curl -fsSL -o CheckInterface.lean https://raw.githubusercontent.com/aliromman/riemann-hypothesis/d5f33aadf72f0ec93318a4cd2b0f95413196a304/ci/import-screen/CheckInterface.lean
shasum -a 256 -c <<'EOF'
73ad1441a3201b2853512abd51f7377cffb562274b1a9a6f79e953efc83e512e  Main.ltar
d42ab8acf8d953f321c501b0e479f7b92c6ab51484f4fae63f745a57deaa0af3  CheckInterface.lean
EOF
leantar --jobs 1 -f -x -j - <<'EOF'
[{"file":"Main.ltar","hash":"2ce68ca17997e829","base":["parent","parent"]}]
EOF
lean --run CheckInterface.lean Main parent/Main.olean rh-root/roots/Main.olean tables > declarations.json
jq -e '.parentNames == 5 and .candidateNames == 5 and .different == 0 and .proofChanges == 0 and .publicImports and .publicImage and .kernelImage' declarations.json
for ext in .olean .olean.server .olean.private .ir.sig .ir
do
  cmp "parent/Main$ext" "rh-root/roots/Main$ext"
done
```

The public job also loads the complete effective project input set and replays all five proof bodies with Lean at trust level zero. It checks the axiom set and the frozen challenge. Those results are in `replay.log`, `axioms.log`, `challenge.log` and `verified.json` in the same original ZIP.

## Check the two fresh imports used by Main

Run this block in the same directory after the Main comparison. It uses about 15 MiB of additional scratch space. The archive names, Lake keys and SHA-256 digests below are those in the official batch 1198 module manifest. The source contains five local declarations in ClaimStrip and 53 in MainConclusion.

```sh
set -eu
mkdir provider-parent provider-tables
cache=https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis
curl -fsSL -o ClaimStrip.ltar "$cache/4ad9ead7b82c6d2a.art"
curl -fsSL -o MainConclusion.ltar "$cache/9d818aa89ca395aa.art"
shasum -a 256 -c <<'EOF'
74ecdac298d7da00cea54549f4c0f7d391b075738c7e26537ddd5164f4562685  ClaimStrip.ltar
2819195ccf32b2884ed6f99f8d661c227cd6f0c09df789c98890d5db5c499d35  MainConclusion.ltar
EOF
leantar --jobs 1 -f -x -j - <<'EOF'
[{"file":"ClaimStrip.ltar","hash":"1500f3841a2fc7a9","base":["provider-parent","provider-parent"]},{"file":"MainConclusion.ltar","hash":"e1dda8ef5768c8cf","base":["provider-parent","provider-parent"]}]
EOF
unzip -q "$ROOT_ZIP" 'rh-root/roots/providers/*/Development/*'
prefix=Development/AutomorphicArithmetic/CharacterBoxes
for module in ClaimStrip MainConclusion
do
  rebuilt="rh-root/roots/providers/$module/$prefix/$module"
  for ext in .olean .olean.server .olean.private .ir.sig .ir
  do
    cmp "provider-parent/$module$ext" "$rebuilt$ext"
  done
  count=5
  if [ "$module" = MainConclusion ]; then count=53; fi
  lean --run CheckInterface.lean "Development.AutomorphicArithmetic.CharacterBoxes.$module" \
    "provider-parent/$module.olean" "$rebuilt.olean" provider-tables > "provider-$module.json"
  jq -e --argjson n "$count" '.parentNames == $n and .candidateNames == $n and .different == 0 and .proofChanges == 0 and .publicImports and .publicImage and .kernelImage' "provider-$module.json"
done
```

The job retained the actual Main setup in `rh-root/roots/providers/main-setup.json.gz`. Both provider paths in this setup point to the new outputs. Each provider's `inputs.jsonl.gz` lists the name, raw public SHA-256 and source of every project module passed to its compiler invocation.
