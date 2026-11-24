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
[{"file":"Main.ltar","hash":"1fa34fb282ebda8e","base":["parent","parent"]}]
EOF
lean --run CheckInterface.lean Main parent/Main.olean rh-root/roots/Main.olean tables > declarations.json
jq -e '.parentNames == 5 and .candidateNames == 5 and .different == 0 and .proofChanges == 0 and .publicImports and .publicImage and .kernelImage' declarations.json
for ext in .olean .olean.server .olean.private .ir.sig .ir
do
  cmp "parent/Main$ext" "rh-root/roots/Main$ext"
done
```

The public job also loads the complete effective project input set and replays all five proof bodies with Lean at trust level zero. It checks the axiom set and the frozen challenge. Those results are in `replay.log`, `axioms.log`, `challenge.log` and `verified.json` in the same original ZIP.
