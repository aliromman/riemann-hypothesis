# Verify the five compiled claims and their two direct providers

These Apple-silicon archives contain the actual compiler output for `ClaimStrip`, `MainConclusion` and `Main` on the indicated pull request. The compiler read a complete set of public project interfaces. The archive records how many of those interfaces also had current or equivalent source-compilation evidence when it was sealed.

| PR | Frozen Git revision | Edited modules with source-compilation evidence | Edited modules still to check |
| --- | --- | ---: | ---: |
| #879 | `f390b4d81f818a3174ffc7fc0154c0d7369c08f2` | 8,503 | 30,440 |
| #977 | `c0d14da69d2c6b5f0335680d7c3b6541acc95c29` | 1,734 | 9,793 |

Both immediate provider sources have the same Git blobs in batches #1739 and #1801. The official original MainConclusion editor file and its Lake trace changed. The four ClaimStrip declarations and the 52 MainConclusion declarations, including every private proof, agree across the two originals. The commands below compare each pull request with the new official parent.

The first command checks the original archive digest and the recorded status of its inputs. The subsequent commands compare the actual declarations, proof expressions and all five compiler outputs for each of the three compiled modules with the community's authenticated parent archive. The archived kernel replay checked the five proofs in the recorded import environment. The complete source builds and the community's independent Comparator are separate checks.

Put the pinned Lean installation on `PATH`. Set `ROOT_ZIP` to the absolute path of one of the original `projected-inputs-darwin-five-roots-*.zip` files. Use an empty directory with about 20 MiB of free space. The commands require `curl`, `unzip`, `shasum`, `jq` and Python 3.

```sh
set -eu
archive_digest=$(shasum -a 256 "$ROOT_ZIP" | cut -d' ' -f1)
case "$archive_digest" in
  bcb11f224791424181dbc6db72425c357f85ff3427a109f8ebbdf1c224c57681)
    revision=f390b4d81f818a3174ffc7fc0154c0d7369c08f2
    observed=8503
    outstanding=30440 ;;
  063f16079ef91fa49feaa2403e25eedd01b4666675a4a208aafb7cc7a7c383eb)
    revision=c0d14da69d2c6b5f0335680d7c3b6541acc95c29
    observed=1734
    outstanding=9793 ;;
  *) echo 'Archive digest differs from both recorded digests' >&2; exit 1 ;;
esac
unzip -p "$ROOT_ZIP" evidence/confirmed-native-snapshot.json |
  jq -e --arg revision "$revision" --argjson observed "$observed" --argjson outstanding "$outstanding" '
    .head == $revision and .combined_confirmed_sources == $observed
    and .open_source_compilation_cases == $outstanding
    and .total_source_edits == ($observed + $outstanding)'
unzip -p "$ROOT_ZIP" evidence/projection-and-proof.json |
  jq -e --arg revision "$revision" '
    .head == $revision and .parent == "c40250a50104b7e02e7d74f658d00fa7b1f4827c"
    and .platform == "arm64-apple-darwin"
    and .actual_provider_and_Main_outputs_equal_community_bytes == 15
    and .all_visible_to_Main == 58917 and (.checked_theorems | length) == 5'
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
[{"file":"Main.ltar","hash":"fb8ba367c277903c","base":["parent","parent"]}]
EOF
lean --run CheckInterface.lean Main parent/Main.olean rh-root/roots/Main.olean tables > declarations.json
jq -e '.parentNames == 5 and .candidateNames == 5 and .different == 0 and .proofChanges == 0 and .publicImports and .publicImage and .kernelImage' declarations.json
for ext in .olean .olean.server .olean.private .ir.sig .ir
do
  cmp "parent/Main$ext" "rh-root/roots/Main$ext"
done
```

The archive contains the executed `replay.log`, `axioms.log`, and `challenge.log` under `rh-root/roots/`. The kernel rejected the changed proof and accepted the five original proof bodies at trust level zero. The axiom check reported `propext`, `Classical.choice` and `Quot.sound` for each claim. The frozen challenge comparison checked all five claim types and the four project-defined statements. The input coverage and public-interface projection used for these runs are in `evidence/confirmed-native-snapshot.json` and `evidence/projection-and-proof.json`.

## Check the two fresh imports used by Main

Run this block in the same directory after the Main comparison. It uses about 15 MiB of additional scratch space. The archive names, Lake keys and SHA-256 digests below are those in the official batch 1801 module manifest. The source contains four local declarations in ClaimStrip and 52 in MainConclusion.

```sh
set -eu
mkdir provider-parent provider-tables
cache=https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis
curl -fsSL -o ClaimStrip.ltar "$cache/226dff08596b2fab.art"
curl -fsSL -o MainConclusion.ltar "$cache/92430abac0ea90bc.art"
shasum -a 256 -c <<'EOF'
f73fae73c223b3623f41f584170d489aefeb9070f1058e467e58df596ee2390b  ClaimStrip.ltar
86f3dc561f6e3150165762f22f8b067e4060abced60db493e4db115813000741  MainConclusion.ltar
EOF
leantar --jobs 1 -f -x -j - <<'EOF'
[{"file":"ClaimStrip.ltar","hash":"d013dbe2a9b4488c","base":["provider-parent","provider-parent"]},{"file":"MainConclusion.ltar","hash":"843b81a26d4d12ea","base":["provider-parent","provider-parent"]}]
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
  count=4
  if [ "$module" = MainConclusion ]; then count=52; fi
  lean --run CheckInterface.lean "Development.AutomorphicArithmetic.CharacterBoxes.$module" \
    "provider-parent/$module.olean" "$rebuilt.olean" provider-tables > "provider-$module.json"
  jq -e --argjson n "$count" '.parentNames == $n and .candidateNames == $n and .different == 0 and .proofChanges == 0 and .publicImports and .publicImage and .kernelImage' "provider-$module.json"
done

python3 - "$ROOT_ZIP" <<'PYTHON'
import gzip, hashlib, json, sys, zipfile

def digest(data):
    return hashlib.sha256(data).hexdigest()

with zipfile.ZipFile(sys.argv[1]) as archive:
    base = "rh-root/roots/"
    report = json.loads(archive.read(base + "report.json"))
    root = report["direct_providers"]
    main = json.loads(gzip.decompress(archive.read(base + "providers/main-setup.json.gz")))
    outside = set()
    for name, row in root["providers"].items():
        prefix = base + "providers/" + name.split(".")[-1] + "/"
        packed = archive.read(prefix + "setup.json.gz")
        raw = gzip.decompress(packed)
        assert digest(packed) == row["compressed_setup_sha256"] and digest(raw) == row["setup_sha256"]
        setup = json.loads(raw)
        members = [json.loads(line) for line in gzip.decompress(archive.read(prefix + "inputs.jsonl.gz")).splitlines()]
        assert setup["name"] == name and set(setup["importArts"]) == {r[0] for r in members}
        assert main["importArts"][name] == [[row["public_output"]], []]
        outside.update(setup["importArts"].keys() - main["importArts"].keys())
    assert sorted(outside) == report["provider_only_inputs"] == ["Lemmata.TracePi"]
    print("Verified each compiler setup and the private import of Lemmata.TracePi")
PYTHON
```

The archive contains the actual Main setup in `rh-root/roots/providers/main-setup.json.gz`. Both provider paths in this setup point to the new outputs. Each provider's `inputs.jsonl.gz` lists the name, raw public SHA-256 and source of every project module passed to its compiler invocation.

For batch 1801, the private import `Lemmata.TracePi` occurs in the `MainConclusion` setup. Lean does not re-export it to `Main`. Each compressed provider setup in the ZIP contains the exact file names that its compiler received.
