# Verify the five compiled claims and their two direct providers

These Apple-silicon archives contain the actual compiler output for `ClaimStrip`, `MainConclusion` and `Main` on the indicated pull request. The compiler read a complete set of public project interfaces. The archive records how many of those interfaces also had current or equivalent source-compilation evidence when it was sealed.

| PR | Frozen Git revision | Edited modules with source-compilation evidence | Edited modules still to check |
| --- | --- | ---: | ---: |
| #879 | `299eff8a308272be2b9167be917156f1929359a2` | 17,734 | 21,222 |
| #977 | `13345ac952b571c8f08a856fcedab838bfef0af8` | 4,340 | 7,194 |

The first command checks the original archive digest and the recorded status of its inputs. The subsequent commands compare the actual declarations, proof expressions and all five compiler outputs for each of the three compiled modules with the community's authenticated parent archive. The archived kernel replay checked the five proofs in the recorded import environment. The complete source builds and the community's independent Comparator are separate checks.

Put the pinned Lean installation on `PATH`. Set `ROOT_ZIP` to the absolute path of one of the original `projected-inputs-darwin-five-roots-*.zip` files. Use an empty directory with about 20 MiB of free space. The commands require `curl`, `unzip`, `shasum`, `jq` and Python 3.

```sh
set -eu
archive_digest=$(shasum -a 256 "$ROOT_ZIP" | cut -d' ' -f1)
case "$archive_digest" in
  f7738823fd2bb343309ebaff5b37d4aaca5f9e98fcb6573f2d36b45f8fb2b853)
    revision=299eff8a308272be2b9167be917156f1929359a2
    observed=17734
    outstanding=21222 ;;
  71a0d28e18cea9d20f5aca8e8785c59d921655c7c9a8e205beaabcd616111790)
    revision=13345ac952b571c8f08a856fcedab838bfef0af8
    observed=4340
    outstanding=7194 ;;
  *) echo 'Archive digest differs from both recorded digests' >&2; exit 1 ;;
esac
unzip -p "$ROOT_ZIP" evidence/confirmed-native-snapshot.json |
  jq -e --arg revision "$revision" --argjson observed "$observed" --argjson outstanding "$outstanding" '
    .head == $revision and .combined_confirmed_sources == $observed
    and .open_source_compilation_cases == $outstanding
    and .total_source_edits == ($observed + $outstanding)'
unzip -p "$ROOT_ZIP" evidence/projection-and-proof.json |
  jq -e --arg revision "$revision" '
    .head == $revision and .parent == "82c577caf1b8a66c76212d78a399234f55813d28"
    and .platform == "arm64-apple-darwin"
    and .actual_provider_and_Main_outputs_equal_community_bytes == 15
    and .all_visible_to_Main == 58953 and (.checked_theorems | length) == 5'
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
[{"file":"Main.ltar","hash":"6d5627a33903f61b","base":["parent","parent"]}]
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

Run this block in the same directory after the Main comparison. It uses about 15 MiB of additional scratch space. The archive names, Lake keys and SHA-256 digests below are those in the official batch 1410 module manifest. The source contains five local declarations in ClaimStrip and 52 in MainConclusion.

```sh
set -eu
mkdir provider-parent provider-tables
cache=https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis
curl -fsSL -o ClaimStrip.ltar "$cache/4ad9ead7b82c6d2a.art"
curl -fsSL -o MainConclusion.ltar "$cache/b1ab367fb7259385.art"
shasum -a 256 -c <<'EOF'
74ecdac298d7da00cea54549f4c0f7d391b075738c7e26537ddd5164f4562685  ClaimStrip.ltar
1551201e5da42166619bc64ecc138f879c423aaa49781db0151a1aec15661d0f  MainConclusion.ltar
EOF
leantar --jobs 1 -f -x -j - <<'EOF'
[{"file":"ClaimStrip.ltar","hash":"1500f3841a2fc7a9","base":["provider-parent","provider-parent"]},{"file":"MainConclusion.ltar","hash":"264225eb2bad01d9","base":["provider-parent","provider-parent"]}]
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

For batch 1410, the private import `Lemmata.TracePi` occurs in the `MainConclusion` setup. Lean does not re-export it to `Main`. Each compressed provider setup in the ZIP contains the exact file names that its compiler received.
