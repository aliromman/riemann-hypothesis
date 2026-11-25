# Seven changed callers and two theta targets on batch #2960

All nine targets compiled on community main `8e5cefeeaffe7e4c12153385b7bb33fb7223c41a` and on its merge with #1037, `ac7b31c0da50c61cf2d0408818076ac442742650`. Both stock Lake builds completed 20,714 jobs. Each build passed a second check with `--no-build`. Stock `leanchecker` replayed all nine target modules on each revision. [Exact commands, exits and log hashes](receipt.json) · [Merge source](https://github.com/aliromman/riemann-hypothesis/commit/ac7b31c0da50c61cf2d0408818076ac442742650)

The 4,849 project dependencies include 937 modules that depend on the PR edits. The baseline used 4,840 restored modules and compiled the nine targets. The merge used 3,912 unaffected modules and 11 modules already checked on this tree. Lake compiled the other 926. The target list also includes the live prerequisites for the archived doubling proof. [Target list](build-targets.txt) · [Nine kernel targets](kernel-targets.txt)

The complete archived doubling file compiled on each revision in both provider orders and with the original import change. All 12 commands per revision passed, including the support modules and the separate `localZ_map` tests. This confirms Daniel Ang’s #1324 already fixes the archived case. The separate live `LinUnit` proof still needs #1037. [Archived results](doubling.json) · [Live proof results](../README.md)

## Reproduce

Use separate clean checkouts of the two commits above. Set `before` and `after` to their paths. Set `results` to this receipt directory and `scripts` to the directory that contains `replay_doubling.py`. Both paths must be absolute. Set `out` to an empty output directory. The archived replay reads the older sources from Git. Use a checkout with those commits. [Replay program](../../../replay_doubling.py)

```sh
for tree in "$before" "$after"; do
  (
    cd "$tree" &&
    xargs lake --no-cache --rehash build < "$results/build-targets.txt" &&
    xargs lake --no-cache --rehash build --no-build < "$results/build-targets.txt" &&
    xargs lake --no-cache env leanchecker -v < "$results/kernel-targets.txt"
  ) || exit 1
done
bin=$(cd "$after" && dirname "$(elan which lean)")
python3 "$scripts/replay_doubling.py" --full --repo "$after" \
  --before "$before" --after "$after" --bin "$bin" --output "$out"
```
