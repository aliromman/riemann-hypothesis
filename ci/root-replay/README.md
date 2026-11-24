# Replay the five claims at a published pull request head

Use this workflow on the public verification branch in the fork. The approved input consists of the upstream pull request number, the exact head and base commits, the complete before and after source trees, and one native compiler record for each changed module.

Generate a request after the PR is public and the local source-bound staging step has checked every changed public and IR image. This accepts either the full staging output or its disk-saving plan. Both modes must have a complete source provenance table and a successful IR audit.

```sh
python3 ci/root-replay/manifest.py --pr "$PR_NUMBER" \
  --stage "$STAGING_DIRECTORY" --out ci/root-replay/request
```

Commit the two files in `ci/root-replay/request` on the fork's `ci/import-pruning/screen` branch. A push that changes the request file starts the single Ubuntu verifier. The import screen listens for changes under `ci/import-screen` only. The source PR contains neither verifier.

The verifier reads the upstream PR and main ref twice. It rejects a different head or base. It checks every physical Lean source file against its Git object. The full diff must contain exactly the recorded private Mathlib import edits. The candidate pins, frozen challenge, comparator configuration and Main must remain identical to the approved parent. The job obtains the official source-bound parent cache receipt. It rechecks the complete project input witnesses for rows that use a certificate from the previous parent.

For each group of 32 archives, the project downloader checks the published SHA-256. Stock leantar expands the archives. For a changed module, the pinned serializer reads both source headers and writes the new public and IR artifacts. The raw public image, IR signature and IR body must match the three digests from the original native compiler run. IR outputs and temporary private images are released after each group. Only one public image per visible module is needed during root elaboration. The original Main also supplies the server and private parts for declaration comparison.

A fresh export of the official Challenge must match the checksum in the community workflow. The verifier then re-elaborates the unchanged Main source with an explicit map of all its project imports. It compares all five kernel declarations with the official parent, rejects an intentionally invalid proof and replays each real theorem body. It checks each permitted axiom set, all five proposition types and the four named proposition definitions against Challenge. The result separates exact expression equality from alpha-equivalence for definition bodies.

The per-module native compiler records are inputs to this check. The root job verifies their source and reconstructs their public artifacts. A complete source build and a full solution Comparator export with independent kernels require separate verification.
