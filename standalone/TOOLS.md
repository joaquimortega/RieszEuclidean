# Comparator tools for Lean 4.19.0

The project toolchain remains `leanprover/lean4:v4.19.0`. Comparator checks
statement/definition agreement, permitted axioms, and proof acceptance; source
assembly is performed by the project generator, not Comparator.

## Pinned sources

| Tool | Official repository | Commit |
| --- | --- | --- |
| Comparator | https://github.com/leanprover/comparator | `97ef939c9fe3f8abf93e4adb654517476da7a66f` (`pre-v25`) |
| lean4export | https://github.com/leanprover/lean4export | `bae5a4a9c1cddec1fd97a82907cb5be9da884b2d` (`v4.19.0`) |
| lean4checker | https://github.com/leanprover/lean4checker | `e11f65c651edd58d68ba260015d2bfde5102cd7f` (`v4.19.0`) |
| Landrun | https://github.com/Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator's `pre-v25` branch uses lean4checker for kernel replay and supports
older Lean projects. Its pinned checkout names Lean 4.24.0. The compatibility
change replaces `v4.24.0` with `v4.19.0` in `lean-toolchain` and both dependency
revisions in `lakefile.toml`, followed by `lake update`. This selects the exact
exporter/checker commits above. One CLI compatibility patch is also required:
`Main.lean` changes `args ++ #[spawnArgs.cmd] ++ spawnArgs.args` to
`args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args`, matching upstream master.
The exact patch is in `comparator-pre-v25.patch`.
This ends Landrun option parsing before the child command, preserving the
exporter's own `--` separator. It changes no comparison or kernel logic.

## Rebuild tools

Run from `riesz-euclidean-lean/`. Tool checkouts and generated binaries stay in the ignored
`.local/` directory. These commands require network access for initial downloads.

```sh
mkdir -p .local
git clone https://github.com/leanprover/comparator .local/comparator
git -C .local/comparator checkout --detach 97ef939c9fe3f8abf93e4adb654517476da7a66f
python3 - <<'PYCODE'
from pathlib import Path
root = Path('.local/comparator')
for name in ['lean-toolchain', 'lakefile.toml']:
    path = root / name
    path.write_text(path.read_text().replace('v4.24.0', 'v4.19.0'))
PYCODE
git -C .local/comparator apply ../../standalone/comparator-pre-v25.patch
(cd .local/comparator && lake update && lake build comparator lean4export)
git clone https://github.com/Zouuup/landrun .local/landrun
git -C .local/landrun checkout --detach 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd .local/landrun && go build -o landrun ./cmd/landrun)
```

The build was verified with Lean 4.19.0 and Go 1.24.4. Landrun requires Linux
with Landlock enabled. A real Landrun sandbox was tested on Linux 6.12.94;
the development-only `fake-landrun.sh` is not used.

## Run Comparator

Run from `riesz-euclidean-lean/` after building the project. This Comparator revision finds
`landrun` and `lean4export` in `PATH`; it does not implement the newer
`COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT` overrides.

```sh
export PATH="$PWD/.local/landrun:$PWD/.local/comparator/.lake/packages/lean4export/.lake/build/bin:$PATH"
systemd-run --user --pipe --wait \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --property=LimitSTACK=64M --property=LimitCORE=0 \
  --working-directory="$PWD" -E PATH="$PATH" \
  lake env "$PWD/.local/comparator/.lake/build/bin/comparator" \
  standalone/comparator.json
```

The 64 MiB process stack accommodates recursive traversal of proof dependencies. `LimitCORE=0` suppresses crash dumps.
These process resource settings do not change proof statements or kernel checks.

The outer systemd restriction follows the current upstream sandbox guidance for
kernels before Linux 7.1. It needs access to the user's systemd bus. Each build
and export also runs inside the real Landrun sandbox. Kernel replay uses the
Lean kernel through the pinned lean4checker, with no external kernel enabled.
The JSON explicitly sets `enable_nanoda: false`, as required by this older
Comparator interface. The reference and solution are trusted repository files;
this setup is not a claim of current-master hardening for adversarial inputs.

Successful completion prints `Lean default kernel accepts the solution` and
`Your solution is okay!`. See `reviews/standalone-validation.md` for the actual outcome. The accepted
ten-result configuration includes the hull lemma; final geometric nonexistence
statements are still pending.

For the initial local run, the three pinned binaries were copied from the
author-authorized previous project to `/tmp/riesz-euclidean-comparator-bin`.
That temporary cache is outside the synchronized tree; the reproducible build
above requires no previous project. Exclude `.local` from synchronization if
you choose that build location.
