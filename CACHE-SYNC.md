# Rebuildable dependencies and cloud synchronization

Do not synchronize `.lake`. A standalone clone downloads its own pinned
Mathlib dependencies with `lake exe cache get`; no shared checkout is needed.
The existing Batteries dependency contains a valid, tracked relative symlink
`docs/README.md -> ../README.md`. Keep it intact; replacing or deleting it makes
Lake report local dependency changes.

On a Linux Yandex Disk installation with this workspace layout, append
`IA/yura/riesz-euclidean-lean/.lake` to `exclude-dirs` in that machine's Yandex
configuration, preserving its other entries. This is a machine-local setting:
Git and cloud synchronization do not propagate the exclusion automatically.
`.gitignore` controls Git only.

The current machine's existing exclusion list was extended with this path when
the project was created. Its configuration was backed up first. No Yandex service
was restarted. Other machines must configure their own exclusion before syncing
or building a dependency cache.
