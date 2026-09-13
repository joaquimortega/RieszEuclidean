# Linter validation before commit

The first explicit environment-linter run found twelve issues: eleven missing
documentation strings and one unused intermediate fact in weak-limit separation.
The documentation was added and the unused fact removed. No linter was disabled,
no nolint annotation was introduced, and no warning was suppressed.

The revised project builds with warningAsError enabled. All fifteen default
environment linters, including slow tests, pass on 73 declarations and 179
automatically generated declarations. lint-current.txt contains the final report.
The blueprint and all twelve transitive axiom reports also pass.

Both earlier GitHub builds succeeded, including the affine module build at
c0adcbc (run 34752482333). This commit adds the explicit linter gate to CI and
records the before-commit rule in the README.
