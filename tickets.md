- General systems of equations
  - Extend solver beyond 2x2 linear: design Gaussian elimination pipeline for N variables (must return full solution vector for 3x3+), plus determinant-based fallback; define representation (matrix vs Expr) and normalization rules.
  - Support non-linear systems: plan numeric/iterative methods (Newton-Raphson with Jacobian), factorization-based branching, and handling of multiple solutions/branches.
  - Specify failure/singularity handling: zero pivots, rank deficiency, inconsistent systems; produce structured diagnostics and partial solutions when possible. Prefer exact/analytic solutions; only fall back to numerical methods when analytic paths are exhausted.
  - Add API/CLI shape for multi-equation input/output, including variable ordering guarantees and pretty-printing.

- Complicated integrands + “can’t solve” criteria
  - Inventory current integrator coverage; design classification pipeline that tags integrands with reason codes (e.g., “non-rational”, “non-polynomial trig”, “non-elementary”).
  - Add heuristics for common transforms (integration by parts, substitution detection, partial fractions) with depth/size limits to avoid blow-up.
  - Define explicit non-elementary detection rules (e.g., ∫e^{x^2}, ∫sin(x)/x) and return structured “cannot integrate” results instead of echoing input.
  - Plan extensibility hooks for future methods (Risch-lite, Meijer-G) and a central “IntegrandKind” enum to drive strategy selection.

- Testing expansion
  - Add property/round-trip tests for simplify/pretty/parse on large fraction-heavy expressions.
  - Add integration tests covering mixed trig/rational/exponential cases, including expected “cannot integrate” outcomes with reason codes.
  - Add system-of-equations tests: large linear systems (full-rank, singular, inconsistent) and simple non-linear systems; verify solution sets/diagnostics.
  - Build regression corpus from known tricky inputs (deeply nested powers, products of sums) and gate with a benchmark harness to watch for performance regressions.

