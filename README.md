# Levent Alpöge/Fable 5's counterexample to the Jacobian conjecture in Lean 4

Everything is in [`Jacobian/Counterexample.lean`](Jacobian/Counterexample.lean): an explicit polynomial self-map of $K^3$ with Jacobian determinant $1$ that is not injective over any field $K$.

The main theorem is

```lean
theorem not_jacobianConjecture_all_char (K : Type*) [Field K] :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) K, IsUnit (jacobianDet F) → Injective (evalMap F)
```

The original determinant $-2$ form is also there as `not_jacobianConjecture` (char ≠ 2), as well as the specialization to $\mathbb{C}$ as `not_jacobianConjecture_complex`.

To check it yourself:

```
lake exe cache get
lake build
```