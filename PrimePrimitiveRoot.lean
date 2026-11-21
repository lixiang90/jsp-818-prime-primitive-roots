import ExplicitTwist
import FiniteCases

/-! Public entry point for the deduction from Dirichlet GRH. -/

/-- Every odd prime admits a strictly smaller prime primitive root under Dirichlet GRH. -/
theorem JSP818.erdos_985_of_grh (grh : JSP818.DirichletGRH) (p : ℕ)
    (hp : p.Prime) (hne : p ≠ 2) : JSP818.HasSmallPrimeRoot p :=
  JSP818.erdos_985_of_grh_and_finite grh JSP818.basicFiniteInput_verified p hp hne

#check JSP818.erdos_985_of_grh
#print axioms JSP818.erdos_985_of_grh
