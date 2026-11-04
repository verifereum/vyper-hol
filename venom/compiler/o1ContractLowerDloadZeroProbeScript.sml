(* Historical zero-size comparison probes retired: access_ok now requires
   strictly positive size for compared pointer provenance.  The old fixture
   does not satisfy the source invariant and is not a counterexample to the
   current frozen contract.  See journal episodes E0008 and E0011. *)
Theory o1ContractLowerDloadZeroProbe
Ancestors
  o1ContractLowerDloadTaint
