(* Boundary probes for observation-sensitive local DFT simulation. *)
Theory dftFrameLocal
Ancestors
  dftFramePair dftFrameVars dftFrameSwap dftScheduleOrder venomInst

Theorem dft_cross_allows_assert_before_mload:
  let a = mk_inst 0 ASSERT [Lit 0w] [];
      b = mk_inst 1 MLOAD [Lit 0w] ["x"]
  in dft_cross a b /\ dft_must_order a b
Proof
  EVAL_TAC >> simp[]
QED
