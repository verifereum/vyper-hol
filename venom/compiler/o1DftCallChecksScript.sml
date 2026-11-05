(*
 * dft_fn keeps every external call's success flag checked
 * (call_checks_ok) on an SSA function.  dftCallChecks proves it for one
 * rescheduling of each block (dft_blocks_call_checks_ok); dft_fn's
 * worklist loop reschedules one block at a time, possibly a block more
 * than once.  Off SSA it fails: a redefinition of the flag can be
 * scheduled between the call and its check.
 *)
Theory o1DftCallChecks
Ancestors
  dftCallChecks unitShapeDefs dftDefs venomWf

Theorem dft_fn_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ fn_pseudos_prefix fn /\
  EVERY inst_shape_ok (fn_insts fn) /\ call_checks_ok fn ==>
  call_checks_ok (dft_fn fn)
Proof
  cheat
QED
