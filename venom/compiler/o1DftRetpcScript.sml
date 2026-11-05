(*
 * dft_fn keeps the return-PC shape (retpc_shape_ok) on an SSA function.
 * On SSA, dft_fn keeps every instruction of each block, up to flipping
 * the operands of a commutative or comparison instruction
 * (dft_fn_all_perm_of), keeps the pseudo-instructions and the labels and
 * successors of each block, so the CFG, reachability and the return-PC
 * variables (defined by RETPC_PARAM, ASSIGN and PHI, none of which is
 * flipped) are the same.
 *)
Theory o1DftRetpc
Ancestors
  dftCorrectness dftLifting unitShapeDefs dftDefs venomWf

Theorem dft_fn_retpc_shape_ok:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ fn_pseudos_prefix fn /\
  EVERY inst_shape_ok (fn_insts fn) /\ retpc_shape_ok fn ==>
  retpc_shape_ok (dft_fn fn)
Proof
  cheat
QED
