(*
 * The step write footprint holds for every context: a successful step from
 * a raw-reachable state outside a revert forwarding changes a memory byte
 * only inside a write range (source_memory_write_ranges) of a raw-reachable
 * instruction state outside a revert forwarding.  For an ordinary
 * instruction that is its own range; for INVOKE it is a range of an
 * instruction the callee's run executes, which raw_reachable reaches
 * through its callee, next and block rules.
 *
 * TOP-LEVEL:
 *   step_write_footprint_holds  - step_write_footprint ctx vs, for all
 *)
Theory stepWriteFootprint
Ancestors
  stepWriteFootprintRun unitMemInv contextRawReachable contextCodegenRel codegenRel
  venomExecSemantics venomState venomInst

(* TOP-LEVEL.  Intuition: no premise is needed.  A non-INVOKE instruction's
   step_inst_base changes vs_memory only inside its
   source_memory_write_ranges (read_byte reads 0 past the end, so memory
   expansion changes no byte).  An INVOKE that steps OK merges the
   callee's final memory (merge_callee_state); every instruction the
   callee's run_blocks executes is raw_reachable (the callee rule enters
   it, the next and block rules follow exec_block and run_blocks), and a
   byte that differs at the end differs across some single step of that
   run.  A callee run that executes a revert forwarding's RETURNDATACOPY
   goes on through ASSIGNs to the pair's REVERT in the same block, so it
   ends in Abort or Error, never IntRet, and the INVOKE does not step OK. *)
Theorem step_write_footprint_holds:
  !ctx vs. step_write_footprint ctx vs
Proof
  rw[step_write_footprint_def] >>
  spose_not_then assume_tac >>
  `~footprint_covers vs ctx i` by (simp[footprint_covers_def] >> metis_tac[]) >>
  qpat_x_assum `!fn2 inst2 s2 off len. _` kall_tac >>
  metis_tac[cj 1 run_defs_byte_frame]
QED
