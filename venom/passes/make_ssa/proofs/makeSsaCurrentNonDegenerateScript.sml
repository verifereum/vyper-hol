(*
 * MakeSSA leaves no degenerate PHI.  On PHI-free input (the first O1 run)
 * every PHI of the output is one the pass placed: at a block of the
 * iterated dominance frontier of the variable's definitions where the
 * variable is live.  Such a block joins two paths that carry different
 * definitions, so after renaming the PHI reads two distinct versions,
 * neither its own output.  On PHI input the cleanup collapses every PHI
 * whose non-self inputs are all equal, so each PHI it keeps has two
 * distinct non-self inputs.
 *)
Theory makeSsaCurrentNonDegenerate
Ancestors
  makeSsaDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract makeSsaCurrentNonDegTransport makeSsaCurrentNonDegPhiInput

(* Why it holds (intuition only; the proof's structure is free).

   No entry label: fn' = fn, and make_ssa_input_ok has fn_phis_non_degenerate.

   had_phis (blocks_have_leading_phi fn.fn_blocks): the output blocks are
   simplify_current_phis_if T bbs2.  bb_well_formed keeps PHIs in a block
   prefix, inst_wf gives PHIs one output and phi_well_formed operands, and
   placement and renaming keep both, so every PHI of bbs2 with output [out]
   is in the prefix simplify_current_phi_prefix walks and
   current_phi_values (remove_current_phi_self out ops) = SOME (v::vs).  It
   stays a PHI only when some w in vs differs from v; v and w survive self
   removal, so both differ from out and both are values of phi_pairs ops.

   PHI-free input (had_phis = F, so bbs3 = bbs2 and every output PHI is a
   placed one): a PHI for x at block B was placed because B is in DF(D) for
   a block D that defines x, either originally or by a PHI placed earlier.
   Use this immediate frontier source: D is not B unless B itself has an
   original definition of x.  x is live into B, so by
   fn_defs_reach_uses every predecessor has a reaching definition.  D
   dominates a predecessor p1 of B, so the name renamed in on the edge
   p1 -> B is defined inside D's dominator subtree after B's own PHI (if
   D = B, after B's original definition), hence not out.  B is not the entry
   (first_block_no_preds) and D does not strictly dominate B, so some
   predecessor p2 is dominated by neither D nor B: its name is defined at a
   block dominating p2, hence outside D's subtree (so it differs from p1's
   name) and not B's PHI (so it differs from out).  ssa_form of the output
   (make_ssa_current_fn_wf_ssa) makes definitions and names one-to-one. *)

Theorem make_ssa_current_fn_phis_non_degenerate:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_phis_non_degenerate fn'
Proof
  strip_tac >> Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- (drule_all current_nondeg_phi_input >> simp[]) >>
  drule_all current_nondeg_phi_free_run >> simp[]
QED
