(*
 * MakeSSA keeps revert-forward pairs: a block's instruction at index k
 * that is half of a revert forwarding (RETURNDATACOPY then REVERT, with
 * only ASSIGNs between and operands equal up to ASSIGN copies) is still
 * one at the same instruction of the output block, which sits
 * LENGTH bb' - LENGTH bb further on (the inserted PHIs).
 *
 * Intuition: PHI insertion only prepends PHIs, cleanup only rewrites the
 * leading PHI prefix (keeping its length), and renaming keeps opcodes and
 * maps the variables at each program point injectively (an original
 * spelling or a fresh supply name), so the ASSIGN chains that
 * same_after_assigns and resolve_block_assigns follow are renamed alike.
 *)
Theory makeSsaCurrentRevertForward
Ancestors
  makeSsaCurrentDefs contextCodegenRel venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract makeSsaRfPipeline makeSsaRfTransport

Theorem make_ssa_current_fn_revert_forward_at:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  revert_forward_at bb k ==>
  LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
  revert_forward_at bb'
    (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
Proof
  strip_tac >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  drule_all rf_make_ssa_current_fn_certificate >> strip_tac >>
  irule rf_phase_certificate_at >> metis_tac[]
QED
