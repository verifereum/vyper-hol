(*
 * MakeSSA keeps each block's terminator last and only lengthens blocks,
 * so a REVERT at instruction k of an input block is a REVERT at
 * make_ssa_pos in the output block of the same label.  The pointer
 * discipline's taint row exempts a RETURNDATACOPY right before a REVERT
 * (about_to_revert); this carries the exemption to the output.
 *)
Theory o1ContractMakeSsaPtrPos
Ancestors
  makeSsaCurrentLockstep makeSsaCurrentDefs makeSsaCurrentProps
  makeSsaCurrentCfg makeSsaCurrentRevertForward o1FrameLockstep
  ptrDiscipline contextCodegenRel o1PassContract venomWf venomInst

(* add_phi_nodes_supply only inserts PHIs at the head of a block,
   rename_current_blocks keeps each instruction's opcode and the block
   lengths, and simplify_current_phis_if only rewrites the leading PHIs
   (to PHI, ASSIGN or NOP, keeping the count).  A well-formed block ends
   in a terminator, which is no PHI, so it stays last. *)
Theorem make_ssa_current_fn_block_last:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' ==>
  LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
  (LAST bb'.bb_instructions).inst_opcode =
  (LAST bb.bb_instructions).inst_opcode
Proof
  cheat
QED

Theorem make_ssa_pos_revert:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = REVERT ==>
  make_ssa_pos fn fn' l k < LENGTH bb'.bb_instructions /\
  (EL (make_ssa_pos fn fn' l k) bb'.bb_instructions).inst_opcode = REVERT
Proof
  cheat
QED

(* A paired state of a MakeSSA lockstep sits at make_ssa_pos in the block
   of the same label (lockstep_rel, state_rel); the revert forwarding
   (make_ssa_current_fn_revert_forward_at) and a REVERT right after
   (make_ssa_pos_revert, with make_ssa_pos l (SUC k) = SUC (make_ssa_pos
   l k)) sit at the matching positions of the output block. *)
Theorem make_ssa_lockstep_revert:
  lockstep_sim L C C' fn fn' (make_ssa_pos fn fn') R /\
  R T (inst,s) sg (inst',s') /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
  make_ssa_current_fn t fn = (fn',t') ==>
  (in_revert_forward fn s ==> in_revert_forward fn' s') /\
  (about_to_revert fn inst s ==> about_to_revert fn' inst' s')
Proof
  cheat
QED
