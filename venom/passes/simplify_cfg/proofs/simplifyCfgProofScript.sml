(*
 * Simplify CFG Pass — Correctness Proof
 *
 * Block merging, trivial jump bypass, unreachable block removal and PHI
 * fixup preserve a function's runs from its entry, and every state the
 * output reaches corresponds to one the input reaches, away from
 * revert-forward pairs too.
 *)

Theory simplifyCfgProof
Ancestors
  simplifyCfgDefs o1PassLift unitShapeDefs venomWf
  simplifyCfgRoundSemantics simplifyCfgStaticInterface simplifyCfgSimTools
  simplifyCfgShapeCore simplifyCfgFrameRf

(* Merged blocks need less fuel, so the fuel is existential each way.
   fn_shape_ok bans DJMP and keeps labels out of every terminator operand
   but a jump target, so a terminator merged away (one distinct successor)
   could neither fail nor halt. *)
Theorem simplify_cfg_fn_correct:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_bisim fn (simplify_cfg_fn fn)
Proof
  strip_tac >>
  qspecl_then [`LENGTH fn.fn_blocks`, `fn`] mp_tac scfg_iter_contract >>
  simp[scfg_static_def, fn_shape_ok_scfg_shape, simplify_cfg_fn_def,
       simplify_cfg_fn_with_labels_def]
QED

(* Every state the output reaches in C' (including on runs that later
   fail) corresponds to one the input reaches in C from the same entry
   state; C and C' run each function alike. *)
Theorem simplify_cfg_frame_sim:
  ctx_bisim C C' /\
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  frame_sim L C C' fn (simplify_cfg_fn fn)
Proof
  strip_tac >> irule frame_sim_trans >> qexistsl_tac [`C'`, `fn`] >>
  simp[frame_sim_ctx_bisim] >>
  qspecl_then [`LENGTH fn.fn_blocks`, `fn`] mp_tac scfg_iter_contract >>
  simp[scfg_static_def, fn_shape_ok_scfg_shape, simplify_cfg_fn_def,
       simplify_cfg_fn_with_labels_def]
QED

(* A target state that touches memory outside a revert-forward pair
   (RETURNDATACOPY [p; 0; rds] then REVERT [p; rds]) corresponds to a source
   state outside one too.  The pass never separates the two instructions of
   a pair: both sit in one block, REVERT ends it, and merging only puts a
   predecessor's non-terminators in front.  Merging can create a pair,
   which the statement allows. *)
Theorem simplify_cfg_frame_sim_rf:
  ctx_bisim C C' /\
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  frame_sim_rf L C C' fn (simplify_cfg_fn fn)
Proof
  strip_tac >> irule frame_sim_rf_trans >>
  qexistsl_tac [`C'`, `fn`] >> simp[scfg_frame_sim_rf_ctx_bisim] >>
  qspecl_then [`LENGTH fn.fn_blocks`, `fn`] mp_tac
    (Q.INST [`C` |-> `C'`] scfg_iter_frame_sim_rf) >>
  simp[scfg_static_def, fn_shape_ok_scfg_shape, simplify_cfg_fn_def,
       simplify_cfg_fn_with_labels_def]
QED
