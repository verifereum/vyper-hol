(* Allocation history for the scalar instructions in an AugAssign prefix. *)
Theory augAssignFullHistory
Ancestors
  bodyFullUnwrapRun emitHelperProps allocaHistory
  exprLoweringProps compileEnv venomExecSemantics venomInst venomState

Theorem augassign_emit_word_history:
  emit_op opc args sa = (Var out,sb) /\
  step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
    OK (update_var out w s) /\
  opc <> INVOKE /\ ~is_terminator opc /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func
    (update_var out w (s with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qspecl_then [`emitted_insts sa sb`, `sa`, `sb`, `s`, `update_var out w s`]
    mp_tac emitted_alloca_history >>
  gvs[same_blocks_def, run_inst_seq_def, update_var_def]
QED

Theorem augassign_emit_void_history:
  emit_void opc args sa = ((),sb) /\
  step_inst_base (mk_inst sa.cs_next_id opc args []) s = OK t /\
  ~is_terminator opc /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qspecl_then [`emitted_insts sa sb`, `sa`, `sb`, `s`, `t`]
    mp_tac emitted_alloca_history >>
  gvs[same_blocks_def, run_inst_seq_def]
QED
