(* Copy staging retains ownership and gas execution at the same endpoint. *)
Theory tupleAssignImmutableDeployStageOwned
Ancestors
  tupleAssignImmutableDeployStageBoundary tuplePlaceStage tupleStageProps
  stmtLowering context emitHelper compileEnv
Libs
  monadsyntax

Theorem tuple_immutable_stage_owned_path:
  (do buf <- compile_alloc_buffer sz;
      emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
      comp_return buf.buf_operand od) sa = (staged,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= sz /\ sz < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. eval_operand staged t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    stmt_state_rel ctx func cenv cx es t /\
    (!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
      w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!x. staged = Var x ==> not_fresh_at sb x) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_marked_path F ctx func s 0 (OK t) /\
    alloca_frame cenv es sa s cenv es t
Proof
  strip_tac >> drule_all tuple_place_stage_path >> strip_tac >>
  drule_all tuple_stage_copy_parts >> strip_tac >>
  qexistsl [`t`, `w`] >> simp[] >>
  gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, comp_return_def, emit_def] >> metis_tac[]
QED
