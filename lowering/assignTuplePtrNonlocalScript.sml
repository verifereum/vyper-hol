(* Nonlocal tuple destinations: literal slots and literal struct-field ADDs. *)
Theory assignTuplePtrNonlocal
Ancestors
  assignTuplePtrField assignTuplePtrStorage tupleTargetStoreRun tupleTargetStoreProps
  stmtSimAssignStorage tupleAssignParts stmtLowering exprLowering
  compileEnv context valueEncodingProps valueCopy exprSimProps emitHelper
  valueEncoding vyperTyping venomExecSemantics ptrDiscipline venomState

Theorem tuple_target_nonlocal_head_path_ptr:
  compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
  assign_tuple_targets cx g v es = (INL (),es') /\
  tuple_target_aligned cenv cx g ty tv /\
  (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) ==>
  ?t G' tn'. stmt_state_rel ctx func cenv cx es' t /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ghost_inv d cenv cx es' G' tn' t /\ tn'.t_mem = tn.t_mem /\
    (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- (drule_all tuple_target_toplevel_place >>
      disch_then (qspec_then `es` assume_tac) >>
      drule_all tuple_target_storage_assignment >> strip_tac >>
      drule_all compile_get_target_ptr_toplevel >>
      disch_then (qspec_then `st` assume_tac) >> gvs[] >>
      drule_all tuple_store_word_step >> strip_tac >>
      qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      drule_all encode_value_word_typed >> strip_tac >>
      `eval_operand (Lit (n2w k)) s = SOME (n2w k) /\ op_taint tn (Lit (n2w k)) = {}` by
        simp[eval_operand_def, op_taint_def] >>
      drule_all tuple_storage_store_head_path_ptr >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl [`t`, `G`, `tn'`] >> simp[]) >>
  drule_all tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tuple_target_storage_assignment >> strip_tac >>
  Cases_on `emit_op ADD [Lit (n2w k); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] st` >>
  rename1 `emit_op ADD _ st = (dst,sp)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  drule_all encode_value_word_typed >> strip_tac >>
  drule_all tuple_field_storage_head_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`t`, `G'`, `tn'`] >> simp[]
QED
