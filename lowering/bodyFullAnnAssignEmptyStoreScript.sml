(* Joint empty declaration zero-length store and binding boundary. *)
Theory bodyFullAnnAssignEmptyStore
Ancestors
  bodyFullAnnAssignMemoryPost gasOutcomeFullStmts
  fragGasOriginPtr fragGasOrigin fragGasMode bodyPtrDefs
  stmtSimDeclSource annAssignPtrEmptySource
  emitHelperProps exprLoweringProps compileEnv
  venomState venomInst finite_map arithmetic
  stmtSimDeclMem valueEncodingProps typedMemoryCopy logStoreDataOriginPtr
  context vyperValue vyperTyping valueEncoding valueEncodingDefs ptrDiscipline
  vyperTypeDefaults loweringStateRelDefs bodyMemBopRestWordPath bodyMemoryDefs

Theorem annassign_empty_full_store_path:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  has_length_word typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
  lookup_var p s = SOME w /\ type_memory_size tyv <= cap /\
  ptr_covers G tn p s cap /\ w2n w + cap < dimword (:256) /\
  w2n w + cap <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code b sf func /\ ~s.vs_halted /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory tyv (default_value tyv) (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv (default_value tyv) (w2n w) mem) /\
    typed_copy_state_frame b (w2n w) (type_memory_size tyv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n w <= i /\ i < w2n w + type_memory_size tyv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `mem_word_at (w2n w) (mstore (w2n w) 0w s).vs_memory = 0w` by
    simp[mstore_mem_word_at_same] >>
  drule_all memory_length_word_layout >> strip_tac >>
  `ptr_covers G tn p s 32` by (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `compile_store_memory ce (Lit 0w) (Var p) (BaseT BoolT) (BaseT BoolT) b = ((),sf)` by
    simp[compile_store_memory_def, is_word_type_def] >>
  `w2n w + 32 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all (SRULE [evaluate_type_def, is_word_type_def, value_has_type_def,
       eval_operand_def, op_taint_def, typed_val_to_w256_def, val_to_w256_def]
    (Q.INST [`tenv` |-> `get_tenv cx`, `dtv` |-> `BaseTV BoolT`,
             `v` |-> `BoolV F`, `src` |-> `Lit 0w`, `dty` |-> `BaseT BoolT`]
      (SPEC_ALL compile_store_memory_word_origin_ptr_path))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==> mem_word_at (w2n w) mem = 0w` by
    (rpt strip_tac >> first_x_assum drule >> simp[val_in_memory_def, val_to_w256_def]) >>
  rpt conj_tac
  >- (irule (cj 1 memory_length_word_layout) >> metis_tac[val_in_memory_def, val_to_w256_def])
  >- (rpt strip_tac >> irule (cj 1 memory_length_word_layout) >> metis_tac[])
  >- (irule typed_copy_state_frame_subinterval >> goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  fs[typed_copy_state_frame_def, op_taint_def]
QED

Theorem annassign_empty_full_store_post:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es0 /\
  has_length_word typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
  lookup_var p s = SOME w /\ type_memory_size tyv <= cap /\
  ptr_covers G tn p s cap /\ w2n w + cap < dimword (:256) /\
  w2n w + cap <= s.vs_alloca_next /\ lo <= w2n w /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code b sf func /\ ~s.vs_halted /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  stmt_state_rel H ctx func ce cx es s /\ ghost_inv_at D lo d ce cx es G tn s /\
  fn_inst_ids_distinct func /\ es.scopes = sc :: rest /\
  lookup_scopes id es.scopes = NONE /\ FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  not_local_ptr ce es.scopes p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,cap) /\
  (!q. q = p \/ ~not_local_ptr ce es.scopes q ==> not_fresh_at b q) /\
  local_ptrs_reserved ce b /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  return_buf_frame d ce b s /\ alloca_history func s ==>
  ?t Gf tf.
    (!D'. gas_origin_ptr_path (D',lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    stmt_state_rel H ctx func ce cx
      (es with scopes := (sc |+ (id,<|assignable := T; type := tyv;
        value := default_value tyv; popped := []|>)) :: rest) t /\
    ghost_inv_at D lo d ce cx
      (es with scopes := (sc |+ (id,<|assignable := T; type := tyv;
        value := default_value tyv; popped := []|>)) :: rest) Gf tf t /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all annassign_empty_full_store_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `val_wf tyv (default_value tyv) /\ value_has_type tyv (default_value tyv)` by
    metis_tac[default_value_has_type_thm, memoryValueFrameTheory.default_value_val_wf] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by simp[] >>
  `stmt_state_rel H ctx func ce cx
    (es with scopes := (sc |+ (id,<|assignable := T; type := tyv;
      value := default_value tyv; popped := []|>)) :: rest) t /\
   ghost_inv_at D lo d ce cx
    (es with scopes := (sc |+ (id,<|assignable := T; type := tyv;
      value := default_value tyv; popped := []|>)) :: rest) Gf tf t` by
    (irule body_full_annassign_memory_post >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `gas_origin_ptr_path _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[ADD_COMM] >>
     qexists_tac `b` >> gvs[] >> metis_tac[]) >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  `return_buf_frame d ce sf t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`b`] >> simp[] >>
     drule emitted_insts_emit_void >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  fs[typed_copy_state_frame_def, venom_state_component_equality]
QED

