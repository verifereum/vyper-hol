(* Concrete scalar-local store ghost integration. *)
Theory assignTuplePtrStoreHead
Ancestors
  wordLoadStorePtr assignTuplePtrWordLocals assignTuplePtrCopyEndpoint typedCopyPtr bodyPtrDefs ptrDiscipline
  venomInst venomState vyperLookup compileEnv loweringStateRelDefs finite_map pred_set list
  assignTuplePtrStoreWord tupleTargetStoreRun tupleTargetStoreProps
  stmtSimAssignStore exprSimProps context emitHelperProps emitHelper fragExec
  vyperState valueEncodingProps localPtrsProps exprLoweringProps stmtSimDeclStore

Theorem mstore_storage_taint_frame_ptr:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ stor_taint_ok cx tn s ==>
  stor_taint_ok cx
    (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
       (mstore (w2n a) w s) tn) (mstore (w2n a) w s)
Proof
  strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  gvs[stor_taint_ok_def, mstore_def] >>
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Theorem local_mstore_ghost_update_ptr:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\
  local_region cenv es.scopes s id (w2n a) sz /\ 32 <= sz /\
  eval_operand value s = SOME word /\ op_taint tn value = {} /\
  (!m. mem_agree_outside (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})
     (mstore (w2n a) word s).vs_memory m ==>
       val_in_memory entry.type v (w2n a) m) ==>
  ghost_inv d cenv cx
    (es with scopes := pre ++
      (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
    G (step_taint (mk_inst iid MSTORE [Var p; value] []) s
         (mstore (w2n a) word s) tn) (mstore (w2n a) word s)
Proof
  strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  irule ghost_inv_local_word_update_ptr >> simp[] >>
  conj_tac
  >- (irule mstore_storage_taint_frame_ptr >> simp[] >>
      metis_tac[ghost_inv_def]) >>
  qexistsl_tac [`sz`, `es`, `func`, `id`, `tn`, `entry.type`, `v`] >>
  simp[op_taint_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `name = id`
  >- (gvs[] >> drule find_containing_scope_pre_none >> strip_tac >>
      gvs[lookup_scopes_update]) >>
  drule find_containing_scope_structure >> strip_tac >>
  fs[lookup_scopes_update_other] >>
  qpat_x_assum `es.scopes = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem tuple_target_local_word_head_path_ptr:
  !ctx func cenv cx es es' s id ty tv v op st sf G tn d D PG.
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) /\
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') /\
    tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv /\
    tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v /\
    value_has_type tv v /\ val_wf tv v /\ is_word_type ty /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~ctx_has_dalloca ctx /\
    ghost_inv d cenv cx es G tn s /\ ptr_val_ok cx ty v op G tn s ==>
    ?t idp sz entry dw G' tn'.
      stmt_state_rel ctx func cenv cx es' t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var idp) sz) /\
      lookup_var idp s = SOME dw /\
      (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      ghost_inv d cenv cx es' G' tn' t /\
      (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
      tn'.t_mem SUBSET tn.t_mem /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + 32) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[tuple_target_aligned_local, tuple_target_layout_local] >>
  drule_all tuple_target_local_assignment >> strip_tac >>
  drule_all tuple_store_local_singleton_code >> simp[] >> strip_tac >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `local_region cenv es.scopes s id (w2n dw) sz` by
    simp[local_region_def] >>
  `type_memory_size entry.type = 32` by
    metis_tac[typed_word_store] >>
  `32 <= sz` by (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  suspend "finish"
QED

Resume tuple_target_local_word_head_path_ptr[finish]:
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` kall_tac >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` kall_tac >>
  `!m. mem_agree_outside
      (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw+32})
      (mstore (w2n dw) (typed_val_to_w256 entry.type v) s).vs_memory m ==>
      val_in_memory entry.type v (w2n dw) m` by
    (rpt strip_tac >> irule typed_word_store_robust_ptr >> metis_tac[]) >>
  drule_all local_mstore_ghost_update_ptr >> strip_tac >>
  `ptr_covers G tn p s 32` by
    (`ptr_covers G tn p s sz` by metis_tac[ghost_inv_def] >>
     gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `emit_inst MSTORE [Var p; op] [] st = ((),sf)` by
    gvs[emit_void_def, emit_inst_def] >>
  drule_all emit_mstore_zero_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  drule_all mstore_ghost_frame >> strip_tac >>
  `sf.cs_current_bb = st.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  suspend "endpoint"
QED

Resume tuple_target_local_word_head_path_ptr[endpoint]:
  `(mstore (w2n dw) (typed_val_to_w256 entry.type v) s).vs_halted = s.vs_halted /\
   (mstore (w2n dw) (typed_val_to_w256 entry.type v) s).vs_current_bb = s.vs_current_bb /\
   (mstore (w2n dw) (typed_val_to_w256 entry.type v) s).vs_allocas = s.vs_allocas /\
   (!x. lookup_var x (mstore (w2n dw) (typed_val_to_w256 entry.type v) s) =
        lookup_var x s)` by simp[mstore_def, lookup_var_def] >>
  `!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
    mem_bytes_at a len
      (mstore (w2n dw) (typed_val_to_w256 entry.type v) s).vs_memory =
    mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  qexistsl_tac [`mstore (w2n dw) (typed_val_to_w256 entry.type v) s with
                   vs_inst_idx := SUC s.vs_inst_idx`, `dw`, `G`,
    `step_taint (mk_inst st.cs_next_id MSTORE [Var p; op] []) s
       (mstore (w2n dw) (typed_val_to_w256 entry.type v) s) tn`] >>
  simp[stmt_state_rel_inst_idx, op_taint_def, DIFF_SUBSET] >>
  gvs[lookup_var_def, op_taint_def] >>
  suspend "ghost_cursor"

QED

Resume tuple_target_local_word_head_path_ptr[ghost_cursor]:
  simp[ghost_inv_inst_idx] >> metis_tac[]
QED

Finalise tuple_target_local_word_head_path_ptr

