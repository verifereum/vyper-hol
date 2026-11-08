(* Scalar local stores use the source encoding and the destination's layout
   contract; no equality of the two evaluated types is required. *)
Theory assignTuplePtrLocalWordRuntime
Ancestors
  wordLoadStorePtr assignTuplePtrStoreHead assignTuplePtrStoreWord stmtSimAssignStore
  typedCopyPtr bodyPtrDefs compileEnv context emitHelper emitHelperProps
  venomState venomExecSemantics vyperState vyperLookup exprSimProps
  exprLoweringProps stmtSimDeclStore assignTuplePtrCopyEndpoint ptrDiscipline
  valueEncodingProps

Theorem tuple_local_word_runtime_head_ptr:
  emit_void MSTORE [Var p; op] sa = ((),sb) /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ op_taint tn op = {} /\
  store_lays_out tv entry.type v /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME dw /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tn'.
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
    ghost_inv d cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. lookup_var x t = lookup_var x s /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\
    local_region cenv es.scopes s id (w2n dw) sz /\ 32 <= sz /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+32) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn' (OK t)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `lookup_scopes id es.scopes = SOME entry` by metis_tac[find_containing_scope_lookup] >>
  `local_region cenv es.scopes s id (w2n dw) sz` by simp[local_region_def] >>
  `32 <= sz` by (fs[local_ptrs_rel_def, store_lays_out_def] >> metis_tac[]) >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  `!m. mem_agree_outside (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw+32})
    (mstore (w2n dw) (typed_val_to_w256 tv v) s).vs_memory m ==>
    val_in_memory entry.type v (w2n dw) m` by
    metis_tac[store_lays_out_robust_ptr] >>
  drule_all local_mstore_ghost_update_ptr >>
  disch_then (qspec_then `sa.cs_next_id` assume_tac) >>
  `ptr_covers G tn p s 32` by
    (`ptr_covers G tn p s sz` by metis_tac[ghost_inv_def] >>
     fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `emit_inst MSTORE [Var p; op] [] sa = ((),sb)` by gvs[emit_void_def, emit_inst_def] >>
  drule_all emit_mstore_zero_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `(mstore (w2n dw) (typed_val_to_w256 tv v) s).vs_halted = s.vs_halted /\
   (mstore (w2n dw) (typed_val_to_w256 tv v) s).vs_current_bb = s.vs_current_bb /\
   (mstore (w2n dw) (typed_val_to_w256 tv v) s).vs_allocas = s.vs_allocas /\
   (!x. lookup_var x (mstore (w2n dw) (typed_val_to_w256 tv v) s) = lookup_var x s)` by
    simp[mstore_def, lookup_var_def] >>
  qexistsl_tac [`mstore (w2n dw) (typed_val_to_w256 tv v) s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst sa.cs_next_id MSTORE [Var p; op] []) s
      (mstore (w2n dw) (typed_val_to_w256 tv v) s) tn`] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx, lookup_var_def, op_taint_def] >>
  reverse conj_tac >- gvs[] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
