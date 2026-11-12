(* Empty length-word values need only a clean zero header, not clean padding. *)
Theory assignBasePtrEmptyStore
Ancestors wordLoadStorePtr assignBasePtrScopePost assignTuplePtrStoreWord assignTuplePtrStoreHead
  annAssignPtrStore stmtSimDeclMem typedCopyPtr bodyPtrDefs exprSimMemoryTransport
  valueEncoding valueEncodingProps valueEncodingProofs venomMemProofs
  venomState venomExecSemantics venomInst emitHelper context compileEnv
  ptrDiscipline pred_set words finite_map ghostPcTransportPtr
  assignBasePtrLiteralOutcome vyperLookup vyperState

Theorem assign_base_empty_header_robust:
  !tenv ty tv off s dirty mem.
    has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
    mem_agree_outside (dirty DIFF {i | off <= i /\ i < off+32})
      (mstore off 0w s).vs_memory mem ==>
    val_in_memory tv (default_value tv) off mem
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at off 32 (mstore off 0w (s with vs_memory := mem)).vs_memory =
   mem_bytes_at off 32 mem` by
    (irule annassign_clean_store_observation_ptr >>
     goal_assum (drule_at Any)) >>
  `mem_word_at off mem = 0w` by
    (drule memory_window_word >> simp[mstore_mem_word_at_same]) >>
  drule_all memory_length_word_layout >> simp[]
QED

Theorem assign_base_empty_local_store_path:
  !d cenv cx es G tn s id pre sc entry rest p sz a sa sb fn ctx PG D ty tv.
    ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME a /\ entry.type = tv /\
    has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n a) sz /\ 32 <= sz /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    emit_inst MSTORE [Var p; Lit 0w] [] sa = ((),sb) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?tf t. gas_path_ptr D 0 ctx fn PG G tn s 0 G tf (OK t) /\
      t = (mstore (w2n a) 0w s with vs_inst_idx := SUC s.vs_inst_idx) /\
      ghost_inv d cenv cx
        (es with scopes := pre ++
          (sc |+ (id,entry with <|value := default_value tv; popped := []|>)) :: rest)
        G tf t /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `ptr_covers G tn p s 32` by
    (`ptr_covers G tn p s sz` by metis_tac[ghost_inv_def] >>
     fs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  `!x. not_fresh_at sa x ==>
    lookup_var x (mstore (w2n a) 0w s) = lookup_var x s /\
    FLOOKUP G x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[mstore_def, lookup_var_def, op_taint_def] >>
  `!mem. mem_agree_outside tf.t_mem (mstore (w2n a) 0w s).vs_memory mem ==>
    val_in_memory entry.type (default_value tv) (w2n a) mem` by
    (rpt strip_tac >> simp[] >> irule assign_base_empty_header_robust >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`tn.t_mem`, `s`] >> gvs[]) >>
  suspend "ghost"
QED

Resume assign_base_empty_local_store_path[ghost]:
  `!i. ~(w2n a <= i /\ i < w2n a+32) ==>
    mem_bytes_at i 1 (mstore (w2n a) 0w s).vs_memory =
      mem_bytes_at i 1 s.vs_memory /\ (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `stor_taint_ok cx tf (mstore (w2n a) 0w s)` by
    (simp[Abbr `tf`] >> irule mstore_storage_taint_frame_ptr >>
     simp[] >> metis_tac[ghost_inv_def]) >>
  drule_all assign_base_local_scope_ghost_post >> strip_tac >>
  drule_all emit_mstore_zero_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qexistsl_tac [`tf`, `mstore (w2n a) 0w s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[assign_base_ptr_ghost_index, lookup_var_def, mstore_def] >>
  gvs[Abbr `tf`, mstore_def]
QED

Finalise assign_base_empty_local_store_path
