(* Final local scope post for a clean scalar write. Storage/transient
   writes already use assign_base_clean_storage_ghost; do not duplicate it. *)
Theory assignBasePtrScalarPost
Ancestors wordLoadStorePtr assignBasePtrLocalStore assignBasePtrCleanStore assignBasePtrCleanStorage assignBasePtrScopePost
  assignBasePtrLiteralOutcome assignBasePtrLiteralGhost typedCopyPtr
  bodyPtrDefs compileEnv localPtrsProps venomState venomExecSemantics
  ptrDiscipline venomInst words finite_map pred_set ghostPcTransportPtr
  venomMemProofs valueEncodingProps assignTuplePtrStoreHead

Theorem assign_base_scalar_local_store_ghost:
  !d cenv cx es G tn s id pre sc entry rest p sz a value w v sa fn PG iid.
    ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\
    local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n a) sz /\ 32 <= sz /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    val_wf entry.type v /\ val_footprint entry.type v <= 32 /\
    val_in_memory entry.type v (w2n a) (mstore (w2n a) w s).vs_memory ==>
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      (step_prov PG G (mk_inst iid MSTORE [Var p; value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst iid MSTORE [Var p; value] []) s (mstore (w2n a) w s) tn)
      (mstore (w2n a) w s) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x (mstore (w2n a) w s) = lookup_var x s /\
      FLOOKUP (step_prov PG G (mk_inst iid MSTORE [Var p; value] [])
        (mstore (w2n a) w s)) x = FLOOKUP G x /\
      op_taint (step_taint (mk_inst iid MSTORE [Var p; value] []) s
        (mstore (w2n a) w s) tn) (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `iid`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  `!x. not_fresh_at sa x ==>
    lookup_var x (mstore (w2n a) w s) = lookup_var x s /\
    FLOOKUP G x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[mstore_def, lookup_var_def, op_taint_def] >>
  `!mem. mem_agree_outside tf.t_mem (mstore (w2n a) w s).vs_memory mem ==>
    val_in_memory entry.type v (w2n a) mem` by
    (simp[] >> rpt strip_tac >>
     irule assign_base_ptr_clean_window_robust_value >> conj_tac >- simp[] >>
     qexistsl_tac [`(mstore (w2n a) w s).vs_memory`, `32`, `tn.t_mem`] >> simp[]) >>
  `!i. ~(w2n a <= i /\ i < w2n a+32) ==>
    mem_bytes_at i 1 (mstore (w2n a) w s).vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `stor_taint_ok cx tf (mstore (w2n a) w s)` by
    (simp[Abbr `tf`] >> irule mstore_storage_taint_frame_ptr >>
     simp[] >> metis_tac[ghost_inv_def]) >>
  drule_all assign_base_local_scope_ghost_post >> simp[]
QED
