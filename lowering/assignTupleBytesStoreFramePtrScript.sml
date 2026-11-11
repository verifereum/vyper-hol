(* Bytestring landing with its runtime-sized exterior frame retained. *)
Theory assignTupleBytesStoreFramePtr
Ancestors assignBasePtrLocalLanding assignBasePtrBytesPost assignBasePtrScopePost
  typedMemoryCopy bodyPtrDefs compileEnv localPtrsProps venomState
  venomExecSemantics ptrDiscipline words finite_map pred_set valueEncoding
  valueEncodingDefs exprLoweringProps fragExec context fragGasPathPtr

Theorem tuple_bytes_local_landing_frame_ptr:
  !src p sa sb fn s a dst len G tn D ctx PG v d cenv cx es
    id pre sc entry rest sz.
    compile_store_bytestring (Var src) (Var p) sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa p /\
    lookup_var src s = SOME a /\ lookup_var p s = SOME dst /\
    mload (w2n a) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) /\
    ptr_covers G tn src s 32 /\
    ptr_covers G tn src s (32 + 32 * word_size len) /\
    ptr_covers G tn p s (32 + 32 * word_size len) /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    val_wf entry.type v /\ val_footprint entry.type v <= 32 + 32 * word_size len /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory entry.type v (w2n a) m) /\
    ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\
    32 + 32 * word_size len <= sz /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u.vs_prev_bb = s.vs_prev_bb /\
      typed_copy_state_frame sa (w2n dst) (32 + 32 * word_size len) s u /\
      ghost_inv d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        Gf tf u /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n dst <= i /\ i < w2n dst + (32 + 32 * word_size len)) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_store_bytestring_robust_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `stor_taint_ok cx tf u` by
    (fs[ghost_inv_def, stor_taint_ok_def, typed_copy_state_frame_def,
        venom_state_component_equality]) >>
  `!i. ~(w2n dst <= i /\ i < w2n dst + (32 + 32 * word_size len)) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> `i < w2n dst \/ w2n dst + (32 + 32 * word_size len) <= i`
       by decide_tac >> metis_tac[]) >>
  drule_all assign_base_local_scope_ghost_post >> strip_tac >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> simp[]
QED
