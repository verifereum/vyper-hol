(* Counted local-write consumers: simulation and ghost share one endpoint. *)
Theory assignBasePtrLocalContinuation
Ancestors assignBasePtrLocalLanding assignBasePtrLocalSemantic
  bodyPtrDefs vyperLookup compileEnv localPtrsProps typedMemoryCopy
  exprLoweringProps exprSimBufferStore valueEncoding venomState finite_map fragGasPathPtr

Theorem assign_base_local_ghost_value[local]:
  ghost_inv d cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
    G tn t /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p t = SOME dst ==>
  val_in_memory entry.type v (w2n dst) t.vs_memory
Proof
  strip_tac >>
  `lookup_scopes id pre = NONE` by metis_tac[find_containing_scope_pre_none] >>
  `lookup_scopes id (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) =
    SOME (entry with <|value := v; popped := []|>)` by simp[lookup_scopes_update] >>
  fs[ghost_inv_def] >>
  first_x_assum drule_all >> simp[mem_agree_outside_def]
QED

Theorem assign_base_flat_local_continuation_ptr:
  !src p sa sb fn s a dst n G tn D ctx PG v d cenv cx es
    id pre sc entry rest sz.
    n < dimword (:256) /\
    compile_copy_memory (Var p) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\ lookup_var p s = SOME dst /\
    ptr_covers G tn src s n /\ ptr_covers G tn p s n /\
    val_wf entry.type v /\ val_footprint entry.type v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory entry.type v (w2n a) m) /\
    ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\
    n <= sz /\ n <= type_memory_size entry.type /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      stmt_state_rel ctx fn cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
      ghost_inv d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        Gf tf u /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_flat_local_landing_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var p u = SOME dst` by metis_tac[] >>
  `val_in_memory entry.type v (w2n dst) u.vs_memory` by
    (drule_all assign_base_local_ghost_value >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule buffer_copy_memory_shape >> simp[same_blocks_def] >> metis_tac[]) >>
  drule_all assign_base_local_write_state_post >> strip_tac >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> simp[] >> metis_tac[]
QED

Theorem assign_base_bytes_local_continuation_ptr:
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
    ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\
    32 + 32 * word_size len <= sz /\
    32 + 32 * word_size len <= type_memory_size entry.type /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      stmt_state_rel ctx fn cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
      ghost_inv d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        Gf tf u /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_bytes_local_landing_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `lookup_var p u = SOME dst` by metis_tac[] >>
  `val_in_memory entry.type v (w2n dst) u.vs_memory` by
    (drule_all assign_base_local_ghost_value >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule buffer_store_bytestring_shape >> simp[same_blocks_def] >> metis_tac[]) >>
  drule_all assign_base_local_write_state_post >> strip_tac >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> simp[] >> metis_tac[]
QED
