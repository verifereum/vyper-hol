(* Final writes into an existing local: consume the actual counted copy
   endpoint, without asking for ghost_kept on the overwritten interval. *)
Theory assignBasePtrLocalLanding
Ancestors assignBasePtrBytesPost assignBasePtrScopePost
  assignBasePtrCopyPath assignBasePtrMcopyTransport typedMemoryCopy
  bodyPtrDefs compileEnv localPtrsProps venomState venomExecSemantics
  ptrDiscipline words finite_map pred_set valueEncoding valueEncodingDefs
  exprLoweringProps fragExec context exprSimBufferStore fragGasPathPtr

Theorem assign_base_bytes_local_landing_ptr:
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
        op_taint tf (Var x) = op_taint tn (Var x))
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

Theorem assign_base_flat_local_landing_ptr:
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
    ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\ n <= sz /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u.vs_prev_bb = s.vs_prev_bb /\
      typed_copy_state_frame sa (w2n dst) n s u /\
      ghost_inv d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        Gf tf u /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory entry.type v (w2n dst) m` by
        (rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
         qexistsl_tac [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
      `stor_taint_ok cx tn s` by fs[ghost_inv_def] >>
      `!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s /\
        FLOOKUP G x = FLOOKUP G x /\ op_taint tn (Var x) = op_taint tn (Var x)`
        by simp[] >>
      drule_all (SRULE [] (Q.INST [`n` |-> `0`, `t` |-> `s`,
        `Gf` |-> `G`, `tf` |-> `tn`] (SPEC_ALL assign_base_local_scope_ghost_post))) >>
      strip_tac >> qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules]) >>
  `0 < n` by decide_tac >>
  drule_all assign_base_copy_memory_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] assume_tac) >>
  qabbrev_tac `u = mcopy (w2n dst) (w2n a) n s` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id MCOPY [Var p;Var src;Lit (n2w n)] []) s u tn` >>
  `eval_operand (Var p) s = SOME dst /\ eval_operand (Var src) s = SOME a /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  `u = mcopy (w2n dst) (w2n a) (w2n (n2w n : bytes32)) s /\
   tf = step_taint (mk_inst sa.cs_next_id MCOPY [Var p;Var src;Lit (n2w n)] []) s u tn`
    by simp[Abbr `u`, Abbr `tf`] >>
  `val_footprint entry.type v <= w2n (n2w n : bytes32)` by simp[] >>
  FREEZE_THEN drule_all (SRULE [] (Q.SPECL [`Var p`, `Var src`, `Lit (n2w n)`, `s`, `s`]
    assign_base_bytes_mcopy_post)) >>
  disch_then (qspecl_then [`sa.cs_next_id`, `PG`, `G`, `sa`, `LENGTH sb.cs_current_insts`] strip_assume_tac) >>
  qpat_x_assum `u = mcopy _ _ _ _` kall_tac >>
  qpat_x_assum `tf = step_taint _ _ _ _` kall_tac >>
  fs[Abbr `u`, Abbr `tf`] >> gs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G tf (OK t)` >>
  `stor_taint_ok cx tf t` by
    (fs[ghost_inv_def, stor_taint_ok_def, typed_copy_state_frame_def,
        venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[op_taint_def] >>
  `!i. ~(w2n dst <= i /\ i < w2n dst+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> `i < w2n dst \/ w2n dst+n <= i` by decide_tac >>
     fs[Abbr `t`] >> metis_tac[]) >>
  `!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
     val_in_memory entry.type v (w2n dst) m` by simp[Abbr `t`] >>
  drule_all assign_base_local_scope_ghost_post >> strip_tac >>
  qexistsl_tac [`G`, `tf`, `t`] >> simp[] >>
  fs[Abbr `t`, mcopy_def, write_memory_with_expansion_def] >>
  drule buffer_copy_memory_shape >> simp[same_blocks_def]
QED
