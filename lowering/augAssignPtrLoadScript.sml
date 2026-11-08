(* Counted load boundaries; semantic liveness is supplied separately. *)
Theory augAssignPtrLoad
Ancestors
  augAssignPtrInterfaces typedCopyPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs
  venomInst venomState venomExecSemantics ptrSafeRun representationCleanPtr
  finite_map vyperValue emitHelperProps exprSimMemoryPath
  emitHelper compileEnv fragExec loweringPosts ptrDiscipline codegenRel
  loweringSlice exprLoweringProps valueEncodingProps exprSimNameWord stmtFragPtr
  accountsRelProps contextCodegenRel exprSimUnwrap

Theorem mload_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  ptr_covers G tn src s 32 /\
  step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) u)
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MLOAD [Var src] [tmp]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  mp_tac (Q.INST [`lo` |-> `0`,
    `i` |-> `mk_inst id MLOAD [Var src] [tmp]`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[update_var_def] >>
  `step_inst 0 ctx (mk_inst id MLOAD [Var src] [tmp]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_halted >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem ghost_inv_scalar_local_clean:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\
  word_value entry.value ==>
  !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >> irule robust_val_in_memory_prim_clean >>
  qexistsl_tac [`w2n a`, `s.vs_memory`, `entry.type`, `entry.value`] >>
  simp[GSYM word_value_def] >>
  gvs[ghost_inv_def] >> metis_tac[]
QED

Theorem load_ambient_frame:
  (opc = MLOAD \/ opc = SLOAD \/ opc = TLOAD) /\
  (!p. not_fresh_at sa p ==> p <> out) ==>
  (step_taint (mk_inst id opc [arg] [out]) s (update_var out v s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [arg] [out]) s (update_var out v s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [arg] [out]) s (update_var out v s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [arg] [out]) s (update_var out v s) tn).t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [arg] [out])
      (update_var out v s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id opc [arg] [out]) s (update_var out v s) tn) (Var p) =
      op_taint tn (Var p))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out v s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_taint_def, set_var_taint_def, adopt_reset_def, imm_taint_def,
       mk_inst_def, source_memory_write_ranges_def, step_writes_def,
       step_prov_def, set_prov_def, out_prov_def] >>
  simp[mem_taint_def, store_taint_def, range_bytes_def,
       source_memory_write_ranges_def, step_writes_def, mk_inst_def,
       written_taint_def] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_mload_path_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = update_var out (mload (w2n a) s)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    lookup_var out sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    op_prov Gf (Var out) = NONE
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n a) s) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all mload_path_ptr >> strip_tac >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s)`,
    `step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn`,
    `(update_var out (mload (w2n a) s) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  `op_taint (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
     (update_var out (mload (w2n a) s) s) tn) (Var out) = {}` by
    (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
  `op_prov (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s)) (Var out) = NONE` by
    (irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_other_none >> simp[mk_inst_def]) >>
  simp[load_ambient_frame, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       arithmeticTheory.ADD1] >>
  irule (SRULE [update_var_def] load_ambient_frame) >> metis_tac[]
QED

(* A load changes only a fresh temporary.  Keep the ambient proof separate
   from the instruction path so it also applies to field/storage loads. *)
Theorem ghost_inv_load_frame:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!p. not_fresh_at sa p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint un (Var p) = op_taint tn (Var p)) /\
  t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
  un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es H un t
Proof
  strip_tac >>
  gvs[ghost_inv_def, local_ptrs_reserved_def, ret_pc_ok_def,
      stor_taint_ok_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa p` by metis_tac[] >>
      gvs[ptr_covers_def] >> metis_tac[]) >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Theorem ghost_inv_word_local_inputs:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  word_value entry.value ==>
  ?a. lookup_var p s = SOME a /\ ptr_covers G tn p s 32 /\
    mload (w2n a) s = val_to_w256 entry.value /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `?a. lookup_var p s = SOME a /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n a) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  `32 <= sz` by
    (gvs[word_value_def, valueEncodingTheory.val_wf_def] >> decide_tac) >>
  qexists_tac `a` >> simp[] >> conj_tac
  >- (`ptr_covers G tn p s sz` by (gvs[ghost_inv_def] >> metis_tac[]) >>
      gvs[ptr_covers_def] >> qexistsl_tac [`a`, `b`, `sz'`] >> simp[] >>
      decide_tac) >>
  conj_tac
  >- (gvs[word_value_def] >>
      gvs[val_in_memory_prim, mem_word_at_eq_mload]) >>
  gen_tac >> strip_tac >> irule ghost_inv_scalar_local_clean >> metis_tac[]
QED

Theorem augassign_local_load_ptr:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ty /\ lookup_scopes name es.scopes = SOME entry /\
  word_value entry.value /\ emit_op MLOAD [Var p] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv sa s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx fn cenv cx (Name ty name) es sa sb s
      (es with gas_obs := []) entry.value (Var out) sf /\
    ghost_inv d cenv cx (es with gas_obs := []) Gf tnf sf /\
    ghost_kept cenv es sa G tn s Gf tnf /\ op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp sf = lookup_var rp s)
Proof
  strip_tac >> drule_all ghost_inv_word_local_inputs >> strip_tac >>
  drule_all emit_mload_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[IgnAsm `sf = _`] >>
  conj_tac >- (gvs[] >> irule name_word_post >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `sf = _` kall_tac >> simp[ghost_inv_gas_obs] >>
      irule ghost_inv_load_frame >>
      qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
      Cases_on `d` >> gvs[return_buf_frame_def, ret_pc_ok_def] >>
      PairCases_on `x` >> gvs[return_buf_frame_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem live_storage_head_clean:
  stor_taint_ok cx tn s /\
  (!st. storage_read_live cx tr st slot tv) /\ 0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >>
  `!st b. ~storage_dead cx tr st (w2n slot) b` by
    metis_tac[storage_read_live_head] >>
  Cases_on `tr` >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[stor_taint_ok_def, cx_dead_def, key_taint_def,
      pred_setTheory.SUBSET_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Theorem ptr_inst_ok_storage_load:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s
Proof
  strip_tac >> Cases_on `tr` >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
       op_taint_def, step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, eval_operand_def, update_var_def]
QED

Theorem storage_load_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) /\
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) u)
    (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s` by
    simp[ptr_inst_ok_storage_load] >>
  `~u.vs_halted` by
    (`step_inst 0 ctx (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s = OK u` by
       (Cases_on `tr` >> gvs[step_inst_non_invoke, mk_inst_def]) >>
     drule venomInstProofsTheory.step_preserves_halted >>
     Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  mp_tac (Q.INST [`lo` |-> `0`,
    `i` |-> `mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]`]
    straight_line_ptr_edge) >>
  Cases_on `tr` >> gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem storage_load_ghost_clean:
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  op_taint (step_taint
    (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s
    (update_var out v s) tn) (Var out) = {}
Proof
  Cases_on `tr` >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mk_inst_def, eval_operand_def, FLOOKUP_UPDATE]
QED

Theorem emit_storage_load_path_ptr:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = update_var out (if tr then tload slot s else sload slot s)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    lookup_var out sf = SOME (if tr then tload slot s else sload slot s) /\
    op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s =
     OK (update_var out (if tr then tload slot s else sload slot s) s)` by
    (Cases_on `tr` >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all storage_load_path_ptr >> strip_tac >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [out])
      (update_var out (if tr then tload slot s else sload slot s) s)`,
    `step_taint (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s
      (update_var out (if tr then tload slot s else sload slot s) s) tn`,
    `(update_var out (if tr then tload slot s else sload slot s) s)
      with vs_inst_idx := SUC s.vs_inst_idx`] >>
  `op_taint (step_taint
    (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s
    (update_var out (if tr then tload slot s else sload slot s) s) tn) (Var out) = {}` by
    simp[storage_load_ghost_clean] >>
  mp_tac (Q.INST [`opc` |-> `if tr then TLOAD else SLOAD`,
    `id` |-> `sa.cs_next_id`, `arg` |-> `Lit slot`,
    `v` |-> `if tr then tload slot s else sload slot s`] load_ambient_frame) >>
  impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[]) >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >> gvs[update_var_def]
QED

Theorem augassign_storage_load_ptr:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  is_word_type ty /\ storage_holds cx tr ty (Value v) slot es s /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  (!st. storage_read_live cx tr st slot tvt) /\ 0 < type_slot_size tvt /\
  ghost_inv d cenv cx es G tn s /\ ret_pc_ok cenv sa s /\
  return_buf_frame d cenv sa s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    eval_operand (Var out) sf = SOME (typed_val_to_w256 tvt v) /\
    stmt_state_rel ctx fn cenv cx es sf /\
    ghost_inv d cenv cx es Gf tnf sf /\
    ghost_kept cenv es sa G tn s Gf tnf /\ op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp sf = lookup_var rp s)
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[ghost_inv_def] >>
  drule_all live_storage_head_clean >> strip_tac >>
  drule_all emit_storage_load_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `sb.cs_next_var = sa.cs_next_var + 1 /\
   out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[IgnAsm `sf = _`] >>
  conj_tac
  >- (qpat_x_assum `sf = _` kall_tac >>
      drule_all storage_holds_load >> strip_tac >> gvs[eval_operand_def]) >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `sf = _` kall_tac >> irule ghost_inv_load_frame >>
      qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
      Cases_on `d` >> gvs[return_buf_frame_def, ret_pc_ok_def] >>
      PairCases_on `x` >> gvs[return_buf_frame_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED
