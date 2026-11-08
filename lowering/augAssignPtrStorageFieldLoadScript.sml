(* Counted field-slot prefix.  Its saved address is an unprovenanced word. *)
Theory augAssignPtrStorageFieldLoad
Ancestors
  augAssignPtrStorageAddress augAssignPtrLoadClean augAssignPtrLoad
  augAssignPtrProvenanceProbe augAssignPtrScalarWitnessProbe
  emitHelper emitHelperProps exprLoweringProps compileEnv stmtFragPtr
  bodyPtrDefs ptrDiscipline venomInst venomState finite_map
  loweringSlice venomExecSemantics fragExec codegenRel
  accountsRelProps loweringPosts exprSimUnwrap typedCopyPtr stmtSimProps freshWrites
  fragGasPathPtr

Theorem emit_storage_address_load_clean_path_ptr:
  emit_op (if tr then TLOAD else SLOAD) [addr] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME slot /\ op_prov G addr = NONE /\
  op_taint tn addr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t = update_var out (if tr then tload slot s else sload slot s)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    lookup_var out t = SOME (if tr then tload slot s else sload slot s) /\
    op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p)) /\
    op_prov H (Var out) = NONE
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [addr] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [addr] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all storage_address_load_path_ptr >> strip_tac >>
  qexistsl [
    `step_prov PG G (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [addr] [out])
      (update_var out (if tr then tload slot s else sload slot s) s)`,
    `step_taint (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [addr] [out]) s
      (update_var out (if tr then tload slot s else sload slot s) s) tn`,
    `(update_var out (if tr then tload slot s else sload slot s) s)
      with vs_inst_idx := SUC s.vs_inst_idx`] >>
  `op_taint (step_taint
    (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [addr] [out]) s
    (update_var out (if tr then tload slot s else sload slot s) s) tn) (Var out) = {}` by
    (irule storage_address_load_ghost_clean_ptr >> metis_tac[]) >>
  mp_tac (Q.INST [`opc` |-> `if tr then TLOAD else SLOAD`,
    `id` |-> `sa.cs_next_id`, `arg` |-> `addr`,
    `v` |-> `if tr then tload slot s else sload slot s`] load_ambient_frame) >>
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1] >>
  Cases_on `tr` >> simp[load_result_has_no_provenance]
QED

Theorem augassign_storage_address_load_clean_ptr:
  emit_op (if tr then TLOAD else SLOAD) [addr] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME slot /\ op_prov G addr = NONE /\
  op_taint tn addr = {} /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  is_word_type ty /\ storage_holds cx tr ty (Value v) slot es s /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  (!st. storage_read_live cx tr st slot tvt) /\ 0 < type_slot_size tvt /\
  ghost_inv d cenv cx es G tn s /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    eval_operand (Var out) t = SOME (typed_val_to_w256 tvt v) /\
    stmt_state_rel ctx fn cenv cx es t /\
    ghost_inv d cenv cx es H tm t /\
    ghost_kept cenv es sa G tn s H tm /\ tm.t_mem = tn.t_mem /\
    op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s) /\
    op_prov H (Var out) = NONE
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[ghost_inv_def] >>
  drule_all live_storage_head_clean >> strip_tac >>
  drule_all emit_storage_address_load_clean_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sb.cs_next_var = sa.cs_next_var + 1 /\
   out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  qexistsl [`H`, `tm`, `t`] >> simp[IgnAsm `t = _`] >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >>
      drule_all storage_holds_load >> strip_tac >> gvs[eval_operand_def]) >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >> irule ghost_inv_load_frame >>
      qexistsl [`G`, `s`, `sa`, `tn`] >> simp[] >>
      gvs[ret_pc_ok_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem literal_slot_add_imm_frame_ptr:
  (step_taint (mk_inst id ADD [Lit a; Lit b] [out]) s
    (update_var out v s) tn).t_imm = tn.t_imm
Proof
  `new_site_bytes s (update_var out v s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, imm_taint_def, adopt_reset_def, set_var_taint_def,
       mk_inst_def]
QED

Theorem emit_literal_slot_add_path_ptr:
  emit_op ADD [Lit a; Lit b] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t = update_var out (a + b)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    lookup_var out t = SOME (a + b) /\
    op_prov H (Var out) = NONE /\ op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Lit a; Lit b] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ADD [Lit a; Lit b] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all literal_slot_add_path_ptr >> strip_tac >>
  qexistsl [
    `step_prov PG G (mk_inst sa.cs_next_id ADD [Lit a; Lit b] [out])
      (update_var out (a + b) s)`,
    `step_taint (mk_inst sa.cs_next_id ADD [Lit a; Lit b] [out]) s
      (update_var out (a + b) s) tn`,
    `(update_var out (a + b) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[literal_slot_add_imm_frame_ptr, copy_len_binop_ghost_frame,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1] >>
  irule step_prov_out_none >> simp[out_prov_arith_none, op_prov_lit, mk_inst_def]
QED

Theorem augassign_storage_slot_add_clean_ptr:
  emit_op ADD [Lit a; Lit b] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    eval_operand (Var out) t = SOME (a + b) /\
    stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es H tm t /\
    ghost_kept cenv es sa G tn s H tm /\ tm.t_mem = tn.t_mem /\
    op_prov H (Var out) = NONE /\ op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s)
Proof
  strip_tac >> drule_all emit_literal_slot_add_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `sb.cs_next_var = sa.cs_next_var + 1 /\
   out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  qexistsl [`H`, `tm`, `t`] >> simp[IgnAsm `t = _`, eval_operand_def] >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >> irule ghost_inv_load_frame >>
      qexistsl [`G`, `s`, `sa`, `tn`] >> simp[] >> gvs[ret_pc_ok_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem augassign_storage_field_load_clean_ptr:
  emit_op ADD [Lit root_slot; Lit off] sa = (Var dst,sm) /\
  emit_op (if tr then TLOAD else SLOAD) [Var dst] sm = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  is_word_type ty /\ storage_holds cx tr ty (Value v) (root_slot + off) es s /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  (!st. storage_read_live cx tr st (root_slot + off) tvt) /\ 0 < type_slot_size tvt /\
  ghost_inv d cenv cx es G tn s /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    eval_operand (Var dst) t = SOME (root_slot + off) /\
    op_prov H (Var dst) = NONE /\ op_taint tm (Var dst) = {} /\
    eval_operand (Var out) t = SOME (typed_val_to_w256 tvt v) /\
    stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es H tm t /\
    ghost_kept cenv es sa G tn s H tm /\ tm.t_mem = tn.t_mem /\
    op_prov H (Var out) = NONE /\ op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb dst /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s)
Proof
  strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all augassign_storage_slot_add_clean_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ret_pc_ok cenv sm t` by
    (irule ret_pc_ok_frame >> qexistsl [`cenv`, `s`, `sa`] >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `storage_holds cx tr ty (Value v) (root_slot + off) es t` by
    (gvs[storage_holds_def, contract_storage_def, contract_transient_def]) >>
  drule_all augassign_storage_address_load_clean_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!rp. not_fresh_at sa rp ==> not_fresh_at sm rp` by
    metis_tac[not_fresh_at_mono] >>
  `op_prov H' (Var dst) = NONE /\ op_taint tm' (Var dst) = {}` by
    fs[ghost_kept_def, op_prov_def] >>
  `ghost_kept cenv es sa G tn s H' tm'` by
    (fs[ghost_kept_def] >> metis_tac[]) >>
  qexistsl [`H'`, `tm'`, `t'`] >> simp[] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- gvs[eval_operand_def] >>
  metis_tac[not_fresh_at_mono]
QED
