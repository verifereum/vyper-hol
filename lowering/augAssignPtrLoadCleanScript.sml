(* Same-witness load packaging.  This does not strengthen the RHS judgment. *)
Theory augAssignPtrLoadClean
Ancestors
  wordLoadStorePtr augAssignPtrScalarWitnessProbe augAssignPtrLoad augAssignPtrProvenanceProbe
  emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs stmtFragPtr
  exprSimNameWord bodyPtrDefs ptrDiscipline venomInst venomState finite_map
  loweringSlice venomExecSemantics fragExec typedCopyPtr codegenRel
  augAssignPtrInterfaces loweringPosts exprSimUnwrap

Theorem augassign_local_load_clean_ptr:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ty /\ lookup_scopes name es.scopes = SOME entry /\
  word_value entry.value /\ emit_op MLOAD [Var p] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    expr_post ctx fn cenv cx (Name ty name) es sa sb s
      (es with gas_obs := []) entry.value (Var out) t /\
    ghost_inv d cenv cx (es with gas_obs := []) H tm t /\
    ghost_kept cenv es sa G tn s H tm /\ op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s) /\
    op_prov H (Var out) = NONE
Proof
  strip_tac >> drule_all ghost_inv_word_local_inputs >> strip_tac >>
  `!rp. not_fresh_at sa rp ==> rp <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all emit_mload_explicit_ghost_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)` >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `id` |-> `sa.cs_next_id`,
    `arg` |-> `Var p`, `v` |-> `mload (w2n (a:256 word)) s`] load_ambient_frame) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `!rp. not_fresh_at sa rp ==>
     lookup_var rp t = lookup_var rp s /\ FLOOKUP H rp = FLOOKUP G rp /\
     op_taint tm (Var rp) = op_taint tn (Var rp)` by
    (simp[Abbr `H`, Abbr `tm`, Abbr `t`] >> rpt strip_tac >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[] >>
  conj_tac >- (simp[Abbr `t`] >> irule name_word_post >> simp[] >> metis_tac[]) >>
  conj_tac >- (simp[ghost_inv_gas_obs] >> irule ghost_inv_load_frame >>
    qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
    simp[Abbr `H`, Abbr `tm`, Abbr `t`, update_var_def, load_ambient_frame] >>
    gvs[ret_pc_ok_def]) >>
  conj_tac >- (simp[ghost_kept_def, Abbr `tm`, load_ambient_frame] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `mload _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
    simp[Abbr `tm`, NoAsms] >>
    irule (cj 1 wordLoadStorePtrTheory.mload_ghost_clean) >> simp[eval_operand_def]) >>
  simp[Abbr `t`, update_var_def, Abbr `H`, load_result_has_no_provenance] >>
  `sb.cs_next_var = sa.cs_next_var + 1 /\
   out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  conj_tac >- (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem emit_storage_load_clean_path_ptr:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
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
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1] >>
  Cases_on `tr` >> simp[load_result_has_no_provenance]
QED

Theorem augassign_storage_load_clean_ptr:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
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
    ghost_kept cenv es sa G tn s H tm /\ op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s) /\
    op_prov H (Var out) = NONE
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[ghost_inv_def] >>
  drule_all live_storage_head_clean >> strip_tac >>
  drule_all emit_storage_load_clean_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `sb.cs_next_var = sa.cs_next_var + 1 /\
   out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[IgnAsm `t = _`] >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >>
      drule_all storage_holds_load >> strip_tac >> gvs[eval_operand_def]) >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >> irule ghost_inv_load_frame >>
      qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
      gvs[ret_pc_ok_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED
