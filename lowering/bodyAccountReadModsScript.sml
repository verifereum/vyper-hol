(* Linked ordinary account access, including the active-frame CODESIZE path. *)
Theory bodyAccountReadMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyForRangeScalarFrameMods bodyFullShared gasContext gasExplicitSites
  bodyFullHashKeccakFixed[qualified]
  bodySimStmtFacts exprBodyPreProps exprSimAccounts exprSimUnopComposeProps
  gasShadowCompileStmtHelpers gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods vyperStorageTrace exprSimProps exprSimWordArgs
  bodyFullBuiltinEnvAccountStep stateRelProj accountsRelProps
  allocaHistory fragGasSeqPtr typedCopyOriginPtrBase decoderGhostFramePtr
  vyperTypeInvariants vyperTypeBuiltins exprSimOperands emitHelperProps
  vyperStorageFootprint vyperContext vyperTypeSystem vyperInterpreter
  vyperState vyperAST loweringPosts loweringStateRelDefs exprSimMemDefs
  exprSimHypsDefs bodyPtrDefs exprLoweringProps exprLowering compileEnv
  ptrDiscipline ptrSafeRun memSafeRun venomExecSemantics venomInst venomState
  contextCodegenRel codegenRel list finite_map words allocLimits
  supportedExprTraverse vyperExprEffects vyperTypeCallGraph
  emitHelper unitTransformDefs fragExec fragGasOriginPtr

Theorem account_source_inputs[local]:
  expr_body_pre_mods mods cenv cx env (Builtin a (Acc item) args) es ==>
  item <> Code /\ ?e. args = [e] /\ a = account_item_type item /\
    expr_type e = BaseT AddressT
Proof
  strip_tac >> conj_tac
  >- fs[expr_body_pre_mods_def, alloc_limits_expr_def] >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >> rename1 `h::t` >> Cases_on `t` >> simp[]
QED

Theorem account_operand_pre[local]:
  item <> Code /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Acc item) [e]) es ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       well_typed_builtin_app_def, byte_widths_expr_def, alloc_limits_expr_def,
       constSubstCorrectTheory.frame_well_typed_exprs_every,
       int_calls_expr_def, expr_has_evm_run_thm, supported_expr_exists_def]
QED

val account_code = ``\item x. case item of
    Balance => emit_op BALANCE [x]
  | Codesize => emit_op EXTCODESIZE [x]
  | Codehash => emit_op EXTCODEHASH [x]
  | IsContract => comp_bind (emit_op EXTCODESIZE [x]) (\c. emit_op GT [c; Lit 0w])
  | Address => comp_return x | Code => comp_return x``;

Theorem account_suffix_extends[local]:
  ^account_code item x sa = (op,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `item` >> simp[comp_return_def, cs_extends_refl, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt strip_tac >> drule emit_op_extends_next_var >>
  metis_tac[emit_op_extends_next_var, cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem account_read_emit[local]:
  MEM opc [BALANCE; EXTCODESIZE; EXTCODEHASH; GT; CODESIZE] /\
  (opc = GT ==> ?x. xs = [x;Lit 0w]) /\
  emit_op opc xs sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  EVERY (\x. op_taint tn x = {}) xs /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc xs [out]) s = OK (update_var out w s)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  alloca_inv s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t G' tn'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
    alloca_history func t /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    eval_operand op t = SOME w /\ op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H:(bool # bytes32 # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee t)
Proof
  strip_tac >>
  qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id opc xs [dst]` >>
  qabbrev_tac `u = update_var dst w s` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G inst u`, `step_taint inst s u tn`] >>
  `op = Var dst /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sa.cs_next_var <= sb.cs_next_var` by
    gvs[Abbr `dst`, emit_op_def, comp_bind_def,
        fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!p. not_fresh_at sa p ==> p <> dst` by simp[Abbr `dst`, not_fresh_at_def] >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!p. not_fresh_at sa p ==>
   lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var p s /\
   FLOOKUP (step_prov PG G inst u) p = FLOOKUP G p /\
   op_taint (step_taint inst s u tn) (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> `p <> dst` by metis_tac[] >>
     simp[Abbr `u`, Abbr `inst`, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  suspend "taint"
QED

Resume account_read_emit[taint]:
  `(step_taint inst s u tn).t_mem = tn.t_mem /\
   (step_taint inst s u tn).t_stor = tn.t_stor /\
   (step_taint inst s u tn).t_trans = tn.t_trans /\
   (step_taint inst s u tn).t_imm = tn.t_imm` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     gvs[Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
       new_site_bytes_def, range_bytes_def, written_taint_def,
       source_memory_write_ranges_def, adopt_reset_def, store_taint_def,
       imm_taint_def, Abbr `u`, update_var_def, mk_inst_def,
       pred_setTheory.EXTENSION, FLOOKUP_DEF] >>
     rpt (BasicProvers.TOP_CASE_TAC >> fs[]) >> metis_tac[]) >>
  `op_taint (step_taint inst s u tn) (Var dst) = {}` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, step_taint_def, op_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE, out_taint_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> fs[])) >>
  `op_prov (step_prov PG G inst u) (Var dst) = NONE` by
    (irule step_prov_out_none >>
     qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, mk_inst_def, out_prov_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >>
     simp[Abbr `inst`, Abbr `dst`] >> metis_tac[]) >>
  `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`] >>
  `alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule_all alloca_history_base_step >>
     qpat_x_assum `MEM opc _` mp_tac >>
     simp[Abbr `inst`, mk_inst_def] >> strip_tac >> gvs[is_terminator_def]) >>
  simp[] >>
  conj_tac >- simp[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  suspend "path"
QED

Resume account_read_emit[path]:
  `(u with <|vs_vars := s.vs_vars; vs_inst_idx := LENGTH sa.cs_current_insts|>) = s /\
   u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
   eval_operand (Var dst) u = SOME w` by
    simp[Abbr `u`, update_var_def, venom_state_component_equality,
         eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[] >> reverse conj_tac
  >- (simp[stmt_state_rel_inst_idx, Abbr `u`] >> rpt strip_tac >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[Abbr `dst`, not_fresh_at_def]) >>
  qx_gen_tac `D` >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `taint_ok func tn inst s` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[taint_ok_def, Abbr `inst`, mk_inst_def, source_memory_read_ranges_def] >>
     fs[EVERY_MEM, GSYM IMP_DISJ_THM] >> rpt strip_tac >> gvs[] >> metis_tac[op_taint_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ inst.inst_opcode <> DALLOCA` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def, step_inst_non_invoke] >>
     qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     fs[Abbr `inst`, mk_inst_def, access_ok_def, source_memory_read_ranges_def,
        source_memory_write_ranges_def, EVERY_MEM, Abbr `u`, update_var_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx), step_prov PG G inst u,
       step_taint inst s u tn)` by
    (`ctx_has_dalloca ctx ==> unitTransformDefs$dalloca_no_wrap inst s` by
       simp[dalloca_no_wrap_non_dalloca] >>
     drule_all straight_line_origin_ptr_edge >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Finalise account_read_emit

(* The selected execution can change registers and the instruction cursor,
   but none of the fields on which the linked frames depend. *)
Theorem account_read_frame[local]:
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  immutable_frame_mods func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  immutable_frame_mods func cenv cx (es with gas_obs := tail) t /\
  ghost_inv_at_mods D lo d cenv cx (es with gas_obs := tail) G' tn' t
Proof
  strip_tac >>
  qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`es`,`s`,`sa`] >> simp[]) >>
  irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >> simp[]
QED

Theorem self_codesize_value_mods[local]:
  is_self_addr e ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (account_item_type Codesize) (Acc Codesize) [e]) es
Proof
  strip_tac >> simp[account_item_type_def] >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >>
      simp[self_codesize_source_bind_all_tails]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `s0.vs_code = cx.txn.code` by
    (drule stmt_state_rel_state_rel >> simp[state_rel_def, accounts_rel_def]) >>
  `emit_op CODESIZE [] sa = (op,sb)` by
    (drule lower_value_self_codesize >>
     disch_then (qspecl_then [`cenv`,`ty`,`BaseT (UintT 256)`,`sa`] assume_tac) >>
     fs[]) >>
  `allocas_from lo s0` by fs[ghost_inv_at_mods_def] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id CODESIZE [] [out]) s0 =
       OK (update_var out (n2w (LENGTH cx.txn.code)) s0)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  suspend "path"
QED

Resume self_codesize_value_mods[path]:
  mp_tac (Q.INST [`opc` |-> `CODESIZE`, `xs` |-> `[]:operand list`,
    `s` |-> `s0`, `w` |-> `n2w (LENGTH cx.txn.code)`, `ee` |-> `es`,
    `G` |-> `G0`, `tn` |-> `tn0`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    account_read_emit) >>
  simp[] >> strip_tac >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`es`,`INL (IntV (&LENGTH cx.txn.code))`,`t`,`tn'`] >>
  simp[self_codesize_source_bind_all_tails] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `immutable_frame_mods func cenv cx (es with gas_obs := []) t /\
   ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G' tn' t` by
    (irule account_read_frame >>
     qexistsl_tac [`G0`,`s0`,`sa`,`tn0`] >> simp[]) >>
  qpat_assum `!h. stmt_state_rel h _ _ _ _ _ _ ==> stmt_state_rel h _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
      storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
     irule storage_well_formed_on_backends >> simp[]) >>
  `t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas /\
   t.vs_alloca_next = s0.vs_alloca_next` by
    fs[venom_state_component_equality] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (strip_tac >> `allocas_below_fmp s0` by metis_tac[] >>
     fs[venom_state_component_equality, allocas_below_fmp_def] >>
     first_assum ACCEPT_TAC) >>
  simp[expr_type_def, is_word_type_def, expr_store_bound_word, ptr_val_ok_def,
       ghost_kept_at_def] >>
  simp[expr_post_mods_def, expr_post_def, expr_type_def, is_word_type_def,
       expr_val_rel_def, expr_val_at_def, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
       integer_wordTheory.i2w_def, stmt_state_rel_start_gas_obs, locals_kept_def,
       pure_frame_def, popped_kept_def, vyperEvalScopesProgressTheory.scopes_progress_refl]
QED

Finalise self_codesize_value_mods

(* One-read suffixes: the opcode reads the same account fields as the
   source, independent of any storage differences permitted by the horizon. *)
Theorem account_single_read[local]:
  MEM item [Balance; Codesize; Codehash] /\
  LENGTH bs = 20 /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  (let src = lookup_account (word_of_bytes_be bs) (ee:evaluation_state).accounts;
       dst = lookup_account (word_of_bytes_be bs) s.vs_accounts in
    dst.balance = src.balance /\ dst.code = src.code /\ dst.nonce = src.nonce) ==>
  ?opc w. MEM opc [BALANCE; EXTCODESIZE; EXTCODEHASH] /\
    ^account_code item x = emit_op opc [x] /\
    (!out. step_inst_base (mk_inst sa.cs_next_id opc [x] [out]) s =
      OK (update_var out w s)) /\
    (!tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
      w = typed_val_to_w256 tv
        (evaluate_account_op item bs (lookup_account (word_of_bytes_be bs) ee.accounts)))
Proof
  simp[AND_IMP_INTRO] >> strip_tac >>
  `w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) =
      (word_of_bytes_be bs : address)` by simp[address_word_w2w]
  >- (qexistsl_tac [`BALANCE`,
      `n2w (lookup_account (word_of_bytes_be bs) ee.accounts).balance`] >>
      simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def] >>
      simp[evaluate_account_op_def, account_item_type_def, vyperValueTheory.evaluate_type_def,
        valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
        integer_wordTheory.i2w_def])
  >- (qexistsl_tac [`EXTCODESIZE`,
      `n2w (LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code)`] >>
      simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def] >>
      simp[evaluate_account_op_def, account_item_type_def, vyperValueTheory.evaluate_type_def,
        valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
        integer_wordTheory.i2w_def]) >>
  qexistsl_tac [`EXTCODEHASH`,
    `if vfmState$account_empty (lookup_account (word_of_bytes_be bs) ee.accounts)
     then 0w else word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (lookup_account (word_of_bytes_be bs) ee.accounts).code)`] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
       vfmStateTheory.account_empty_def] >>
  simp[evaluate_account_op_def, account_item_type_def,
    vyperValueTheory.evaluate_type_def, valueEncodingTheory.typed_val_to_w256_def,
    valueEncodingTheory.val_to_w256_def] >>
  simp[vfmStateTheory.account_empty_def] >> IF_CASES_TAC >>
  simp[PAD_RIGHT, vyperTypeBytesCryptoTheory.LENGTH_Keccak_256_w64] >>
  simp[byteTheory.word_of_bytes_be_def, valueEncodingProofsTheory.word_of_bytes_replicate_zero]
QED

Theorem account_suffix_read[local]:
  item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed ee.accounts /\
  ^account_code item x sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn x = {} /\ op_prov G x = NONE /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  alloca_inv s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (let src = lookup_account (word_of_bytes_be bs) (ee:evaluation_state).accounts;
       dst = lookup_account (word_of_bytes_be bs) s.vs_accounts in
    dst.balance = src.balance /\ dst.code = src.code /\ dst.nonce = src.nonce) ==>
  ?t G' tn'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
      eval_operand op t = SOME (typed_val_to_w256 tv
        (evaluate_account_op item bs (lookup_account (word_of_bytes_be bs) ee.accounts)))) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H:(bool # bytes32 # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee t)
Proof
  strip_tac >> Cases_on `item = Address`
  >- (gvs[comp_return_def, account_item_type_def, evaluate_account_op_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[venom_state_component_equality, gas_origin_ptr_path_rules,
           vyperValueTheory.evaluate_type_def]) >>
  Cases_on `item = IsContract`
  >- suspend "iscontract" >>
  `MEM item [Balance; Codesize; Codehash]` by (Cases_on `item` >> gvs[]) >>
  mp_tac account_single_read >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `emit_op opc [x] sa = (op,sb)` by metis_tac[] >>
  `MEM opc [BALANCE; EXTCODESIZE; EXTCODEHASH; GT; CODESIZE] /\ opc <> GT` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >> simp[]) >>
  mp_tac (Q.INST [`xs` |-> `[x]`] account_read_emit) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> simp[]
QED

Resume account_suffix_read[iscontract]:
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op EXTCODESIZE [x] sa = (len,sm)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (drule emit_op_extends_next_var >> simp[]) >>
  `cs_extends sm sb` by
    (qpat_assum `emit_op GT _ _ = _` (mp_tac o MATCH_MP emit_op_extends_next_var) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  qabbrev_tac `w = n2w (LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code) : bytes32` >>
  `!out. step_inst_base (mk_inst sa.cs_next_id EXTCODESIZE [x] [out]) s =
     OK (update_var out w s)` by
    simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def, address_word_w2w, Abbr `w`] >>
  mp_tac (Q.INST [`opc` |-> `EXTCODESIZE`, `xs` |-> `[x]`,
                  `op` |-> `len`, `sb` |-> `sm`] account_read_emit) >>
  simp[] >> strip_tac >>
  `!out. step_inst_base (mk_inst sm.cs_next_id GT [len; Lit 0w] [out]) t =
     OK (update_var out (bool_to_word (w2n w > 0)) t)` by
    simp[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def, eval_operand_def,
         WORD_GREATER, word_lo_def] >>
  `alloca_inv t /\ allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
     fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def,
        venomMemDefsTheory.alloca_next_valid_def, allocas_from_def, allocas_below_fmp_def] >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC >>
     strip_tac >> qpat_x_assum `ctx_has_dalloca ctx ==> _` mp_tac >> simp[] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`opc` |-> `GT`, `xs` |-> `[len; Lit 0w]`, `sa` |-> `sm`,
    `s` |-> `t`, `G` |-> `G'`, `tn` |-> `tn'`, `w` |-> `bool_to_word (w2n w > 0)`]
    account_read_emit) >>
  simp[Once op_taint_def] >> strip_tac >>
  qexistsl_tac [`t'`,`G''`,`tn''`] >> simp[] >>
  suspend "iscontract_post"
QED

Resume account_suffix_read[iscontract_post]:
  conj_tac
  >- (qpat_x_assum `t' with <|vs_vars := _; vs_inst_idx := _|> = t` mp_tac >>
      qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
      simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> `not_fresh_at sm p` by
        metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      qpat_assum `!p. not_fresh_at sm p ==> _` drule >>
      qpat_assum `!p. not_fresh_at sa p ==> _` drule >> simp[]) >>
  conj_tac
  >- (simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
           evaluate_account_op_def, valueEncodingTheory.typed_val_to_w256_def,
           valueEncodingTheory.val_to_w256_def] >>
      `LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code < dimword (:256)` by
        (qpat_x_assum `accounts_well_typed _` mp_tac >>
         simp[vyperTypeInvariantsTheory.accounts_well_typed_def,
              vyperTypeInvariantsTheory.account_well_typed_def, wordsTheory.dimword_def] >>
         disch_then (qspec_then `word_of_bytes_be bs` strip_assume_tac) >> decide_tac) >>
      simp[Abbr `w`, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, bool_to_word_def] >>
      Cases_on `(lookup_account (word_of_bytes_be bs) ee.accounts).code` >> simp[]) >>
  gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`t`,`G'`,`tn'`,`[]`] mp_tac) >> simp[]
QED

Finalise account_suffix_read

Theorem account_child_value[local]:
  body_exprs_full_ok_mods mods exps cx [e] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem account_paired_prefix[local]:
  item <> Code /\ ~is_self_codesize (Acc item) [e] /\
  lower_value compile_expr cenv ty (Builtin ann (Acc item) [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Acc item) [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x sm shsm.
    lower_value compile_expr cenv (BaseT AddressT) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
      (gas_shadow_expr e) shadow_sa = (x,shsm) /\
    ^account_code item x sm = (op,sb) /\
    gas_shadow_state sm shsm /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shsm shadow_func /\ sa.cs_next_var <= sm.cs_next_var
Proof
  strip_tac >> drule_all_then strip_assume_tac lower_value_acc >>
  rename1 `lower_value compile_expr cenv (BaseT AddressT) e sa = (x,sm)` >>
  `~is_self_codesize (Acc item) [gas_shadow_expr e]` by
    fs[is_self_codesize_def, gasShadowCompileHelpersTheory.gas_shadow_self_addr] >>
  `?sx shsm. lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
      (gas_shadow_expr e) shadow_sa = (sx,shsm) /\
      ^account_code item sx shsm = (op,shadow_sb)` by
    (BETA_TAC >> irule lower_value_acc >> simp[] >>
     qexistsl_tac [`ann`,`ty`] >> gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def]) >>
  `sx = x /\ gas_shadow_state sm shsm` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qexistsl_tac [`x`,`sm`,`shsm`] >> simp[] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`cenv`,`BaseT AddressT`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `cs_extends shadow_sa shsm` by
    (qspecl_then [`gas_shadow_env T cenv`,`BaseT AddressT`,`gas_shadow_expr e`,`shadow_sa`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `cs_extends sm sb` by
    (mp_tac (Q.INST [`sa` |-> `sm`] account_suffix_extends) >> simp[]) >>
  `cs_extends shsm shadow_sb` by
    (mp_tac (Q.INST [`sa` |-> `shsm`, `sb` |-> `shadow_sb`] account_suffix_extends) >> fs[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shsm shadow_func /\ fn_has_code shsm shadow_sb shadow_func` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

val account_tail = ``\v ee. (unop_result cx (account_item_type item) (Acc item)
    [BaseT AddressT] v ee,ee)``;

Theorem account_bind_tail[local]:
  expr_type e = BaseT AddressT /\ ~is_self_codesize (Acc item) [e] /\
  (!H res ee gt r. R H res ee gt r ==> ?exc. res = INR exc) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Qchild R /\
  (!marks res mid G tn t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res,mid with gas_obs := tail)) /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Qchild H res mid G tn t /\ mid.gas_obs = [] /\ ~t.vs_halted) ==>
    ?v. res = INL v /\
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
        (^account_tail v) (mid,t,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e])) (read_result cx))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx)) ^account_tail` by
    (dep_rewrite.DEP_REWRITE_TAC[eval_expr_unop_action_general] >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  pop_assum SUBST1_TAC >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >- simp[storage_trace_frame_def,exprSimUnopPropsTheory.unop_result_def] >>
  qexists_tac `\H res ee G tn t. Qchild H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  BETA_TAC >> conj_tac
  >- (rpt strip_tac >> disj1_tac >>
      qpat_assum `!marks res mid G tn t. _` (irule o BETA_RULE) >>
      conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem account_pre_gas_obs[local]:
  expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods cenv cx env e es
Proof
  simp[expr_body_pre_mods_def,expr_sim_inv_mods_def]
QED

Theorem account_ghost_kept[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)) /\ tn'.t_mem = tn.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  rewrite_tac[ghost_kept_at_def] >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Theorem account_value_mods[local]:
  item <> Code /\ expr_type e = BaseT AddressT /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT AddressT) e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  strip_tac >> Cases_on `is_self_codesize (Acc item) [e]`
  >- (Cases_on `item` >> gvs[is_self_codesize_def] >> simp[self_codesize_value_mods]) >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac account_paired_prefix >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`account_item_type item`,`Acc item`] >>
     simp[builtin_args_length_ok_def,precompile_builtin_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shsm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule account_bind_tail >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  suspend "continuation"
QED

Resume account_value_mods[continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qexists_tac `v` >> simp[] >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
    (qspec_then `[]` (mp_tac o SIMP_RULE (srw_ss()) [])) >>
  asm_rewrite_tac[] >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[account_pre_gas_obs] >>
  `expr_sim_inv_mods mods cenv cx env mid /\ value_runtime_typed env (expr_type e) v` by
    (qpat_assum `bind (eval_expr cx e) _ _ = (INL v,mid)`
       (mp_then Any mp_tac (SIMP_RULE (srw_ss()) [SF ETA_ss] expr_body_pre_eval_mods)) >>
     disch_then (qspecl_then [`mods`,`env`,`cenv`] mp_tac) >> simp[]) >>
  `?bs. v = BytesV bs /\ LENGTH bs = 20` by
    (qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperValueTheory.evaluate_type_def] >> Cases_on `v` >>
     simp[vyperTypingTheory.value_has_type_def]) >>
  rename1 `LENGTH bs = 20` >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `accounts_well_typed mid.accounts` by fs[expr_sim_inv_mods_def] >>
  `post_value_type cenv e = BaseT AddressT` by simp[is_word_type_def] >>
  `op_taint tn x = {} /\ op_prov G x = NONE` by fs[ptr_val_ok_def,is_word_type_def] >>
  qhdtm_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))` by
    (qhdtm_x_assum `expr_val_rel` mp_tac >>
     simp[expr_val_rel_def,is_word_type_def,vyperValueTheory.evaluate_type_def]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `let src = lookup_account (word_of_bytes_be bs) mid.accounts;
       dst = lookup_account (word_of_bytes_be bs) s.vs_accounts in
     dst.balance = src.balance /\ dst.code = src.code /\ dst.nonce = src.nonce` by
    (drule stmt_state_rel_state_rel >> simp[state_rel_def,accounts_rel_def] >>
     strip_tac >> drule accounts_agree_lookup >> simp[]) >>
  drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`cx`,`PG`] strip_assume_tac)
    account_suffix_read >>
  rename1 `t.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  rename1 `op_prov G' op = NONE` >> rename1 `op_taint tn' op = {}` >>
  qabbrev_tac `out = evaluate_account_op item bs (lookup_account (word_of_bytes_be bs) mid.accounts)` >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL out`,`t`,`tn'`] >>
  simp[exprSimUnopPropsTheory.unop_result_def,evaluate_builtin_def,Abbr `out`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H)` by
    fs[expr_post_mods_def,expr_post_def] >>
  `stmt_state_rel H ctx func cenv cx mid t` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ ==> _` irule >> simp[]) >>
  `immutable_frame_mods func cenv cx mid t /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' t` by
    (`immutable_frame_mods func cenv cx (mid with gas_obs := []) t /\
      ghost_inv_at_mods (DF H) lo d cenv cx (mid with gas_obs := []) G' tn' t` suffices_by simp[] >>
     irule account_read_frame >> qexistsl_tac [`G`,`s`,`sm`,`tn`] >> simp[]) >>
  `is_word_type (account_item_type item)` by
    (Cases_on `item` >> gvs[account_item_type_def,is_word_type_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ t`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by fs[venom_state_component_equality] >>
  `!p. not_fresh_at sa p ==>
     lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at sm p` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!p. not_fresh_at sm p ==> _` (drule_then ACCEPT_TAC)) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule account_ghost_kept >> qexistsl_tac [`G`,`tn`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!p. not_fresh_at sa p ==> lookup_var p t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  simp[expr_type_def,expr_store_bound_word,ptr_val_ok_def] >>
  simp[expr_post_mods_def,expr_post_def,expr_type_def,expr_val_rel_def,expr_val_at_def] >>
  conj_tac
  >- (`?tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv` by
        (Cases_on `item` >> gvs[account_item_type_def,vyperValueTheory.evaluate_type_def,wordsTheory.dimword_def]) >>
      qpat_assum `!tv. evaluate_type _ _ = SOME tv ==> _` (drule_then assume_tac) >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  disch_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >> simp[]
QED

Finalise account_value_mods

Theorem account_read_sim_mods:
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) ==>
  !exps src tops DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty a item args es.
    (builtin_args_length_ok (Acc item) (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a (Acc item) args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin a (Acc item) args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin a (Acc item) args) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac account_source_inputs >> gvs[builtin_args_length_ok_def] >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule account_operand_pre >> qexistsl_tac [`account_item_type item`,`item`] >> simp[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT AddressT) e es` by
    (irule account_child_value >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  conj_asm1_tac
  >- (irule account_value_mods >> simp[] >> qexistsl_tac [`env`,`mods`] >> simp[]) >>
  first_assum irule >> simp[expr_type_def,compile_acc_stack] >>
  conj_tac >- (rpt strip_tac >> drule eval_expr_builtin_value >> simp[]) >>
  Cases_on `item` >> gvs[account_item_type_def,is_word_type_def]
QED
