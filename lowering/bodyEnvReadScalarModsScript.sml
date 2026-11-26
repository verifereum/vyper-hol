(* Read-only, zero-operand scalar builtins. Both source and machine read the
   same transaction context; the machine additionally writes a fresh word. *)
Theory bodyEnvReadScalarMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyForRangeScalarFrameMods gasOutcomeFullPostMods
  gasStorage gasContext gasExplicitSites
  exprBodyPreProps exprSimWordArgs exprSimCalldata exprSimProps exprSimOperands
  typedCopyOriginPtrBase emitHelperProps allocasBelowFmpUpdatesProps
  exprLoweringProps stateRelProj allocaHistory exprSimMemDefs
  vyperTypeBuiltins vyperTypeSystem vyperContext vyperInterpreter
  vyperState vyperAST vyperValue valueEncoding loweringPosts
  codegenRel contextCodegenRel unitTransformDefs instMemFrontier
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  compileEnv emitHelper bodyPtrDefs fragGasOriginPtr vyperStorageFootprint words
  exprLowering loweringStateRelDefs valueEncodingProofs memSafeRun

Theorem env_scalar_source[local]:
  i <> PrevHash /\ i <> MsgGas ==>
  ?v. evaluate_builtin cx es.accounts (env_item_type i) (Env i) [] [] = INL v /\
      (!tail. bind (eval_expr cx (Builtin (env_item_type i) (Env i) []))
        (read_result cx) (es with gas_obs := tail) = (INL v,es with gas_obs := tail)) /\
      is_word_type (env_item_type i) /\
      (!tv. evaluate_type (get_tenv cx) (env_item_type i) = SOME tv ==>
          typed_val_to_w256 tv v = val_to_w256 v)
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def, is_self_codesize_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `i` >>
  gvs[evaluate_builtin_def, env_item_type_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
      return_def, read_result_def] >>
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []
QED

(* These opcodes share a read-only, zero-input execution protocol. *)
val read_opcodes = ``[CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER;
  BLOBBASEFEE; GASPRICE; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
  ORIGIN; CALLDATASIZE]``;

Theorem env_scalar_emission[local]:
  i <> PrevHash /\ i <> MsgGas /\
  lower_value compile_expr cenv ty (Builtin (env_item_type i) (Env i) []) sa = (op,sb) /\
  evaluate_builtin cx accts (env_item_type i) (Env i) [] [] = INL v ==>
  ?opc. MEM opc ^read_opcodes /\ emit_op opc [] sa = (op,sb) /\
    !s id out. call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx ==>
      step_inst_base (mk_inst id opc [] [out]) s = OK (update_var out (val_to_w256 v) s)
Proof
  strip_tac >> drule lower_value_env >> strip_tac >>
  Cases_on `i` >> gvs[compile_env_var_def, evaluate_builtin_def] >>
  (qmatch_asmsub_abbrev_tac `emit_op opc [] sa` >>
   qexists_tac `opc` >> simp[] >>
   rw[Abbr `opc`, step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def, call_ctx_rel_def] >>
   simp[val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def])
QED

Theorem calldatalen_scalar_emission[local]:
  lower_value compile_expr cenv ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) ==>
  ?opc. MEM opc ^read_opcodes /\ emit_op opc [] sa = (op,sb) /\
    !s id out. call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx ==>
      step_inst_base (mk_inst id opc [] [out]) s =
        OK (update_var out (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s)
Proof
  simp[lower_value_calldata_len] >> strip_tac >>
  qexists_tac `CALLDATASIZE` >> simp[] >>
  rw[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def, call_ctx_rel_def] >>
  simp[val_to_w256_def, integer_wordTheory.i2w_def]
QED

Theorem scalar_read_opcode_checks[local]:
  MEM opc ^read_opcodes /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  step_inst_base (mk_inst id opc [] [out]) s = OK (update_var out w s) ==>
  opc <> INVOKE /\ opc <> GAS /\ opc <> DALLOCA /\ ~is_terminator opc /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst id opc [] [out]) s /\
  inst_mem_below_frontier (mk_inst id opc [] [out]) s /\
  inst_dload_in_section (mk_inst id opc [] [out]) s
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def, is_terminator_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[update_var_def]
QED

Theorem scalar_read_ghost_update[local]:
  MEM opc ^read_opcodes /\ ~not_fresh_at sa out /\
  t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
  G' = step_prov PG G (mk_inst sa.cs_next_id opc [] [out]) (update_var out w s) /\
  tn' = step_taint (mk_inst sa.cs_next_id opc [] [out]) s (update_var out w s) tn ==>
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> out` by metis_tac[] >>
  `G' = DRESTRICT G (COMPL {out})` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def]) >>
  `tn' = tn with t_var := tn.t_var |+ (out,{})` by
    (qabbrev_tac `u = update_var out w s` >>
     qabbrev_tac `ins = mk_inst sa.cs_next_id opc [] [out]` >>
     `source_memory_write_ranges ins s = [] /\ step_writes ins s u = [] /\
      ~MEM ins.inst_opcode [CALL; DELEGATECALL; CREATE; CREATE2] /\
      ins.inst_opcode <> ISTORE /\ ins.inst_opcode <> SSTORE /\ ins.inst_opcode <> TSTORE` by
       (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
        simp[Abbr `ins`, step_writes_def, source_memory_write_ranges_def, mk_inst_def]) >>
     `new_site_bytes s u = {}` by
       (simp[Abbr `u`, new_site_bytes_def, update_var_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
        rpt gen_tac >> Cases_on `aid IN FDOM s.vs_allocas` >> simp[]) >>
     `ins.inst_operands = [] /\ ins.inst_outputs = [out]` by simp[Abbr `ins`, mk_inst_def] >>
     `mem_taint tn ins s u = tn.t_mem` by
       simp[mem_taint_def, written_taint_def, range_bytes_def, pred_setTheory.EXTENSION] >>
     `tn' = step_taint ins s u tn` by simp[Abbr `ins`] >>
     qpat_x_assum `tn' = step_taint ins _ _ _` SUBST1_TAC >>
     simp[step_taint_def, store_taint_def, adopt_reset_def,
          imm_taint_def, out_taint_def, set_var_taint_def, taint_component_equality]) >>
  simp[op_prov_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  gen_tac >> strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem scalar_read_path[local]:
  MEM opc ^read_opcodes /\ emit_op opc [] sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc [] [out]) s = OK (update_var out w s)) ==>
  ?out t G' tn'. out = STRING #"%" (toString sa.cs_next_var) /\ op = Var out /\
    t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id opc [] [out]) (update_var out w s) /\
    tn' = step_taint (mk_inst sa.cs_next_id opc [] [out]) s (update_var out w s) tn /\
    eval_operand op t = SOME w /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `!D out. opc <> INVOKE /\ opc <> GAS /\ opc <> DALLOCA /\ ~is_terminator opc /\
     ptr_inst_ok D lo 0 ctx func G tn (mk_inst sa.cs_next_id opc [] [out]) s /\
     inst_mem_below_frontier (mk_inst sa.cs_next_id opc [] [out]) s /\
     inst_dload_in_section (mk_inst sa.cs_next_id opc [] [out]) s` by
    (rpt gen_tac >> irule scalar_read_opcode_checks >> simp[] >>
     qexists_tac `w` >> simp[]) >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> simp[] >>
  `!D. ?out t G' tn'.
       Var (STRING #"%" (toString sa.cs_next_var)) = Var out /\
       t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
       G' = step_prov PG G (mk_inst sa.cs_next_id opc [] [out]) (update_var out w s) /\
       tn' = step_taint (mk_inst sa.cs_next_id opc [] [out]) s (update_var out w s) tn /\
       gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
       eval_operand (Var out) t = SOME w /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qx_gen_tac `Dh` >>
     qpat_assum `!D out. opc <> INVOKE /\ _` (qspec_then `Dh` assume_tac) >>
     mp_tac (Q.INST [`args` |-> `[]:operand list`, `a` |-> `sa`, `b` |-> `sb`, `D` |-> `Dh`]
                     typed_copy_origin_ptr_emit_op_path) >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_x_assum (qspec_then `""` mp_tac) >> simp[]) >>
     strip_tac >> gvs[]) >>
  simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  conj_tac >- (qpat_x_assum `!D. ?out t G' tn'. _` mp_tac >> simp[update_var_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME ins` >>
  `step_inst_base ins s = OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by
    simp[Abbr `ins`] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by simp[] >>
  drule_all alloca_history_base_step >>
  qpat_assum `!D out. opc <> INVOKE /\ _` (qspecl_then [`ARB`, `""`] strip_assume_tac) >>
  simp[Abbr `ins`, mk_inst_def, update_var_def]
QED

Theorem scalar_read_value_post[local]:
  is_word_type (expr_type e) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v) /\
  eval_operand op t = SOME (val_to_w256 v) /\
  stmt_state_rel H ctx func cenv cx es t /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) t /\
  storage_well_formed_on cx es (FST H) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas ==>
  expr_post_mods H ctx func cenv cx e es sa sb s (es with gas_obs := []) v op t
Proof
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  simp[expr_post_mods_def, expr_post_def, expr_val_rel_def, expr_val_at_def,
       stmt_state_rel_start_gas_obs, locals_kept_def, pure_frame_def,
       popped_kept_def, vyperEvalScopesProgressTheory.scopes_progress_refl]
QED

Theorem scalar_zero_operand_value[local]:
  is_word_type (expr_type e) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := tail) =
          (INL v, es with gas_obs := tail)) /\
  (!sa op sb. lower_value compile_expr cenv ty e sa = (op,sb) ==>
    ?opc. MEM opc ^read_opcodes /\ emit_op opc [] sa = (op,sb) /\
      !s id out. call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx ==>
        step_inst_base (mk_inst id opc [] [out]) s = OK (update_var out (val_to_w256 v) s)) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule stmt_state_rel_state_rel >> disch_then (assume_tac o MATCH_MP state_rel_call_ctx_rel) >>
  suspend "path"
QED

Resume scalar_zero_operand_value[path]:
  qpat_assum `!sa op sb. lower_value _ _ _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo s0` by fs[ghost_inv_at_mods_def] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id opc [] [out]) s0 =
         OK (update_var out (val_to_w256 v) s0)` by simp[] >>
  drule_all_then (qspecl_then [`tn0`, `gas_explicit_sites ctx shadow_ctx`, `PG`, `G0`]
      strip_assume_tac) scalar_read_path >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`es`,`INL v`,`t`,`tn'`] >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  suspend "post"
QED

Resume scalar_zero_operand_value[post]:
  `~not_fresh_at sa out` by simp[not_fresh_at_def] >>
  drule_all_then strip_assume_tac scalar_read_ghost_update >>
  `not_local_ptr cenv es.scopes out` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es t` by
    (drule_all stmt_state_rel_update_var >>
     disch_then (qspec_then `val_to_w256 v` mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  `immutable_frame_mods func cenv cx (es with gas_obs := []) t` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`es`,`s0`,`sa`] >>
     simp[update_var_def]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G' tn' t` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G0`,`es`,`s0`,`sa`,`tn0`] >>
     simp[update_var_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s0` mp_tac >>
     simp[allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  qpat_x_assum `MEM opc _` kall_tac >> gvs[] >>
  simp[expr_store_bound_def, ptr_val_ok_def, ghost_kept_at_def] >>
  reverse conj_tac >- simp[update_var_def] >>
  irule scalar_read_value_post >> simp[update_var_def]
QED

Finalise scalar_zero_operand_value

Theorem env_reads_value_mods[local]:
  i <> PrevHash /\ i <> MsgGas ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (env_item_type i) (Env i) []) es
Proof
  strip_tac >> drule_all env_scalar_source >>
  disch_then (qspecl_then [`es`,`cx`] strip_assume_tac) >>
  irule scalar_zero_operand_value >> simp[expr_type_def] >>
  rpt strip_tac >> drule_all env_scalar_emission >> simp[]
QED

Theorem calldatalen_value_mods[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (BaseT (UintT 256)) CalldataLen []) es
Proof
  irule scalar_zero_operand_value >> simp[expr_type_def, is_word_type_def] >>
  qexists_tac `IntV &LENGTH cx.txn.calldata` >>
  simp[calldata_source_all_tails,
       vyperValueTheory.evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  rpt strip_tac >> drule calldatalen_scalar_emission >>
  simp[val_to_w256_def]
QED

Theorem env_read_scalar_sim_mods:
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) ==>
  !DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty a bt args es.
    ((?i. bt = Env i /\ i <> PrevHash /\ i <> MsgGas) \/ bt = CalldataLen) /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin a bt args) es
Proof
  strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[] >> drule expr_body_pre_mods_well_typed >>
      simp[well_typed_expr_def, well_typed_builtin_app_def] >> strip_tac >> gvs[] >>
      conj_asm1_tac >- simp[env_reads_value_mods] >>
      first_assum irule >> simp[expr_type_def, eval_expr_builtin_value] >>
      `is_word_type (env_item_type i)` by (Cases_on `i` >> simp[env_item_type_def, is_word_type_def]) >>
      simp[] >> reverse conj_tac >- metis_tac[eval_expr_builtin_value] >>
      gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var i sa` >> simp[as_stack_val_def]) >>
  gvs[] >> drule expr_body_pre_mods_well_typed >>
  simp[well_typed_expr_def, well_typed_builtin_app_def] >> strip_tac >> gvs[] >>
  conj_asm1_tac >- simp[calldatalen_value_mods] >>
  first_assum irule >>
  simp[expr_type_def, is_word_type_def, compile_calldata_len_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
