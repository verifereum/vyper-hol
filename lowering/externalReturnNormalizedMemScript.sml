(* The actual external Return branch with a typed normalization prefix. *)
Theory externalReturnNormalizedMem
Ancestors
  externalReturnDirectMem externalReturnNormalizeRun externalNormalizePremises
  externalReturnSelectedMetadata externalReturnEncoderSuffixMem
  stmtSimReturnWiden typedStoreEndpoint externalReturnPrefix returnValueTyped
  incompatibleReturnLayout
  vyperTypeSystem stmtLowering exprLoweringProps loweringPosts
  exprSimDefs vyperTypeArgFits compileEnv typedNormalizeEntryBoundary
  stmtLoweringMono fragExec exprOperandVar externalReturnRegisteredWindowMem
  externalReturnZeroLayout externalReturnEncoderSites externalRawReturnType
  bodySim compileVyper externalReturnDirectSource externalReturnWindowResources
  valueEncodingProofs vyperABI vyperTypeABI loweringHalt

val _ = Parse.hide "body";

(* A returned value read at its physical (lowered) type: typed there, and
   widening to the return type. *)
Theorem return_value_physical_typed:
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) =
    (INL v, es') /\
  post_value_type cenv e = lowered_value_type cenv e ==>
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret /\
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
        value_has_type stv v
Proof
  strip_tac >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ret` by
    (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
     simp[type_stmt_def, AllCaseEqs()]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  drule_all exprSimHypsTheory.post_value_type_widens >> strip_tac >>
  conj_tac >- metis_tac[vyperTypeArgFitsTheory.type_widens_to_trans] >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[] >>
      `(do r <- eval_expr cx (Call ty (IntCall fid) args drv);
           read_result cx r od) (es with gas_obs := g) = (INL v, es')` by
        (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
      drule_all exprSimHypsTheory.ifexp_intcall_read_physical_typed >>
      simp[]) >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_not_int_call] >>
  drule_all return_value_typed >> simp[]
QED

Theorem external_frame_ret_value_normalized_run_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa0 func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env0 /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa0) ==>
    !cenv' env lctx e es sa sb cenv'' s0 op s1 ee v t.
       same_frame cenv cenv' /\
       expr_sim_inv cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
       stmt_exprs_ok cenv' (Return (SOME e)) /\
       IS_SOME (type_stmt env ret (Return (SOME e))) /\
       call_evaluation_safe
         (initial_evaluation_context am.sources am.layouts tx NONE)
         (int_calls_stmt (Return (SOME e))) /\
       stmt_env cenv' lctx ret (Return (SOME e)) sa = (cenv'', sb) /\
       lower_value compile_expr cenv' ret e sa = (op, s1) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv' sa /\ ~block_is_terminated sa /\
       stmt_state_rel unit.cu_context func cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) es s0 /\
       alloca_history func s0 /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       expr_post unit.cu_context func cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE)
         e es sa s1 s0 ee v op t /\
       (?gs ee'.
          bind (eval_expr
                  (initial_evaluation_context am.sources am.layouts tx NONE) e)
            (read_result
               (initial_evaluation_context am.sources am.layouts tx NONE))
            (es with gas_obs := gs) = (INL v, ee')) /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ~t.vs_halted /\
       (~is_word_type ret /\
         ~(is_bytestring_type (lowered_value_type cenv' e) /\
           is_bytestring_type ret) /\
         lowered_value_type cenv' e <> ret) ==>
       ?fuel r. run_from fuel unit.cu_context func t = r /\ exit_result r /\
                mem_safe_run fuel unit.cu_context func t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_package_frame_exit >> strip_tac >>
  qmatch_asmsub_abbrev_tac `expr_post ctx func cenv' cx` >>
  qpat_x_assum `?gs ee'. _` strip_assume_tac >>
  `post_value_type cenv' e = lowered_value_type cenv' e` by
    (`well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ret` by
       (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
        simp[type_stmt_def, AllCaseEqs()]) >>
     Cases_on `lowered_value_type cenv' e = expr_type e \/
       is_bytestring_type (expr_type e) /\
       is_bytestring_type (lowered_value_type cenv' e) /\
       arg_type_fits (lowered_value_type cenv' e) (expr_type e)`
     >- (pop_assum strip_assume_tac
         >- metis_tac[post_value_type_lowered] >>
         metis_tac[type_widens_from_bytestring]) >>
     drule_all incompatible_return_layout_intcall >> strip_tac >>
     simp[post_value_type_def]) >>
  drule_all return_value_physical_typed >> strip_tac >>
  `~(is_bytestring_type ret /\
     is_bytestring_type (lowered_value_type cenv' e))` by metis_tac[] >>
  drule_all normalize_return_source_kinds >> strip_tac >>
  suspend "compile"
QED

Resume external_frame_ret_value_normalized_run_mem[compile]:
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv' ret) s1` >>
  rename1 `compile_alloc_buffer _ s1 = (nbuf,s2)` >>
  Cases_on `compile_store_memory_typed cenv' nbuf.buf_operand ret op
    (lowered_value_type cenv' e) s2` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (u,s3)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  `compile_external_return (SOME nbuf.buf_operand) F cenv'.ce_raw_return
    cenv'.ce_ret_enc_info cenv'.ce_max_return_size F
    (FST (SND cenv'.ce_nonreentrant))
    (FST (SND (SND cenv'.ce_nonreentrant)))
    (SND (SND (SND cenv'.ce_nonreentrant))) s3 = ((),sb)` by
    (Cases_on `compile_external_return (SOME nbuf.buf_operand) F cenv'.ce_raw_return
      cenv'.ce_ret_enc_info cenv'.ce_max_return_size F
      (FST (SND cenv'.ce_nonreentrant))
      (FST (SND (SND cenv'.ce_nonreentrant)))
      (SND (SND (SND cenv'.ce_nonreentrant))) s3` >> gvs[]) >>
  `ci_mono sa (SND (lower_value compile_expr cenv' ret e sa))` by
    (irule ci_mono_lower_value_cfn >> simp[cj 1 compile_expr_ci_mono]) >>
  `cs_extends sa s1` by
    (qpat_x_assum `ci_mono sa (SND _)` mp_tac >>
     asm_rewrite_tac[] >> simp[ci_mono_def]) >>
  `cs_extends s1 s2` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_def, pairTheory.SND] >>
  `cs_extends s2 s3` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `cs_extends s3 sb` by
    metis_tac[cj 3 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  `cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code s3 sb func` by metis_tac[fn_has_code_split] >>
  `(emitted_blocks s2 s3 <> [] ==> ?bb.
      lookup_block s3.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)` by
    (drule normalize_typed_external_return_entry >>
     disch_then drule >> simp[] >> disch_then drule >> simp[]) >>
  suspend "resources"
QED

Resume external_frame_ret_value_normalized_run_mem[resources]:
  `!x. op = Var x ==> not_fresh_at s1 x` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `local_ptrs_reserved _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[compile_lower_value_var]) >>
  `local_ptrs_reserved cenv' s1` by
    (irule compiler_ci_mono_reserved >> qexists_tac `sa` >>
     qpat_x_assum `ci_mono sa (SND _)` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_x_assum `cenv' = cenv''` (SUBST_ALL_TAC o SYM) >>
  drule_all normalize_external_frame_resources >>
  simp[GSYM (markerTheory.Abbrev_def)] >> strip_tac >>
  qpat_assum `post_value_type cenv' e = _` (fn th =>
    qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_post_def, th])) >>
  `sfields_tenv_consistent cenv'.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv'.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     rewrite_tac[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all normalize_source_window >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) normalize_return_store_mem_cont >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand op t = _`)) >>
  disch_then (qspec_then `stv` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> suspend "suffix"
QED

Resume external_frame_ret_value_normalized_run_mem[suffix]:
  `ret <> NoneT` by metis_tac[valued_return_type_not_none] >>
  drule_all external_package_encoder_admissible >> strip_tac >>
  drule_all external_package_raw_flag >> strip_tac >>
  `~cenv'.ce_raw_return` by
    (strip_tac >>
     `lookup_raw_return_or_F (NONE : num option) tx.function_name External tops` by
       metis_tac[] >>
     drule_all source_typing_raw_return_type >> strip_tac >>
     gvs[is_bytestring_type_def]) >>
  `cenv'.ce_is_external` by suspend "external_flag" >>
  `return_buffer_ok cenv'` by
    (qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
     simp[stmt_exprs_ok_def, stmt_valued_return_def]) >>
  qpat_x_assum `Abbrev (cx = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all selected_external_frame_source_abi_metadata >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_enc_plan tenv (if wrap then _ else _) _` >>
  `?at rv. abi_encoder_window_input cenv'.ce_ret_enc_info at rv b
      (type_memory_size dtv) t'.vs_memory /\
      LENGTH (enc at rv) <= cenv'.ce_max_return_size` by suspend "window" >>
  suspend "execution"
QED

Resume external_frame_ret_value_normalized_run_mem[window]:
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  qpat_x_assum `vyper_abi_size_bound _ _ = _` mp_tac >>
  qpat_x_assum `evaluate_type _ ret = SOME dtv` mp_tac >>
  qpat_x_assum `value_has_type dtv v` mp_tac >>
  qpat_x_assum `val_in_memory dtv v b _` mp_tac >>
  qpat_x_assum `b + type_memory_size dtv <= _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `wrap` >> gvs[]
  >- (drule_all return_nominal_singleton_window >> metis_tac[]) >>
  `?av. vyper_to_abi tenv ret v = SOME av` by
    (irule (cj 1 vyper_to_abi_total) >> metis_tac[]) >>
  drule_all return_plan_nominal_source_window >> metis_tac[]
QED

Resume external_frame_ret_value_normalized_run_mem[execution]:
  `cenv'.ce_max_return_size < dimword (:256)` by
    (fs[return_buffer_ok_def, wordsTheory.dimword_def] >> decide_tac) >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  drule compile_external_return_abi_parts >> simp[] >> strip_tac >>
  `cs_extends s3 sa'` by
    (mp_tac (Q.SPECL [`cenv'.ce_max_return_size`, `s3`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sa' sb'` by
    (mp_tac (cj 2 ci_mono_compile_abi_encode) >>
     disch_then (qspecl_then [`buf.buf_operand`, `nbuf.buf_operand`,
       `cenv'.ce_ret_enc_info`, `sa'`] mp_tac) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sb' sb` by
    (mp_tac (Q.SPECL [`RETURN`, `[buf.buf_operand; len]`, `[]`, `sb'`]
       ci_mono_emit_inst) >> asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sa' sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code s3 sa' func /\ fn_has_code sa' sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sa' sb' func /\ fn_has_code sb' sb func` by
    metis_tac[fn_has_code_split] >>
  suspend "sites"
QED

Resume external_frame_ret_value_normalized_run_mem[sites]:
  `type_memory_bytes cenv' ret = type_memory_size dtv` by metis_tac[] >>
  `s1.cs_next_id < s3.cs_next_id` by
    (qpat_assum `compile_alloc_buffer (type_memory_bytes _ _) _ = _`
       (mp_tac o MATCH_MP compile_alloc_buffer_parts) >>
     strip_tac >>
     `ci_mono s2 s3` by
       metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
     fs[ci_mono_def] >> decide_tac) >>
  `s3.cs_next_id < sa'.cs_next_id` by
    (drule_at (Pat `compile_alloc_buffer _ s3 = _`) compile_alloc_buffer_parts >>
     simp[]) >>
  `s1.cs_next_id NOTIN frag_ids sa' sb'` by
    (irule encoder_fragment_prior_site_excluded >> decide_tac) >>
  `!x. nbuf.buf_operand = Var x ==> not_fresh_at s3 x` by
    (qpat_assum `compile_alloc_buffer (type_memory_bytes _ _) _ = _`
       (mp_tac o MATCH_MP compile_alloc_buffer_parts) >>
     strip_tac >>
     `ci_mono s2 s3` by
       metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
     fs[ci_mono_def, not_fresh_at_def]) >>
  suspend "sizes"
QED

Resume external_frame_ret_value_normalized_run_mem[sizes]:
  `!inst n base sz. MEM inst (fn_insts func) /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ ee t` mp_tac >>
     rewrite_tac[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!pz zz. FLOOKUP t'.vs_allocas s3.cs_next_id = SOME (pz,zz) ==>
      zz = cenv'.ce_max_return_size` by
    (map_every qx_gen_tac [`pz`, `zz`] >> strip_tac >>
     `FLOOKUP t.vs_allocas s3.cs_next_id = SOME (pz,zz)` by
       (qpat_x_assum `!aid. aid <> _ ==> _` (qspec_then `s3.cs_next_id` mp_tac) >>
        simp[] ) >>
     qpat_x_assum `compile_alloc_buffer (type_memory_bytes _ _) _ = _` kall_tac >>
     drule_all actualAllocExecTheory.actual_alloc_buffer_site >> strip_tac >>
     first_x_assum (drule_at (Pat `MEM _ _`)) >>
     simp[venomInstTheory.mk_inst_def]) >>
  `!inst pz zz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids sa' sb' /\
      FLOOKUP t'.vs_allocas inst.inst_id = SOME (pz,zz) ==> zz = 32` by
    (rpt gen_tac >> strip_tac >>
     `inst.inst_id <> s1.cs_next_id` by metis_tac[] >>
     `FLOOKUP t.vs_allocas inst.inst_id = SOME (pz,zz)` by metis_tac[] >>
     drule_all encoder_function_alloca_shape >> strip_tac >>
     qpat_x_assum `!inst n base sz. _ ==> sz = w2n n`
       (qspec_then `inst` mp_tac) >>
     qpat_x_assum `FLOOKUP t.vs_allocas inst.inst_id = SOME (pz,zz)` mp_tac >>
     qpat_x_assum `inst.inst_operands = [Lit 32w]` mp_tac >>
     qpat_x_assum `inst.inst_opcode = ALLOCA` mp_tac >>
     qpat_x_assum `MEM inst (fn_insts func)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[wordsTheory.dimword_def]) >>
  suspend "exit"
QED

Resume external_frame_ret_value_normalized_run_mem[exit]:
  qpat_x_assum `compile_alloc_buffer (type_memory_bytes _ _) _ = _` kall_tac >>
  drule registered_encoder_allocate_window >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`s1.cs_next_id`, `type_memory_size dtv`, `ctx`] mp_tac) >>
  impl_tac >- suspend "allocation_pre" >> strip_tac >>
  drule_all abi_encoder_return_safe_exit >> strip_tac >>
  qpat_x_assum `mem_cont_sim _ _ t t'` mp_tac >>
  qpat_x_assum `mem_cont_sim _ _ t' u` mp_tac >>
  qpat_x_assum `run_from _ _ _ u = r` mp_tac >>
  qpat_x_assum `exit_result r` mp_tac >>
  qpat_x_assum `mem_safe_run _ _ _ u` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  metis_tac[memContinuationExitTheory.mem_cont_sim_safe_exit]
QED

Resume external_frame_ret_value_normalized_run_mem[allocation_pre]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Resume external_frame_ret_value_normalized_run_mem[external_flag]:
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  qpat_x_assum `same_frame _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  drule entryStateRelTheory.compile_register_positional_args_cenv >> strip_tac >>
  `cenv0.ce_is_external` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     strip_tac >> gvs[update_cenv_nonreentrant_def] >>
     Cases_on `ret = NoneT` >>
     simp[update_cenv_ret_abi_def, build_compile_env_def, pairTheory.UNCURRY]) >>
  `cenv.ce_is_external` by
    (qpat_x_assum `_ = _ with ce_vars := _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `same_frame _ _`
    (strip_assume_tac o REWRITE_RULE [same_frame_def]) >>
  `cenv'.ce_is_external = cenv.ce_is_external` by
    (qpat_x_assum `_ with <|ce_vars := _; ce_var_type := _;
      ce_dynarray_capacity := _|> = _` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[]
QED

Finalise external_frame_ret_value_normalized_run_mem
