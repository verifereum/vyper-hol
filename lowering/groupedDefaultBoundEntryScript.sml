(* Continue a normal grouped initializer at the common positional registration. *)
Theory groupedDefaultBoundEntry
Ancestors
  groupedRuntimeEndpoint groupedRegisteredBody groupedEntryCommon groupedDefaultBinding
  groupedDefaultArguments groupedDefaultHorizon groupedEntryPackage fragGasOriginPtrDead
  entryPtrSeamRegister entryLocals argumentRegistrationOpen defaultEntrySourcePreparation
  calldataRegistrationLocals externalBodyFrame entryStateRel moduleLowering compileVyper
  constSubstCorrect vyperInterpreter vyperStorageFootprint vyperState
  ptrDiscipline bodyPtrDefs venomMemDefs venomState compileEnv
  sourceUnitExecution loweringStateRelDefs selectedAcceptedFold exprLoweringProps
  abiDecoderCoherence vyperCalldata vyperTypeContract vyperContext e2eDefs
  fragGasOriginPtr fragExec gasShadowRunLowering gasShadowState gasShadow
  gasShadowModuleDefs venomInst emitHelper runtimeEntryEndpoint
  whitelistCheckerConsts valueEncoding externalBodySupport externalEntryBound
  groupedEntryResources venomWf emitHelperProps bodySimEntry exprLowering
  bodyFullHashKeccakFixed venomFnInstsProofs registrationRejectMetadata
  finite_map list rich_list alist pair words

Theorem grouped_normal_prefix_dead[local]:
  gas_origin_ptr_path (cx_dead ([],[]) cx,0,explicit,ctx,fn,PG)
    (s,G,tn) marks (OK u,J,tz) ==>
  !D. gas_origin_ptr_path (D,0,explicit,ctx,fn,PG) (s,G,tn) marks (OK u,J,tz)
Proof
  strip_tac >> gen_tac >> irule gas_origin_ptr_path_dead_mono >>
  goal_assum (drule_at Any) >> simp[cx_dead_def, storage_dead_def]
QED

Theorem grouped_bind_typed_values[local]:
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs /\
  LIST_REL value_has_type tvs vals ==>
  ?env. bind_arguments tenv args vals = SOME env
Proof
  strip_tac >> irule decoded_arguments_bind >>
  fs[LIST_REL_EL_EQN] >> gen_tac >> strip_tac >>
  `n < LENGTH args /\ n < LENGTH tvs` by simp[] >>
  qpat_assum `!i. i < LENGTH args ==> _` (qspec_then `n` assume_tac) >>
  Cases_on `EL n args` >> fs[EL_MAP] >>
  qexists_tac `EL n tvs` >> simp[]
QED

Theorem grouped_default_normal_bound_entry:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  ctx = unit.cu_context /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  ss = subst_consts_stmts (module_consts_env tops []) fbody /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,ss)) =
    (lbl,ce0,pa,mc,pay,nr,key,ut,view,ss,rt) /\
  package_external_group tops rpolicy.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
     tx.function_name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,ss) =
    ExternalDefaults common entries specs off /\
  pos = TAKE (LENGTH args - LENGTH dflts) args /\
  kw = DROP (LENGTH args - LENGTH dflts) args /\
  MAP (\(name,_,ty,_). (name,ty)) vars = kw /\
  ALL_DISTINCT (MAP (\(_,op,_,_). op) vars) /\
  kwtvs = MAP (\(_,_,_,tv). tv) slots /\
  LIST_REL (\(name,dst,ty,e) (aid,q,p,tv).
    dst = Var q /\ type_memory_bytes common.ec_env ty = type_memory_size tv /\
    MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [q]) (fn_insts fn)) vars slots /\
  LIST_REL (\(aid,q,p,tv) v.
    aid < cut.cs_next_id /\ not_fresh_at entry q /\
    FLOOKUP u.vs_allocas aid = SOME (p,type_memory_size tv) /\
    lookup_var q u = SOME (n2w p) /\ ptr_covers J tz q u (type_memory_size tv) /\
    value_has_type tv v /\
    (!mem. mem_agree_outside tz.t_mem u.vs_memory mem ==> val_in_memory tv v p mem)) slots kwvals /\
  LIST_REL value_has_type ptvs pvals /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) (ptvs ++ kwtvs) /\
  LENGTH pos = LENGTH ptvs /\
  (!c arg tv. MEM (arg,tv) (ZIP (args,ptvs ++ kwtvs)) /\
    c = common.ec_env with ce_vars := c.ce_vars ==>
      selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
      abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv) /\
  EVERY (\tv. type_memory_size tv < dimword (:256)) (ptvs ++ kwtvs) /\
  LIST_REL (\arg tv. type_memory_bytes ce0 (SND arg) = type_memory_size tv) pos ptvs /\
  calldata_decode_args u.vs_call_ctx.cc_calldata ptvs 0 = SOME pvals /\
  4 + SUM (MAP tv_abi_size ptvs) < dimword (:256) /\
  pvals ++ kwvals = tx.args ++ values /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),s1) /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  EVERY (runtime_constant_expr [(NONE,tops)])
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) /\
  no_sha256_exprs (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) /\
  (!tail. eval_exprs cx (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
    (s1 with gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail) =
    (INL values,ee with gas_obs := tail)) /\
  emit_inst JMP [Label common.ec_common_label] [] cut = ((),term) /\
  fn_has_code cut term fn /\
  entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
  cut.cs_next_id <= entry.cs_next_id /\
  compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
    common.ec_pos_args 4 entry = (ce,sa) /\ fn_has_code entry sa fn /\
  compile_guarded_body ce common.ec_nonreentrant common.ec_nkey common.ec_transient
    common.ec_view common.ec_body common.ec_return sa = ((),final) /\ fn_has_code sa final fn /\
  compile_guarded_body (gas_shadow_env T ce) common.ec_nonreentrant common.ec_nkey common.ec_transient
    common.ec_view (MAP gas_shadow_stmt common.ec_body) common.ec_return shadow_sa = ((),shadow_final) /\
  fn_has_code shadow_sa shadow_final shadow_fn /\ gas_shadow_state sa shadow_sa /\
  ctx.ctx_entry = SOME "__entry" /\ lookup_function "__entry" ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\ lookup_block "__entry" fn.fn_blocks = SOME bb /\
  fn_inst_ids_distinct fn /\
  (!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  gas_shadow_context ctx shadow_unit.cu_context /\ gas_shadow_function fn shadow_fn /\
  MEM shadow_fn shadow_unit.cu_context.ctx_functions /\
  explicit = gas_explicit_sites ctx shadow_unit.cu_context /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  s.vs_allocas = FEMPTY /\ selected_registration_resources ctx fn site 0 sf s /\
  unit_alloca_budget ctx < dimword (:256) /\
  at_point cut u /\ fresh_vars_wrt entry u /\ fresh_vars_wrt sa u /\
  (!aid pair. FLOOKUP u.vs_allocas aid = SOME pair ==> aid < entry.cs_next_id) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
    gas_origin_ptr_path (cx_dead H cx,0,explicit,ctx,fn,[]) (s,FEMPTY,entry_taint) marks (OK u,J,tz) /\
    stmt_state_rel H ctx fn (common.ec_env with ce_vars := FEMPTY) cx (ee with gas_obs := []) u /\
    ghost_inv_at (cx_dead H cx) 0 NONE (common.ec_env with ce_vars := FEMPTY)
      cx (ee with gas_obs := []) J tz u) ==>
  ?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args dflts ret ss
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (MAP FST args)` by metis_tac[external_selected_args_distinct] >>
  `pos ++ kw = args` by simp[TAKE_DROP] >>
  `common.ec_env = ce0 /\ common.ec_nonreentrant = nr /\
   common.ec_nkey = key /\ common.ec_transient = ut /\ common.ec_view = view /\
   common.ec_body = ss /\ common.ec_return = rt /\
   common.ec_pos_args = build_positional_args ce0 pos` by
    (drule_all grouped_package_common_environment >> simp[]) >>
  qpat_x_assum `common.ec_env = ce0` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qabbrev_tac `cekw = compile_register_kwarg_vars ce0 vars` >>
  `cekw with ce_vars := ce0.ce_vars = ce0` by
    simp[Abbr `cekw`, compile_register_kwarg_vars_cenv] >>
  `ce = cekw with ce_vars := ce.ce_vars` by
    metis_tac[compile_register_positional_args_cenv] >>
  `ce with ce_vars := ce0.ce_vars = ce0 /\
   ce with ce_vars := FEMPTY = ce0 with ce_vars := FEMPTY` by
    gvs[PULL_FORALL, compile_env_component_equality] >>
  `?envb. bind_arguments (type_env tops) args (pvals ++ kwvals) = SOME envb` by suspend "bind" >>
  `ee with gas_obs := [] = s1 with gas_obs := [] /\ ee.storage_trace = []` by suspend "frame" >>
  `!tail. external_entry_bound tops am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail) mut args dflts
      (ee with <|scopes := [envb]; gas_obs := tail|>)` by
    (qpat_assum `cx = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     qpat_assum `pvals ++ kwvals = _` (fn th =>
       qpat_assum `bind_arguments _ _ (pvals ++ kwvals) = _`
         (assume_tac o REWRITE_RULE [th])) >>
     drule_all_then strip_assume_tac grouped_defaults_bound_frame >> simp[]) >>
  `valid_horizon cx (initial_state am []) ([],[]) ee.storage_trace` by
    simp[grouped_default_empty_regions_horizon, storage_trace_regions_def, storage_trace_locks_def] >>
  first_x_assum (qspec_then `([],[])` (drule_then strip_assume_tac)) >>
  `!D. gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,FEMPTY,entry_taint) marks (OK u,J,tz)` by
    (drule grouped_normal_prefix_dead >> simp[]) >>
  `tz.t_stor = {} /\ tz.t_trans = {} /\ tz.t_imm = {}` by
    fs[ghost_inv_at_def, stor_taint_ok_at_def, cx_dead_def, storage_dead_def] >>
  qabbrev_tac `landed = jump_to entry.cs_current_bb u` >>
  `selected_registration_resources ctx fn site 0 entry landed /\
   stmt_state_rel (([],[]):(bool # bytes32 # type_value) list # num list)
     ctx fn (ce with ce_vars := FEMPTY) cx (ee with gas_obs := []) landed /\
   (!D exp. gas_origin_ptr_path (D,0,exp,ctx,fn,[]) (u,J,tz) [] (OK landed,J,tz))` by suspend "jump" >>
  `selected_registration_owners fn (MAP FST kw) kwtvs kwvals
      (LENGTH kw) cekw entry landed J tz` by suspend "owners" >>
  `(LIST_REL (\(name,ty) tv. ?loc. FLOOKUP cekw.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) pos ptvs) /\
    (!id ty. MEM (id,ty) args ==>
        (?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)) /\ ce.ce_var_type id = SOME ty) /\
    (!id loc. FLOOKUP ce.ce_vars id = SOME loc ==> MEM id (MAP FST args)) /\
    local_ptrs_reserved ce sa` by suspend "maps" >>
  suspend "register"
QED

Resume grouped_default_normal_bound_entry[bind]:
  irule grouped_bind_typed_values >> goal_assum (drule_at Any) >>
  `LIST_REL value_has_type kwtvs kwvals` suffices_by
    (strip_tac >> qpat_assum `pvals ++ kwvals = _` (SUBST1_TAC o SYM) >>
     irule LIST_REL_APPEND_suff >> asm_rewrite_tac[]) >>
  qpat_assum `kwtvs = _` SUBST1_TAC >> pure_rewrite_tac[LIST_REL_MAP1] >>
  qpat_assum `LIST_REL _ slots kwvals` mp_tac >> match_mp_tac LIST_REL_mono >>
  simp[pairTheory.FORALL_PROD, combinTheory.o_DEF]
QED

Resume grouped_default_normal_bound_entry[frame]:
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[source_deployment_rel_def, initial_evaluation_context_def] >>
  qpat_assum `!tail. eval_exprs _ _ _ = _`
    (qspec_then `[]:bytes32 list` assume_tac) >>
  drule_all grouped_checked_default_source_frame >> simp[] >> strip_tac >>
  drule external_send_call_value_frame >>
  fs[evaluation_state_component_equality, initial_state_def]
QED

Resume grouped_default_normal_bound_entry[jump]:
  qpat_assum `entry.cs_current_bb = _` (fn th =>
    qpat_assum `emit_inst JMP _ _ cut = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
  conj_tac
  >- (drule_all grouped_initializer_registration_start >>
      simp[GSYM markerTheory.Abbrev_def]) >>
  conj_tac >-
    (qunabbrev_tac `landed` >>
     qpat_assum `ce with ce_vars := FEMPTY = _`
       (fn th => pure_rewrite_tac [th,stmt_state_rel_jump_to]) >>
     first_assum ACCEPT_TAC) >>
  drule_all grouped_initializer_registration_start >>
  simp[GSYM markerTheory.Abbrev_def]
QED

Resume grouped_default_normal_bound_entry[owners]:
  `MAP FST kw = MAP (\(name,_,_,_). name) vars /\ LENGTH kw = LENGTH vars` by
    (qpat_assum `MAP _ vars = kw` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  qpat_assum `Abbrev (landed = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  irule grouped_jump_registration_owners >> asm_rewrite_tac[] >> qexists_tac `cut` >>
  asm_rewrite_tac[] >>
  qunabbrev_tac `cekw` >> irule grouped_initialized_keyword_owners >> simp[] >>
  conj_tac
  >- (qpat_assum `MAP FST kw = _` (SUBST1_TAC o SYM) >>
      qpat_assum `ALL_DISTINCT (MAP FST args)` mp_tac >>
      qpat_assum `pos ++ kw = args` (SUBST1_TAC o SYM) >>
      simp_tac bool_ss [MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  qpat_assum `LIST_REL _ slots kwvals` mp_tac >>
  match_mp_tac LIST_REL_mono >> simp[pairTheory.FORALL_PROD]
QED

Resume grouped_default_normal_bound_entry[maps]:
  drule source_typing_ok_type_def_keys_distinct >> strip_tac >>
  drule_all registration_package_inputs >> strip_tac >>
  `MAP FST kw = MAP (\(name,_,_,_). name) vars` by
    (qpat_assum `MAP _ vars = kw` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  `ALL_DISTINCT (MAP FST pos) /\ ALL_DISTINCT (MAP FST kw) /\
   (!id. MEM id (MAP FST pos) ==> ~MEM id (MAP FST kw))` by
    (qpat_assum `ALL_DISTINCT (MAP FST args)` mp_tac >>
     qpat_assum `pos ++ kw = args` (SUBST1_TAC o SYM) >>
     simp_tac bool_ss [MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qabbrev_tac `kwmap = MAP (\(id,op,ty,e). (id,PtrVar op (type_memory_bytes ce0 ty))) (REVERSE vars)` >>
  `MAP FST kwmap = REVERSE (MAP FST kw)` by
    simp[Abbr `kwmap`, MAP_MAP_o, MAP_REVERSE, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
  `!id. FLOOKUP cekw.ce_vars id =
     case ALOOKUP kwmap id of SOME loc => SOME loc | NONE => FLOOKUP ce0.ce_vars id` by
    simp[Abbr `cekw`, Abbr `kwmap`, compile_register_kwarg_vars_cenv] >>
  `!id. MEM id (MAP FST pos) ==> FLOOKUP cekw.ce_vars id = FLOOKUP ce0.ce_vars id` by
    (rpt strip_tac >> `ALOOKUP kwmap id = NONE` by
       (qpat_assum `MAP FST kwmap = _`
          (fn eq => pure_rewrite_tac [ALOOKUP_NONE,eq,MEM_REVERSE]) >>
        qpat_assum `!id. MEM id (MAP FST pos) ==> _` (drule_then ACCEPT_TAC)) >>
     qpat_assum `!id. FLOOKUP cekw.ce_vars id = _` (qspec_then `id` mp_tac) >>
     simp[]) >>
  `!id loc. FLOOKUP ce0.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    (rpt gen_tac >> strip_tac >> CCONTR_TAC >>
     qpat_assum `!k. ~MEM k (MAP FST args) ==> _` (drule_then mp_tac) >> simp[]) >>
  `!id loc. FLOOKUP cekw.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    (rpt gen_tac >> strip_tac >> Cases_on `ALOOKUP kwmap id`
     >- (qpat_assum `!id. FLOOKUP cekw.ce_vars id = _` (qspec_then `id` mp_tac) >>
         simp[] >> strip_tac >>
         qpat_assum `!id loc. FLOOKUP ce0.ce_vars id = SOME loc ==> _` irule >>
         qexists_tac `loc` >> simp[]) >>
     `MEM id (MAP FST kw)` by
       (CCONTR_TAC >> `ALOOKUP kwmap id = NONE` by
         (qpat_assum `MAP FST kwmap = _`
            (fn eq => pure_rewrite_tac [ALOOKUP_NONE,eq,MEM_REVERSE]) >>
          first_assum ACCEPT_TAC) >> fs[]) >>
     qpat_assum `pos ++ kw = args` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac[MAP_APPEND,MEM_APPEND] >> disj2_tac >> first_assum ACCEPT_TAC) >>
  `!id ty. MEM (id,ty) args ==>
    ?off. FLOOKUP ce0.ce_vars id = SOME (MemLoc off (type_memory_bytes ce0 ty))` by
    (rpt gen_tac >> strip_tac >> qpat_assum `EVERY _ args` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(id,ty)` mp_tac) >> simp[FST,SND]) >>
  `!id ty. MEM (id,ty) pos ==>
    ?off. FLOOKUP cekw.ce_vars id = SOME (MemLoc off (type_memory_bytes ce0 ty))` by
    (rpt gen_tac >> strip_tac >>
     `MEM id (MAP FST pos)` by (pure_rewrite_tac[MEM_MAP] >> qexists_tac `(id,ty)` >> simp[]) >>
     `MEM (id,ty) args` by
       (qpat_assum `pos ++ kw = args` (SUBST1_TAC o SYM) >> pure_rewrite_tac[MEM_APPEND] >>
        disj1_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!id. MEM id (MAP FST pos) ==> _` (drule_then SUBST1_TAC) >>
     qpat_assum `!id ty. MEM (id,ty) args ==> _` (drule_then ACCEPT_TAC)) >>
  suspend "maps_rest"
QED

Resume grouped_default_normal_bound_entry[maps_rest]:
  conj_tac
  >- (qpat_assum `LIST_REL _ pos ptvs` mp_tac >> pure_rewrite_tac[LIST_REL_EL_EQN] >>
      strip_tac >> conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >> Cases_on `EL n pos` >>
      rename1 `EL n pos = (id,ty)` >>
      `MEM (id,ty) pos` by (pure_rewrite_tac[MEM_EL] >> qexists_tac `n` >> simp[]) >>
      qpat_assum `!id ty. MEM (id,ty) pos ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!n. n < LENGTH pos ==> _` (qspec_then `n` mp_tac) >>
      qpat_assum `EL n pos = (id,ty)`
        (fn eq => simp_tac bool_ss [eq,SND,pairTheory.UNCURRY]) >>
      qpat_assum `n < LENGTH pos` (fn th => simp_tac bool_ss [th]) >>
      strip_tac >> qexists_tac `MemLoc off' (type_memory_bytes ce0 ty)` >>
      conj_tac >- (pure_rewrite_tac[FST] >> first_assum ACCEPT_TAC) >>
      qpat_assum `type_memory_bytes ce0 ty = _`
        (fn th => simp_tac bool_ss [th,var_location_memory_size_def])) >>
  `!id. MEM id (MAP FST kw) <=> ALOOKUP kwmap id <> NONE` by
    (gen_tac >> qpat_assum `MAP FST kwmap = _`
       (fn eq => pure_rewrite_tac[ALOOKUP_NONE,eq,MEM_REVERSE]) >> simp[]) >>
  `!id op n. ALOOKUP kwmap id = SOME (PtrVar op n) ==>
    ?ty e. MEM (id,op,ty,e) vars` by
    (rpt gen_tac >> strip_tac >>
     `MEM (id,PtrVar op n) kwmap` by metis_tac[ALOOKUP_MEM] >>
     pop_assum mp_tac >> simp[Abbr `kwmap`,MEM_MAP,MEM_REVERSE,pairTheory.EXISTS_PROD] >>
     metis_tac[]) >>
  `!id loc. ALOOKUP kwmap id = SOME loc ==> ?op n. loc = PtrVar op n` by
    (rpt gen_tac >> strip_tac >>
     `MEM (id,loc) kwmap` by metis_tac[ALOOKUP_MEM] >>
     pop_assum mp_tac >> simp[Abbr `kwmap`,MEM_MAP,MEM_REVERSE,pairTheory.EXISTS_PROD] >>
     metis_tac[]) >>
  suspend "maps_reserved"
QED

Resume grouped_default_normal_bound_entry[maps_reserved]:
  `!id op ty e. MEM (id,op,ty,e) vars ==> ?p. op = Var p /\ not_fresh_at entry p` by
    (rpt gen_tac >> pure_rewrite_tac[MEM_EL] >>
     disch_then (qx_choose_then `i` strip_assume_tac) >>
     qpat_assum `LIST_REL _ vars slots` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LIST_REL _ slots kwvals` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     `i < LENGTH slots` by simp[] >>
     qpat_assum `!n. n < LENGTH vars ==> _` (drule_then assume_tac) >>
     qpat_assum `!n. n < LENGTH slots ==> _` (drule_then assume_tac) >>
     qabbrev_tac `row = EL i slots` >> PairCases_on `row` >>
     qpat_assum `(id,op,ty,e) = EL i vars` (SUBST_ALL_TAC o SYM) >>
     pop_assum kall_tac >> ntac 2 (pop_assum mp_tac) >>
     simp[pairTheory.UNCURRY] >> rpt strip_tac >> qexists_tac `row1` >> simp[]) >>
  `!id op sz. FLOOKUP cekw.ce_vars id = SOME (PtrVar op sz) ==>
    ?ty e. MEM (id,op,ty,e) vars` by
    (rpt gen_tac >> strip_tac >>
     `MEM id (MAP FST args)` by
       (qpat_assum `!id loc. FLOOKUP cekw.ce_vars id = SOME loc ==> _` (drule_then ACCEPT_TAC)) >>
     Cases_on `ALOOKUP kwmap id` >>
     qpat_assum `!id. FLOOKUP cekw.ce_vars id = _` (qspec_then `id` mp_tac) >>
     simp[] >> strip_tac
     >- (`?ty. MEM (id,ty) args` by
           (qpat_assum `MEM id (MAP FST args)` mp_tac >>
            simp_tac bool_ss [MEM_MAP, pairTheory.EXISTS_PROD,FST] >> metis_tac[]) >>
         pop_assum strip_assume_tac >>
         qpat_assum `!id ty. MEM (id,ty) args ==> _` (drule_then strip_assume_tac) >> fs[]) >>
     qpat_assum `!id op n. ALOOKUP kwmap id = SOME (PtrVar op n) ==> _` irule >> gvs[]) >>
  suspend "maps_reserve_use"
QED

Resume grouped_default_normal_bound_entry[maps_reserve_use]:
  `!id1 ty1 e1 id2 ty2 e2 p. MEM (id1,Var p,ty1,e1) vars /\
    MEM (id2,Var p,ty2,e2) vars ==> id1 = id2` by
    (rpt gen_tac >> pure_rewrite_tac[MEM_EL] >> rpt strip_tac >>
     `n = n'` by
       (qspecl_then [`MAP (\(_,op,_,_). op) vars`,`n`,`n'`] mp_tac ALL_DISTINCT_EL_IMP >>
        qpat_assum `(id1,Var p,ty1,e1) = _` (fn x =>
          qpat_assum `(id2,Var p,ty2,e2) = _` (fn y =>
            simp_tac (srw_ss()) [EL_MAP,SYM x,SYM y])) >>
        simp[]) >>
     qpat_assum `n = n'` SUBST_ALL_TAC >>
     qpat_assum `(id1,Var p,ty1,e1) = _` mp_tac >>
     qpat_assum `(id2,Var p,ty2,e2) = _` (mp_tac o SYM) >>
     rpt (pop_assum kall_tac) >> metis_tac[pairTheory.PAIR_EQ]) >>
  `!id p sz. FLOOKUP cekw.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at entry p /\
    !id' sz'. FLOOKUP cekw.ce_vars id' = SOME (PtrVar (Var p) sz') ==> id = id'` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!id op sz. FLOOKUP cekw.ce_vars id = _ ==> _` (drule_then strip_assume_tac) >>
     conj_tac
     >- (qpat_assum `!id op ty e. MEM (id,op,ty,e) vars ==> _` (drule_then mp_tac) >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!id op sz. FLOOKUP cekw.ce_vars id = _ ==> _`
       (qspecl_then [`id'`,`Var p`,`sz'`] (drule_then strip_assume_tac)) >>
     qpat_assum `!id1 ty1 e1 id2 ty2 e2 p. _ ==> id1 = id2` irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `!id z n. FLOOKUP cekw.ce_vars id = SOME (MemLoc z n) ==> MEM id (MAP FST pos)` by
    (rpt gen_tac >> strip_tac >>
     `MEM id (MAP FST args)` by
       (qpat_assum `!id loc. FLOOKUP cekw.ce_vars id = SOME loc ==> _` (drule_then ACCEPT_TAC)) >>
     `~MEM id (MAP FST kw)` by
       (strip_tac >>
        qpat_assum `!id. MEM id (MAP FST kw) <=> _` (qspec_then `id` mp_tac) >>
        disch_then (drule_then assume_tac o iffLR) >>
        Cases_on `ALOOKUP kwmap id` >- fs[] >>
        qpat_assum `!id loc. ALOOKUP kwmap id = SOME loc ==> _` (drule_then strip_assume_tac) >>
        qpat_assum `!id. FLOOKUP cekw.ce_vars id = _` (qspec_then `id` mp_tac) >> simp[]) >>
     qpat_assum `MEM id (MAP FST args)` mp_tac >>
     qpat_assum `pos ++ kw = args` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac[MAP_APPEND,MEM_APPEND] >>
     qpat_assum `~MEM id (MAP FST kw)` (fn th => simp_tac bool_ss [th])) >>
  `cekw.ce_imm_alloca = NONE` by
    (drule targeted_external_package_layout >>
     qpat_assum `cekw with ce_vars := ce0.ce_vars = ce0` (SUBST1_TAC o SYM) >> simp[]) >>
  suspend "maps_finish"
QED

Resume grouped_default_normal_bound_entry[maps_finish]:
  `!id z n. FLOOKUP cekw.ce_vars id = SOME (MemLoc z n) ==>
    MEM id (MAP FST common.ec_pos_args)` by
    (qpat_assum `common.ec_pos_args = _` SUBST1_TAC >>
     pure_rewrite_tac[build_positional_args_FST] >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce sa /\
   !n. (?off sz. FLOOKUP cekw.ce_vars n = SOME (MemLoc off sz)) \/
       (?p sz. FLOOKUP cekw.ce_vars n = SOME (PtrVar (Var p) sz)) ==>
       ?p sz. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (drule compile_register_positional_args_reserved >> disch_then irule >>
     qpat_assum `cekw.ce_imm_alloca = NONE` (fn th =>
       simp_tac bool_ss [th, optionTheory.NOT_NONE_SOME]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  `!id. MEM id (MAP FST kw) ==> ?p sz. FLOOKUP cekw.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!id. MEM id (MAP FST kw) <=> _` (qspec_then `id` mp_tac) >>
     disch_then (drule_then assume_tac o iffLR) >>
     Cases_on `ALOOKUP kwmap id` >- fs[] >>
     qpat_assum `!id loc. ALOOKUP kwmap id = SOME loc ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `x = PtrVar _ _` SUBST_ALL_TAC >>
     qpat_assum `!id op n. ALOOKUP kwmap id = SOME (PtrVar op n) ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!id op ty e. MEM (id,op,ty,e) vars ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!id. FLOOKUP cekw.ce_vars id = _` (qspec_then `id` mp_tac) >> simp[]) >>
  `!id loc. FLOOKUP ce.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    (rpt gen_tac >> strip_tac >> drule_all compile_register_positional_args_bound >>
     strip_tac >>
     qpat_assum `!id loc. FLOOKUP cekw.ce_vars id = SOME loc ==> _` (drule_then ACCEPT_TAC)) >>
  conj_tac >- suspend "maps_final_types" >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume grouped_default_normal_bound_entry[maps_final_types]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_assum `!n. _ ==> ?p sz. FLOOKUP ce.ce_vars n = _` irule >>
      qpat_assum `MEM (id,ty) args` mp_tac >>
      qpat_assum `pos ++ kw = args` (SUBST1_TAC o SYM) >>
      pure_rewrite_tac[MEM_APPEND] >> strip_tac
      >- (disj1_tac >> qpat_assum `!id ty. MEM (id,ty) pos ==> _`
            (drule_then strip_assume_tac) >> metis_tac[]) >>
      disj2_tac >> qpat_assum `!id. MEM id (MAP FST kw) ==> _` irule >>
      pure_rewrite_tac[MEM_MAP] >> qexists_tac `(id,ty)` >> simp[]) >>
  `supported_function_body tops External args ss` by
    (drule_all supportedGetterPropsTheory.supported_selected_external_body >> simp[]) >>
  Cases_on `compile_register_positional_args ce0 pa 4 entry` >>
  drule_all external_entry_target_param_type >>
  qpat_assum `compile_register_positional_args ce0 pa 4 entry = _`
    (strip_assume_tac o MATCH_MP (SPEC_ALL compile_register_positional_args_cenv)) >>
  `q.ce_var_type = ce0.ce_var_type` by
    (qpat_assum `q = ce0 with ce_vars := _` SUBST1_TAC >> simp[]) >>
  `ce.ce_var_type = ce0.ce_var_type` by
    (qpat_assum `ce with ce_vars := ce0.ce_vars = ce0` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[]
QED

Resume grouped_default_normal_bound_entry[register]:
  `cekw.ce_struct_fields = ce0.ce_struct_fields /\ cekw.ce_flag_n_members = ce0.ce_flag_n_members` by
    (qpat_assum `cekw with ce_vars := ce0.ce_vars = ce0` (SUBST1_TAC o SYM) >> simp[]) >>
  `common.ec_pos_args = build_positional_args cekw pos` by
    (qpat_assum `common.ec_pos_args = _` SUBST1_TAC >>
     simp[build_positional_args_def,MAP_EQ_f,pairTheory.FORALL_PROD,build_positional_arg_def,
          type_to_abi_dec_info_layout_cong]) >>
  `compile_register_positional_args cekw (build_positional_args cekw pos) 4 entry = (ce,sa)` by
    (qpat_assum `common.ec_pos_args = build_positional_args cekw pos` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\ ce.ce_return_buf = NONE` by
    (drule targeted_external_package_layout >>
     qpat_assum `ce with ce_vars := ce0.ce_vars = ce0` (SUBST1_TAC o SYM) >> simp[]) >>
  `ce.ce_return_pc = NONE` by (drule_all external_package_body_inv >> simp[]) >>
  `LENGTH kw = LENGTH kwtvs /\ LENGTH kw = LENGTH kwvals /\ LENGTH pos = LENGTH pvals` by
    (qpat_assum `MAP _ vars = kw` (SUBST1_TAC o SYM) >>
     imp_res_tac LIST_REL_LENGTH >> simp[]) >>
  `calldata_decode_args landed.vs_call_ctx.cc_calldata ptvs 0 = SOME pvals /\
   fresh_vars_wrt sa landed` by
    (unabbrev_all_tac >> simp[jump_to_def,fresh_vars_wrt_def,lookup_var_def] >>
     fs[fresh_vars_wrt_def,lookup_var_def]) >>
  suspend "register_invoke"
QED

Resume grouped_default_normal_bound_entry[register_invoke]:
  `(ctx_has_dalloca ctx ==> allocas_below_fmp landed /\
    landed.vs_alloca_next + pending_alloca_size fn landed <= w2n landed.vs_initial_fmp)` by
    (strip_tac >> conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ _ landed`
           (mp_tac o MATCH_MP (SPEC_ALL stmt_state_rel_allocas_below_fmp)) >> simp[]) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ landed` (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     qpat_assum `fmp_room ctx fn landed` (mp_tac o REWRITE_RULE [fmp_room_def]) >>
     simp[] >> decide_tac) >>
  `!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE` by
    (gen_tac >> strip_tac >> Cases_on `FLOOKUP ce.ce_vars k` >> simp[] >>
     qpat_assum `!id loc. FLOOKUP ce.ce_vars id = SOME loc ==> _` (drule_then mp_tac) >> simp[]) >>
  `!c arg tv. MEM (arg,tv) (ZIP (args,ptvs ++ kwtvs)) /\ c = cekw with ce_vars := c.ce_vars ==>
    selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
    abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv` by
    (rpt gen_tac >> strip_tac >>
     `c = ce0 with ce_vars := c.ce_vars` by
       fs[compile_env_component_equality] >>
     qpat_assum `!c arg tv. _ /\ c = ce0 with ce_vars := c.ce_vars ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  qpat_assum `pos ++ kw = args` (fn eq =>
    drule_all_then (qx_choosel_then [`t`,`G`,`tn`] (map_every assume_tac o CONJUNCTS))
      (REWRITE_RULE [eq] (Q.INST [`PG` |-> `[]`] grouped_register_body_arguments))) >>
  suspend "endpoint"
QED

Resume grouped_default_normal_bound_entry[endpoint]:
  `!D. gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,FEMPTY,entry_taint) marks (OK t,G,tn)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ _ marks (OK u,J,tz)` (qspec_then `D` assume_tac) >>
     qpat_assum `!D exp. gas_origin_ptr_path _ (u,J,tz) [] _`
       (qspecl_then [`D`,`explicit`] assume_tac) >>
     qpat_assum `!D exp. gas_origin_ptr_path _ (landed,J,tz) [] _`
       (qspecl_then [`D`,`explicit`] assume_tac) >>
     ntac 3 (pop_assum mp_tac) >> rpt (pop_assum kall_tac) >>
     metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  `~block_is_terminated entry` by simp[block_is_terminated_def] >>
  `~block_is_terminated sa` by drule_all_then ACCEPT_TAC compile_register_positional_args_open >>
  `MEM fn ctx.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `key = global_nonreentrant_slot /\ ut = T /\ view = (mut = View) /\
   rt = (if ret = NoneT then NONE else SOME ret)` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [LET_THM,package_external_fn_def,set_external_package_target_def]) >>
  qabbrev_tac `es = ee with <|scopes := [envb];gas_obs := []|>` >>
  `es.gas_obs = [] /\ storage_trace_domain cx (initial_state am []) es.storage_trace` by
    simp[Abbr `es`,storage_trace_domain_def,storage_trace_horizon_def,
         storage_trace_regions_def,storage_trace_locks_def,grouped_default_empty_regions_horizon] >>
  `!gx. external_entry_bound tops am tx vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ gx) mut args dflts (es with gas_obs := gx)` by
    (qunabbrev_tac `es` >>
     simp_tac (srw_ss()) [evaluation_state_fupdfupds] >> first_assum ACCEPT_TAC) >>
  `compile_guarded_body ce nr global_nonreentrant_slot T (mut = View) ss
     (if ret = NoneT then NONE else SOME ret) sa = ((),final) /\
   compile_guarded_body (gas_shadow_env T ce) nr global_nonreentrant_slot T (mut = View)
     (MAP gas_shadow_stmt ss)
     (if ret = NoneT then NONE else SOME ret) shadow_sa = ((),shadow_final)` by
    (qpat_assum `compile_guarded_body _ _ _ _ _ _ _ sa = _` mp_tac >>
     qpat_assum `compile_guarded_body _ _ _ _ _ _ _ shadow_sa = _` mp_tac >> fs[]) >>
  `nr ==> fresh_vars_wrt sa t` by (strip_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `es` >>
  qpat_x_assum `ctx = unit.cu_context` SUBST_ALL_TAC >>
  qpat_x_assum `explicit = _` SUBST_ALL_TAC >>
  irule grouped_registered_body_endpoint >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac `fbody` >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`bb`,`ce`,`ce0`,`cx`,`final`,`fn`,`pay`,`view`,`lbl`,
    `marks`,`mc`,`key`,`pa`,`rt`,`s`,`sa`,`shadow_final`,`shadow_fn`,
    `shadow_sa`,`shadow_unit`,`t`,`tn`,`ut`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise grouped_default_normal_bound_entry
