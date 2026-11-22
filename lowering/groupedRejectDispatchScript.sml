(* Compose the selected grouped reject path with runtime dispatch. *)
Theory groupedRejectDispatch
Ancestors
  e2eDefs vyperLoweringCorrect ptrDiscipline acceptedContextPhi fragGasOriginPtr list pred_set
  venomInst venomState callRejectMemory[ignore_grammar] groupedEntryPackage selectedAcceptedFold
  groupedDefaultArguments
  abiDecoderCoherence compileEnv vyperContext vyperABIEntries entryRejectCode finite_map
  rich_list words pair arithmetic relation vyperAST groupedRejectCutRegistration
  groupedRejectReplay groupedRejectSelection groupedRejectSuppliedArguments vyperCalldata
  gasShadowRunLowering compileVyper supportedProgram fragExec venomExecSemantics bodyPtrDefs
  exprLoweringProps moduleLowering gasShadowState gasShadow vyperCompiler fragFuel
  loweringStateRelDefs vyperInterpreter[qualified,ignore_grammar]
  vyperValue[qualified,ignore_grammar]
Libs
  groupedRejectSlotsLib

val _ = Parse.hide "tops";

Theorem row22_reject_from_dispatch_callback:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    EXISTS external_has_defaults (FST (classify_functions tops)) /\
    (ctx_has_dalloca unit.cu_context ==>
      vs.vs_fmp = vs.vs_initial_fmp /\
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) ==>
    (!mut nr rr name args defaults ret stmts prefix k tvs.
      4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
      MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) /\
      defaults <> [] /\ MEM (prefix,k) (abi_entries args defaults) /\
      abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector vs.vs_call_ctx.cc_calldata /\
      OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME tvs /\
      4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
      calldata_decode_args vs.vs_call_ctx.cc_calldata
        (TAKE (LENGTH args - LENGTH defaults) tvs) 0 = NONE /\
      calldata_decode_args vs.vs_call_ctx.cc_calldata
        (DROP (LENGTH args - LENGTH defaults) tvs)
        (SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) tvs))) <> NONE ==>
      ?fn z H tn marks.
        venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
        z.vs_returndata = [] /\
        !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
           FEMPTY,entry_taint) marks (Abort Revert_abort z,H,tn)) ==>
    ?func s G' tn' marks.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      entry_prov func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>) FEMPTY = FEMPTY /\
      entry_taint_vars func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>) entry_taint = entry_taint /\
      (!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,func,[])
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>,FEMPTY,entry_taint)
        marks (Abort Revert_abort s,G',tn'))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> disch_tac >>
  `unit.cu_context.ctx_entry = SOME "__entry"` by
    (drule lower_vyper_runtime_unit_context_entry >> simp[]) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `u` |-> `unit`]
    (SPEC_ALL callRejectMemoryTheory.grouped_runtime_unit_reject_dispatch_origin)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  disch_then (qx_choosel_then [`fn`,`z`,`H`,`tn`,`marks`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all entryRejectCodeTheory.lower_vyper_runtime_unit_entry_label >> simp[]) >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                                vs_inst_idx := 0|>` >>
  `entry_prov fn start FEMPTY = FEMPTY /\
   entry_taint_vars fn start entry_taint = entry_taint` by
    (Cases_on `lookup_block start.vs_current_bb fn.fn_blocks`
     >- simp[entry_prov_def, entry_taint_vars_def] >>
     irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     goal_assum (drule_at Any) >>
     drule_all acceptedContextPhiTheory.lower_vyper_runtime_unit_block_phi >> simp[]) >>
  qexistsl_tac [`fn`,`z`,`H`,`tn`,`marks`] >> simp[]
QED

Theorem row22_dispatch_callback_if_seed:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  initial_venom_state_rel tops am tx vs /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  (ctx_has_dalloca unit.cu_context ==>
    vs.vs_fmp = vs.vs_initial_fmp /\
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) /\
  defaults <> [] /\ MEM (prefix,k) (abi_entries args defaults) /\
  abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector vs.vs_call_ctx.cc_calldata /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  calldata_decode_args vs.vs_call_ctx.cc_calldata
    (TAKE (LENGTH args - LENGTH defaults) tvs) 0 = NONE /\
  calldata_decode_args vs.vs_call_ctx.cc_calldata
    (DROP (LENGTH args - LENGTH defaults) tvs)
    (SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) tvs))) <> NONE ==>
  (!start fn shadow_unit shadow_fn common entries specs off all_tvs
    vars alloc_start alloc_end checks si cut last dispatch_end shadow_si shadow_cut
    v Gv tnv a Ga ta entry cef registered residual shadow_residual u G tn slots vals.
    start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    runtime_gas_shadow_unit tops rp = SOME shadow_unit /\ gas_shadow_unit unit shadow_unit /\
    lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shadow_fn /\
    gas_shadow_function fn shadow_fn /\
    package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
      (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off /\
    ALL_DISTINCT (MAP FST args) /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME all_tvs /\
    LIST_REL (\(n,ty) tv.
      abi_decoder_coherent common.ec_env (type_env tops) common.ec_env.ce_struct_fields ty tv /\
      (?loc. FLOOKUP common.ec_env.ce_vars n = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args all_tvs /\
    prefix = TAKE (LENGTH args - LENGTH defaults + k) args /\
    tvs = TAKE (LENGTH args - LENGTH defaults + k) all_tvs /\
    4 + SUM (MAP tv_abi_size all_tvs) < dimword (:256) /\
    4 + SUM (MAP tv_abi_size tvs) = min_calldata_size common.ec_env prefix 0 /\
    off = 4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) all_tvs)) /\
    specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH defaults) args,defaults)) /\
    common.ec_pos_args = build_positional_args common.ec_env (TAKE (LENGTH args - LENGTH defaults) args) /\
    (common.ec_payable \/ start.vs_call_ctx.cc_callvalue = 0w) /\
    compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end) /\
    checks.cs_current_bb = external_prefix_label name k /\ checks.cs_current_insts = [] /\
    compile_entry_checks (min_calldata_size common.ec_env prefix 0) common.ec_payable checks = ((),si) /\
    fn_has_code checks si fn /\
    compile_init_kwargs common.ec_env vars off k (Lit 0w) si = ((),cut) /\
    fn_has_code si cut fn /\ fn_has_code cut last fn /\
    emit_inst JMP [Label common.ec_common_label] [] cut = ((),last) /\
    ci_mono last dispatch_end /\
    compile_init_kwargs (gas_shadow_env T common.ec_env)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off k (Lit 0w) shadow_si = ((),shadow_cut) /\
    fn_has_code shadow_si shadow_cut shadow_fn /\ gas_shadow_state si shadow_si /\
    selected_registration_resources unit.cu_context fn ARB 0 checks v /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (v,Gv,tnv) [] (OK a,Ga,ta)) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK v,Gv,tnv)) /\
    selected_registration_resources unit.cu_context fn ARB 0 si a /\
    selected_registration_frame start entry_taint a ta /\ a.vs_memory = start.vs_memory /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base. op = Var q /\ not_fresh_at si q /\ lookup_var q a = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q]) (fn_insts fn) /\
        FLOOKUP a.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        id < si.cs_next_id /\ base + type_memory_bytes common.ec_env ty < dimword (:256) /\
        ptr_covers Ga ta q a (type_memory_bytes common.ec_env ty)) /\
    (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp a /\
      a.vs_alloca_next + pending_alloca_size fn a <= w2n a.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK a,Ga,ta)) /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget unit.cu_context < dimword (:256) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
    ci_mono cut entry /\ entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
    compile_register_positional_args (compile_register_kwarg_vars common.ec_env vars)
      common.ec_pos_args 4 entry = (cef,registered) /\ fn_has_code entry registered fn /\
    compile_init_kwargs common.ec_env (DROP k vars) (4 + SUM (MAP tv_abi_size tvs)) 0
      (Lit 0w) residual = ((),cut) /\
    compile_init_kwargs (gas_shadow_env T common.ec_env)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) (DROP k vars))
      (4 + SUM (MAP tv_abi_size tvs)) 0 (Lit 0w) shadow_residual = ((),shadow_cut) /\
    fn_has_code residual cut fn /\ fn_has_code shadow_residual shadow_cut shadow_fn /\
    gas_shadow_state residual shadow_residual /\
    selected_registration_resources unit.cu_context fn ARB 0 residual u /\
    (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp u /\
      u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp) /\
    EVERY (^row22_kw_alloc residual u G tn) (DROP k slots) /\
    LIST_REL (\(aid,p,base,tv) v. ^row22_kw_initialized residual u G tn (aid,p,base,tv,v))
      (TAKE k slots) vals /\
    calldata_decode_args a.vs_call_ctx.cc_calldata (DROP (LENGTH args - LENGTH defaults) tvs)
      (SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH defaults) tvs))) = SOME vals /\
    ALL_DISTINCT (MAP FST slots) /\
    LIST_REL (^row22_kw_meta common.ec_env (type_env tops)) (DROP k vars) (DROP k slots) /\
    MAP (\(_,_,_,tv). tv) slots = DROP (LENGTH args - LENGTH defaults) all_tvs /\
    MAP (\(_,_,_,e). e) (DROP k vars) = DROP k defaults /\
    selected_registration_frame a ta u tn /\ tn.t_mem SUBSET ta.t_mem /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[]) (a,Ga,ta) [] (OK u,G,tn)) ==>
    ?D explicit marks r H tz.
      gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[]) (u with vs_outcomes := [],G,tn)
        marks (r,H,tz) /\ (!t. r = OK t ==> at_point cut t)) ==>
  ?fn z H tn marks.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,FEMPTY,entry_taint)
      marks (Abort Revert_abort z,H,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_then assume_tac >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` by simp[Abbr `start`] >>
  `ctx_has_dalloca unit.cu_context ==> unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp` by
    (strip_tac >> qpat_assum `ctx_has_dalloca _ ==> _` (drule_then (ACCEPT_TAC o cj 2))) >>
  drule_all row22_selected_start_with_cut >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`fn`,`z`,`H`,`tn`] (map_every assume_tac o CONJUNCTS))
    (qx_choosel_then [`fn`,`shadow_unit`,`shadow_fn`,`common`,`entries`,`specs`,`off`,`all_tvs`,
      `vars`,`alloc_start`,`alloc_end`,`checks`,`si`,`cut`,`last`,`dispatch_end`,`shadow_si`,`shadow_cut`,
      `v`,`Gv`,`tnv`,`a`,`Ga`,`ta`,`entry`,`cef`,`registered`] (map_every assume_tac o CONJUNCTS)))
  >- (qexistsl_tac [`fn`,`z`,`H`,`tn`,`[]`] >> asm_rewrite_tac[]) >>
  (* Advance the real selected run through the supplied keywords. *)
  `a.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `selected_registration_frame start _ a _`
       (mp_tac o cj 1 o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `start = _` SUBST1_TAC >> simp[NoAsms]) >>
  `LENGTH defaults <= LENGTH args` by
    (qpat_assum `source_typing_ok _ _ _` (strip_assume_tac o REWRITE_RULE [source_typing_ok_def]) >>
     drule_all checked_grouped_defaults_length >> simp[]) >>
  `k <= LENGTH defaults` by
    (qpat_assum `MEM (prefix,k) (abi_entries args defaults)` mp_tac >> simp[NoAsms, abi_entries_member]) >>
  `LENGTH a.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all entryValueRevertPtrTheory.initial_entry_dispatch_scalars >> simp[]) >>
  `LIST_REL (\(name,ty) tv.
     abi_decoder_coherent common.ec_env (type_env tops) common.ec_env.ce_struct_fields ty tv) args all_tvs` by
    (qpat_assum `LIST_REL _ args all_tvs` mp_tac >> ho_match_mp_tac LIST_REL_mono >> Cases >> simp[]) >>
  `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env
    (type_env tops) common.ec_env.ce_struct_fields (SND arg) tv) args all_tvs` by
    (qpat_assum `LIST_REL (\(name,ty) tv. abi_decoder_coherent _ _ _ ty tv) args all_tvs`
       mp_tac >> ho_match_mp_tac LIST_REL_mono >> Cases >> simp[]) >>
  `off = min_calldata_size common.ec_env (TAKE (LENGTH args - LENGTH defaults) args) 0` by
    (qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args all_tvs`
       (mp_tac o SYM o Q.INST [`n` |-> `LENGTH (args:argument list) - LENGTH (defaults:expr list)`] o
        MATCH_MP grouped_argument_min_calldata_size) >> simp[]) >>
  `4 + SUM (MAP tv_abi_size tvs) <= LENGTH a.vs_call_ctx.cc_calldata` by
    (qpat_assum `a.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `n = LENGTH args - LENGTH defaults` >>
  `calldata_decode_args a.vs_call_ctx.cc_calldata (DROP n tvs)
      (SUM (MAP tv_abi_size (TAKE n tvs))) <> NONE` by
    (qpat_assum `a.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `n = LENGTH args - LENGTH defaults` by
    (qpat_assum `Abbrev (n = _)` (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  `!name op ty e. MEM (name,op,ty,e) vars ==>
    ?id q b. op = Var q /\ not_fresh_at si q /\ lookup_var q a = SOME (n2w b) /\
      MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q]) (fn_insts fn) /\
      FLOOKUP a.vs_allocas id = SOME (b,type_memory_bytes common.ec_env ty) /\
      b + type_memory_bytes common.ec_env ty < dimword (:256) /\ id < si.cs_next_id /\
      ptr_covers Ga ta q a (type_memory_bytes common.ec_env ty)` by
    (qpat_assum `!name op ty e. MEM (name,op,ty,e) vars ==> _` mp_tac >>
     simp[NoAsms, AC CONJ_ASSOC CONJ_COMM]) >>
  drule_all row22_supplied_suffix_start >>
  disch_then (qx_choosel_then [`residual`,`shadow_residual`,`u`,`G`,`tn`,`slots`,`vals`]
    (map_every assume_tac o CONJUNCTS)) >>
  (* Use the selected and supplied witnesses together: in particular the
     residual state and both its ghosts must be those of the real fold. *)
  qpat_x_assum `!start fn shadow_unit shadow_fn common. _`
    (qspecl_then [`start`,`fn`,`shadow_unit`,`shadow_fn`,`common`,`entries`,`specs`,`off`,
      `all_tvs`,`vars`,`alloc_start`,`alloc_end`,`checks`,`si`,`cut`,`last`,`dispatch_end`,
      `shadow_si`,`shadow_cut`,`v`,`Gv`,`tnv`,`a`,`Ga`,`ta`,`entry`,`cef`,`registered`,
      `residual`,`shadow_residual`,`u`,`G`,`tn`,`slots`,`vals`] mp_tac) >>
  (impl_tac >-
    (simp_tac bool_ss [] >>
     rpt (first_assum (ACCEPT_TAC o BETA_RULE) ORELSE conj_tac))) >>
  disch_then assume_tac >>
  `!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[]) (a,Ga,ta) [] (OK u,G,tn)` by
    (gen_tac >> first_assum (qspecl_then [`D`,`EMPTY`] ACCEPT_TAC)) >>
  drule_all row22_replay_initializer >>
  disch_then (DISJ_CASES_THEN
    (qx_choosel_then [`w`,`Jw`,`tw`,`marks`] (map_every assume_tac o CONJUNCTS)))
  >- (qexistsl_tac [`fn`,`w`,`Jw`,`tw`,`marks`] >> asm_rewrite_tac[] >>
      qpat_assum `start = _` (SUBST1_TAC o SYM) >> gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (start,_,_) [] (OK a,Ga,ta)`
        (qspecl_then [`D`,`EMPTY`]
           (irule o REWRITE_RULE [APPEND] o MATCH_MP gas_origin_ptr_path_append)) >>
      simp[NoAsms] >> first_assum (qspec_then `D` ACCEPT_TAC)) >>
  (* The normal replay endpoint is the first certified cut. *)
  `!D. gas_origin_ptr_path (D,0,EMPTY,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) marks (OK w,Jw,tw)` by
    (gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (start,_,_) [] (OK a,Ga,ta)`
       (qspecl_then [`D`,`EMPTY`]
          (irule o REWRITE_RULE [APPEND] o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[NoAsms] >> first_assum (qspec_then `D` ACCEPT_TAC)) >>
  `w.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `w.vs_call_ctx = a.vs_call_ctx` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `emit_inst JMP [Label entry.cs_current_bb] [] cut = ((),last)` by
    (qpat_assum `entry.cs_current_bb = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!D. gas_origin_ptr_path _ (start,_,_) marks (OK w,Jw,tw)`
    (qspec_then `ARB` assume_tac) >>
  `gas_origin_ptr_path (ARB,0,EMPTY,unit.cu_context,fn,[])
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,FEMPTY,entry_taint)
     marks (OK w,Jw,tw)` by
    (qpat_assum `start = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule_all row22_cut_registration_abort >>
  disch_then (qx_choosel_then [`z`,`Jz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`fn`,`z`,`Jz`,`tz`,`marks`] >> asm_rewrite_tac[] >>
  qpat_assum `start = _` (SUBST1_TAC o SYM) >> gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (start,_,_) marks (OK w,Jw,tw)`
    (qspec_then `D` (irule o REWRITE_RULE [APPEND_NIL] o
      Q.INST [`right` |-> `[]`] o SPEC_ALL o MATCH_MP gas_origin_ptr_path_append)) >>
  simp[]
QED
