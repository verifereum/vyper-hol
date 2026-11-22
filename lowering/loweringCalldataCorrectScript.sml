(* S1 and S3 for arbitrary calldata, with joint entry-run certificates. *)
Theory loweringCalldataCorrect
Ancestors
  e2eDefs vyperLoweringCorrect loweringMemCorrect sourceUnitExecution sourceUnitExitSafe
  ptrDiscipline vyperCalldata dispatchedCallAssembly dispatchedSelectedEndpoint
  gasShadowRunLowering loweringShapeProps calldataNoneEntryController calldataNoneDecoder
  acceptedContextPhi entryJointRevertExit compileVyper fragGasOriginPtr entryDispatchPtr
  loweringRuntimeCorrect supportedProgram entryDispatchProps publicGetterProps
  vyperTypeContractContext nonreentrantEntryEquiv vyperReadOnlySyntax vyperTypeContractGetter
  vyperTypeContract list fragGasPathPtr pred_set venomInst venomState
  callDynamicMemory[qualified,ignore_grammar] o1PassContract lowerDloadDefs
  callRejectMemory[ignore_grammar] bodyPtrDefs contextRawReachable venomExecProofs
  selectedAcceptedFold compileEnv vyperContext vyperCompiler finite_map rich_list words
  vyperInterpreter[qualified,ignore_grammar] constSubst[qualified,ignore_grammar] pair
  arithmetic relation vyperAST vyperTypeBuiltins groupedRejectDispatch
  groupedRejectOmittedArguments groupedRejectReplay venomExecSemantics allocaFrontierBound
  moduleLowering vyperStorageFootprint

val _ = Parse.hide "tops";

(* The call a contract makes of raw calldata: the external entry it
   dispatches to and the arguments it decodes (vyperCalldata), including the
   __default__ fallback and noncanonical encodings. *)
Definition dispatched_vyper_call_def:
  dispatched_vyper_call tops tx calldata ret <=>
    calldata_dispatch tops calldata = SOME (tx.function_name, tx.args) /\
    ?mut nr args dflts body.
      vyperInterpreter$lookup_function NONE tx.function_name External tops =
        SOME (mut, nr, args, dflts, ret, body)
End

(* The legacy dispatcher exposes only empty default lists. The checker
   rules out parameters and therefore defaults on the fallback. *)
Triviality selected_legacy_defaults_nil[local]:
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  source_typing_ok tops am tx /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  dflts = []
Proof
  strip_tac >> Cases_on `name = "__default__"`
  >- (gvs[] >> drule lookup_function_External_cases >> strip_tac
      >- (`function_header_ok External mut nr raw "__default__" args dflts ret`
            by metis_tac[source_typing_function_header] >>
          drule supportedNamesTheory.supported_fallback_no_arguments >> strip_tac >>
          gvs[source_typing_ok_def] >>
          `module_allocated am.layouts tx.target NONE tops` by
            (drule check_contract_main_module_allocated >> simp[]) >>
          `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
             External mut nr [] dflts ret fbody` by
            (irule check_contract_runtime_function_body_MEM >>
             simp[] >> qexistsl_tac [`"__default__"`, `raw`] >> simp[]) >>
          fs[check_function_body_def]) >>
      metis_tac[external_getter_defaults]) >>
  drule_all lookup_function_external_member >> strip_tac >>
  qpat_x_assum `~EXISTS external_has_defaults _` mp_tac >>
  simp[EVERY_MEM] >> disch_then
    (qspec_then `subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,dflts,ret,fbody)` mp_tac) >>
  Cases_on `dflts` >>
  simp[constSubstTheory.subst_consts_fn_def, external_has_defaults_def,
       constSubstTheory.subst_consts_expr_def]
QED

Triviality runtime_dispatched_readings_certificate[local]:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops ==>
    ?shadow_unit. !am tx ret vs.
      source_typing_ok tops am tx /\
      source_deployment_rel tops am tx /\
      dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
      initial_venom_state_rel tops am tx vs /\
      outcomes_accounts_typed (SOME vs.vs_outcomes) /\
      (ctx_has_dalloca unit.cu_context ==>
        !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
          dalloca_no_wrap inst s) /\
      (ctx_has_dalloca unit.cu_context ==>
        unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
        w2n vs.vs_initial_fmp < 2 ** 254) ==>
      ?marks.
        source_unit_execution_correct_with shadow_unit.cu_context marks
          tops ret am tx unit vs /\
        ((?tail. call_storage_ok am tx vs.vs_outcomes
           (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
         !tail. FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
           INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `EXISTS external_has_defaults (FST (classify_functions tops))`
  >- (drule_all runtime_body_grouped_default_readings >>
      disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
      qexists_tac `shadow_unit` >> rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
      fs[dispatched_vyper_call_def] >> metis_tac[]) >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
                gas_shadow_unit unit shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     irule runtime_gas_shadow_unit_exists >> fs[]) >>
  pop_assum strip_assume_tac >>
  qexists_tac `shadow_unit` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `dispatched_vyper_call _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dispatched_vyper_call_def]) >>
  drule_all_then SUBST_ALL_TAC selected_legacy_defaults_nil >>
  drule_all dispatched_call_correct_with_readings >> simp[]
QED

Theorem lower_vyper_runtime_unit_correct_dispatched_readings_available:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_no_wrap inst s)
    ==>

    ?marks.
      source_unit_execution_correct_at marks tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_dispatched_readings_certificate >>
  disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
  first_x_assum (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
  qpat_assum `ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_no_wrap inst s` (fn th => rewrite_tac[th]) >>
  simp[] >> strip_tac >> qexists_tac `marks` >>
  metis_tac[source_unit_execution_correct_at_def]
QED

(* The shadow context is fixed by the program before choosing a call. *)
Theorem lower_vyper_runtime_unit_correct_dispatched_with:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops ==>
    ?shadow_ctx. !am tx ret vs.
      source_typing_ok tops am tx /\
      source_deployment_rel tops am tx /\
      dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
      LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
      initial_venom_state_rel tops am tx vs /\
      outcomes_accounts_typed (SOME vs.vs_outcomes) /\
      LENGTH vs.vs_outcomes < 2 ** 64 /\
      vs.vs_fmp = vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254 /\
      unit_alloca_budget unit.cu_context +
        32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp ==>
      ?marks.
        source_unit_execution_correct_with shadow_ctx marks
          tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_dispatched_readings_certificate >>
  disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
  qexists_tac `shadow_unit.cu_context` >> rpt gen_tac >> strip_tac >>
  `raw_variant vs.vs_initial_fmp vs vs` by
    simp[raw_variant_def, gas_variant_def, venomStateTheory.venom_state_component_equality] >>
  `!fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_no_wrap inst s` by
    (qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `vs.vs_initial_fmp`, `vs`]
       mp_tac callDynamicMemoryTheory.call_raw_variant_no_wrap >>
     impl_tac >- simp[] >> metis_tac[]) >>
  `(ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_no_wrap inst s)` by (strip_tac >> first_assum ACCEPT_TAC) >>
  `(ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254)` by (strip_tac >> conj_tac >> decide_tac) >>
  qpat_assum `!am tx ret vs. _ ==> ?marks. _`
    (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks` >> first_assum ACCEPT_TAC
QED

(* S1, calldata that dispatches to nothing: no fallback, a short head, or a
   failed decode.  The entry reverts with empty returndata before any
   function body runs. *)
Theorem lower_vyper_runtime_unit_reverts_legacy[local]:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254)
    ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> strip_tac >>
  drule none_entry_reject_from_decoder >>
  disch_then (drule_at (Pat `source_typing_ok _ _ _`)) >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `!bb. venomInst$lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all lower_vyper_runtime_unit_block_phi >> simp[]) >>
  drule (BETA_RULE none_coherent_decode_paths) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) o
    Q.INST [`limit` |-> `last`, `lo` |-> `0`, `PG` |-> `[]`] o SPEC_ALL) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  (impl_tac >-
    (simp[allocas_from_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!id. first.cs_next_id <= id ==> _`
       (drule_then (fs o single)))) >>
  metis_tac[]
QED

Theorem grouped_runtime_unit_reject_origin:
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`tops`,`rpolicy`,`unit`,`am`,`tx`,`vs`]
    row22_reject_from_dispatch_callback) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then irule >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`] (SPEC_ALL row22_dispatch_callback_if_seed)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then irule >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  (* Recover the model start from the actual selected and supplied prefix. *)
  `selected_registration_frame vs entry_taint u tn` by
    (qpat_assum `selected_registration_frame start _ a _` mp_tac >>
     qpat_assum `selected_registration_frame a _ u _` mp_tac >>
     qpat_assum `start = _` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     simp[selected_registration_frame_def, venom_state_accfupds] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `common.ec_payable \/ vs.vs_call_ctx.cc_callvalue = 0w` assume_tac >-
    (qpat_assum `common.ec_payable \/ _` mp_tac >>
     qpat_assum `start = _` SUBST1_TAC >> simp[NoAsms, venom_state_accfupds])) >>
  `gas_origin_ptr_path (ARB,0,EMPTY,unit.cu_context,fn,[])
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
      FEMPTY,entry_taint) [] (OK u,G,tn)` by
    (qpat_assum `start = _` (SUBST1_TAC o SYM) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (start,_,_) [] (OK a,Ga,ta)`
       (qspecl_then [`ARB`,`EMPTY`]
         (irule o REWRITE_RULE [APPEND] o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[NoAsms] >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (a,Ga,ta) [] (OK u,G,tn)`
       (qspecl_then [`ARB`,`EMPTY`] ACCEPT_TAC)) >>
  `!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (`ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
       (drule lower_vyper_runtime_unit_context_entry >>
        disch_then (mp_tac o MATCH_MP lowering_context_ok_bridge o CONJUNCT1) >>
        simp[NoAsms, EVERY_MEM, fn_labels_def] >> metis_tac[lookup_function_MEM]) >>
     metis_tac[MEM_lookup_block]) >>
  `(ctx_has_dalloca unit.cu_context ==> allocas_below_fmp u /\
     unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
     w2n vs.vs_initial_fmp < 2 ** 254)` by
    (strip_tac >> qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp u /\ _` drule >>
     qpat_assum `ctx_has_dalloca _ ==> vs.vs_fmp = _ /\ _` drule >> simp[]) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `ds` |-> `defaults`, `fbody` |-> `stmts`,
    `ce` |-> `common.ec_env`, `ctx` |-> `unit.cu_context`, `shfn` |-> `shadow_fn`,
    `sa` |-> `residual`, `supplied` |-> `TAKE k slots`, `slots` |-> `DROP k slots`,
    `site` |-> `ARB`, `D` |-> `ARB`, `explicit` |-> `EMPTY`] row22_omitted_model_inputs) >>
  (impl_tac >- (simp_tac bool_ss [] >> rpt (first_assum (ACCEPT_TAC o BETA_RULE) ORELSE conj_tac))) >>
  disch_then (qx_choosel_then [`art`,`es`,`init_cx`,`init_env`,`seed`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `init_cx = _` SUBST_ALL_TAC >>
  qpat_x_assum `init_env = _` SUBST_ALL_TAC >>
  qpat_x_assum `seed = _` SUBST_ALL_TAC >>
  (* The seed uses the omitted slots and preserves the supplied slots. *)
  qabbrev_tac `kept = MAP (\((aid,p,base,tv),v). (aid,p,base,tv,v)) (ZIP (TAKE k slots,vals))` >>
  `MAP FST kept = TAKE k (MAP FST slots)` by
    (`LENGTH (TAKE k slots) = LENGTH vals` by
       (qpat_assum `LIST_REL _ (TAKE k slots) vals` (ACCEPT_TAC o MATCH_MP LIST_REL_LENGTH)) >>
     simp[Abbr `kept`, GSYM MAP_TAKE, LIST_EQ_REWRITE, LENGTH_ZIP, EL_MAP, EL_ZIP] >>
     rpt strip_tac >> qabbrev_tac `slot = EL x (TAKE k slots)` >> PairCases_on `slot` >> simp[]) >>
  `ALL_DISTINCT (MAP FST (DROP k slots) ++ MAP FST kept)` by
    (simp[MAP_DROP] >>
     qpat_assum `ALL_DISTINCT (MAP FST slots)` mp_tac >>
     CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM (Q.SPECL [`k`,`MAP FST slots`] TAKE_DROP)])) >>
     simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts (tx with function_name := name) NONE` >>
  qabbrev_tac `env = artifact_env art [(NONE,tops)] NONE` >>
  qpat_assum `compile_init_kwargs _ (DROP _ _) _ 0 _ residual = _`
    (mp_then (Pos hd) (drule_at (Pat `check_contract F _ _ _ = SOME _`))
      (BETA_RULE (Q.INST [`DF` |-> `\H. cx_dead H cx`] row22_omitted_seed_path))) >>
  disch_then irule >>
  rpt (first_assum (ACCEPT_TAC o BETA_RULE) ORELSE conj_tac) >>
  qexistsl_tac [`cx`,`env`,`es`,`kept`,`shadow_residual`,`shadow_unit.cu_context`,
    `shadow_cut`,`shadow_fn`,`DROP k slots`,`initial_state am []`,`tops`] >>
  rpt (first_assum (ACCEPT_TAC o BETA_RULE) ORELSE conj_tac) >>
  simp[dead_lo_ok_def]
QED

Theorem lower_vyper_runtime_unit_reverts:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254)
    ==>
    ?func s G' tn' n.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) n (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) n G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> strip_tac >>
  `vs.vs_fmp = vs.vs_initial_fmp` by fs[initial_venom_state_rel_def] >>
  Cases_on `EXISTS external_has_defaults (FST (classify_functions tops))`
  >- (qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`] mp_tac
        grouped_runtime_unit_reject_origin >>
      impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
      disch_then (qx_choosel_then [`func`, `s`, `G'`, `tn'`, `marks`] strip_assume_tac) >>
      qspecl_then [`unit.cu_context`, `func`, `vs`, `s`, `G'`, `tn'`, `marks`]
        mp_tac entry_joint_revert_exit >>
      impl_tac >- asm_rewrite_tac[] >> strip_tac >>
      qexistsl [`func`, `s`, `G'`, `tn'`, `LENGTH marks`] >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`] mp_tac
    lower_vyper_runtime_unit_reverts_legacy >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`func`, `s`, `G'`, `tn'`] strip_assume_tac) >>
  qexistsl [`func`, `s`, `G'`, `tn'`, `0`] >> asm_rewrite_tac[] >> metis_tac[]
QED

(* S3 at the marks of S1's certificate (lower_vyper_runtime_unit_correct_dispatched_with),
   where the storage guards hold and the source call is not exempt: its exit
   arm gives the memory-safe run from the entry and, at every valid horizon,
   the pointer-safe run at that horizon's dead set. *)
Theorem lower_vyper_runtime_unit_memory_ok_dispatched:
  !marks tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx)
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        !H. valid_horizon
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am []) H
              (source_storage_trace am tx vs.vs_outcomes
                 (gas_explicit marks vs.vs_gas_readings)) ==>
            taint_within
              (cx_dead H
                 (initial_evaluation_context am.sources am.layouts tx NONE))
              unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all source_unit_exit_safe_runs >> strip_tac >>
  qspecl_then [`marks`, `tops`, `ret`, `am`, `tx`, `unit`, `vs`, `func`]
    mp_tac source_unit_exit_ptr_safe_horizons >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
  simp[] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  drule_all lower_vyper_runtime_unit_memory_ok >> simp[]
QED
