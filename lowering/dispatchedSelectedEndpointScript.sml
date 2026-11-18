(* The selected entry registers exactly the arguments decoded from the
   incoming call, and hands their concrete and ghost states to the body. *)
Theory dispatchedSelectedEndpoint
Ancestors
  dispatchedSelectedPreparation dispatchedSelectedRelations
  selectedAcceptedDecoder selectedAcceptedSingleton selectedAcceptedFold
  defaultEntryEndpointAssembly externalEntryChecks fragGasPathFrameMem
  moduleLoweringProps venomState venomInst list words

Theorem dispatched_entry_endpoint_selected:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    tx.function_name <> "__default__" /\
    initial_venom_state_rel tops am tx vs /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dispatched_selected_registration_preparation >>
  disch_then (List.foldr (uncurry qx_choose_then) strip_assume_tac
    [`efn`,`tvs`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,
     `nkey`,`ut'`,`iv`,`rt`,`st`,`cenv`,`sa`,`st'`,`s1`,`G1`,`tn1`]) >>
  `LENGTH args = LENGTH tvs /\ LENGTH args = LENGTH tx.args` by
    fs[LIST_REL_EL_EQN] >>
  `4 + SUM (MAP tv_abi_size tvs) < dimword (:256)` by decide_tac >>
  `fresh_vars_wrt sa s1` by
    (drule compile_register_positional_args_next_var >> strip_tac >>
     irule emitHelperPropsTheory.fresh_vars_wrt_mono >> qexists `st` >> simp[]) >>
  `selected_registration_resources unit.cu_context efn ARB 0 st s1` by
    simp[selected_registration_resources_def] >>
  `alloca_history efn s1` by
    (drule_all externalEntryJointTheory.entry_path_endpoint_facts >> simp[]) >>
  `!ce j. j < LENGTH args /\ ce = cenv0 with ce_vars := ce.ce_vars ==>
    selected_slot_accepts ce (type_env tops) ce.ce_struct_fields (SND (EL j args)) (EL j tvs) /\
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields (SND (EL j args)) (EL j tvs)` by
    suspend "slot" >>
  `!j. j < LENGTH args ==> ?loc.
    FLOOKUP cenv0.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH args ==> ?off. FLOOKUP _ _ = SOME (MemLoc off _)`
       (qspec_then `j` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `off` assume_tac) >>
     qexists `MemLoc off (type_memory_size (EL j tvs))` >>
     simp[moduleLoweringTheory.var_location_memory_size_def]) >>
  `compile_register_positional_args cenv0 (build_positional_args cenv0 args) 4 st = (cenv,sa)` by
    metis_tac[] >>
  drule_at (Pat `calldata_decode_args _ _ _ = _`)
    (selected_registration_fold |> SPEC_ALL |> Q.INST
      [`PG` |-> `[]`]) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `selected_registration_resources _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
  disch_then (qspecl_then [`tn1`,`sa`,`G1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (List.foldr (uncurry qx_choose_then) strip_assume_tac [`s0`,`G0`,`tn0`]) >>
  qpat_x_assum `selected_registration_resources _ _ _ _ sa s0`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_x_assum `selected_registration_frame s1 tn1 s0 tn0`
    (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
  `!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
    (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j tx.args) p mem)` by
    suspend "owners" >>
  `tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {}` by simp[] >>
  `!H:(bool # 256 word # type_value) list # num list.
    ghost_inv_at (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
      0 NONE cenv (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0 /\
    stmt_state_rel H unit.cu_context efn cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0` by
    suspend "relations" >>
  suspend "assembly"
QED

Resume dispatched_entry_endpoint_selected[slot]:
  rpt gen_tac >> strip_tac >>
  `abi_decoder_coherent cenv0 (type_env tops) cenv0.ce_struct_fields
      (SND (EL j args)) (EL j tvs)` by
    (qpat_assum `LIST_REL (abi_decoder_coherent _ _ _) _ _`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[EL_MAP]) >>
  `abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields
      (SND (EL j args)) (EL j tvs)` by
    (qpat_assum `ce = cenv0 with ce_vars := ce.ce_vars` SUBST1_TAC >>
     simp[ctorRegisterArgsTheory.ctor_decoder_coherent_vars]) >>
  simp[] >> metis_tac[selected_register_one,selected_argument_decoder_accepts]
QED

Resume dispatched_entry_endpoint_selected[owners]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _`
    (qspec_then `j` mp_tac o REWRITE_RULE [selected_registration_owners_def]) >>
  simp[EL_MAP] >> strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid = SOME (p,n)` >>
  qexistsl [`aid`,`q`,`p`,`n`] >> simp[]
QED

Resume dispatched_entry_endpoint_selected[relations]:
  drule_all_then (MATCH_ACCEPT_TAC o
    ONCE_REWRITE_RULE [CONJ_COMM] o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_cx_dead])
    dispatched_selected_actual_endpoint_relations
QED

Resume dispatched_entry_endpoint_selected[assembly]:
  `?bb. lookup_block "__entry" efn.fn_blocks = SOME bb` by
    (Cases_on `efn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  `s0.vs_labels = vs.vs_labels` by
    (`gas_path_mem unit.cu_context efn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) 0 (OK s0)` by
       (drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]) >>
     qpat_assum `gas_path_mem _ _ (vs with <|vs_prev_bb := NONE;
           vs_current_bb := "__entry"; vs_inst_idx := 0|>) 0 (OK s0)`
       (mp_then (Pat `gas_path_mem _ _ _ 0 (OK _)`) mp_tac
           externalEntryJointTheory.entry_path_endpoint_facts) >>
     disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >> simp[]) >>
  `default_registration_entry_frame vs s0` by
    (qpat_assum `vars_pc_only _ s1`
       (strip_assume_tac o SRULE [vars_pc_only_def, venom_state_component_equality]) >>
     simp[defaultConcreteRegistrationDefsTheory.default_registration_entry_frame_def]) >>
  irule default_entry_endpoint_from_certificates >>
  conj_tac >- simp[] >>
  (* Both paths meet at (s1,G1,tn1); the body starts at (s0,G0,tn0). *)
  qexistsl [`G1`,`G0`,`bb`,`cenv0`,`cenv0`,`cenv`,`efn`,`nkey`,`lbl`,
    `min_cds`,`s0`,`pos_args`,`is_payable`,`rt`,`s1`,`sa`,`st'`,`st`,
    `tn1`,`tn0`,`ut'`,`iv`] >>
  simp[loweringPostsTheory.return_buf_frame_def]
QED

Finalise dispatched_entry_endpoint_selected
