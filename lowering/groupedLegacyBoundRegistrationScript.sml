(* Bind the source and register the machine from the same successful check. *)
Theory groupedLegacyBoundRegistration
Ancestors
  groupedRegisteredBody groupedDefaultState externalEntryBound externalEntryChecks
  selectedAcceptedFold defaultConcreteRegistrationDefs emitHelperProps fragGasOriginPtr
  entryStateRel fragExec bodyPtrDefs vyperStorageFootprint vyperCall vyperInterpreter
  vyperState vyperCalldata loweringStateRelDefs compileEnv moduleLowering ptrDiscipline
  venomExecSemantics venomState venomInst finite_map list words

Theorem grouped_legacy_bound_registration:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  initial_venom_state_rel tops am tx vs /\
  send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),ev) /\
  bind_arguments (type_env tops) args tx.args = SOME envb /\
  ALL_DISTINCT (MAP FST args) /\
  (!c arg tv. MEM (arg,tv) (ZIP (args,tvs)) /\ c = ce0 with ce_vars := c.ce_vars ==>
    selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
    abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv) /\
  EVERY (\tv. type_memory_size tv < dimword (:256)) tvs /\
  LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce0.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size tv)) args tvs /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
  compile_register_positional_args ce0 (build_positional_args ce0 args) 4 reg = (cf,sa) /\
  fn_has_code reg sa fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  calldata_decode_args u.vs_call_ctx.cc_calldata tvs 0 = SOME tx.args /\
  4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
  selected_registration_frame vs entry_taint u tn /\
  selected_registration_resources ctx fn site 0 reg u /\
  default_registration_resources ctx fn site 0 reg u (tn with t_mem := {}) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp) /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE) /\
  local_ptrs_reserved cf sa /\
  cf.ce_modules = [(NONE,tops)] /\ cf.ce_module = NONE /\ ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\
  cf.ce_return_pc = NONE /\ cf.ce_return_buf = NONE /\
  storage_vars_rel (cf with ce_vars := FEMPTY) cx /\
  transient_vars_rel (cf with ce_vars := FEMPTY) cx /\
  immutable_section_layout (cf with ce_vars := FEMPTY) tops /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (s,FEMPTY,entry_taint) [] (OK u,G,tn)) ==>
  ?es t J tz.
    (!gx. external_entry_bound tops am tx vs.vs_outcomes gx mut args [] (es with gas_obs := gx)) /\
    es.gas_obs = [] /\ storage_trace_domain cx (initial_state am []) es.storage_trace /\
    at_point sa t /\ fresh_vars_wrt sa t /\ return_buf_frame NONE cf sa t /\
    (!H:(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx fn cf cx es t /\ ghost_inv_at (cx_dead H cx) 0 NONE cf cx es J tz t) /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,FEMPTY,entry_taint) [] (OK t,J,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cx.txn = tx` by simp[initial_evaluation_context_def] >>
  `send_call_value mut cx (initial_state am [envb] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),ev with scopes := [envb])` by
    (drule send_call_value_with_scopes >>
     simp[initial_state_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!gx. external_entry_bound tops am tx vs.vs_outcomes gx mut args []
      ((ev with scopes := [envb]) with gas_obs := gx)` by
    (qpat_assum `cx = _` SUBST_ALL_TAC >> drule_all external_entry_bound_no_defaults >> simp[]) >>
  `ev.gas_obs = [] /\ ev.storage_trace = []` by
    (qpat_assum `send_call_value _ _ _ = (INL (),ev)`
       (mp_tac o MATCH_MP send_call_value_accounts) >> simp[initial_state_def]) >>
  `storage_trace_domain cx (initial_state am []) ev.storage_trace` by
    simp[storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
         storage_observations_ok_def, storage_trace_regions_def,
         storage_trace_locks_def, regions_consistent_def, storage_locks_separated_def,
         storage_well_formed_on_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def] >>
  suspend "entry_state"
QED

Resume grouped_legacy_bound_registration[entry_state]:
  `stmt_state_rel (([],[]):(bool # bytes32 # type_value) list # num list)
    ctx fn (cf with ce_vars := FEMPTY) cx ev u` by
    (mp_tac (Q.INST [`ce` |-> `cf with ce_vars := FEMPTY`, `st` |-> `reg`,
       `s` |-> `u`, `es` |-> `ev`, `D` |-> `cx_dead ([],[]) cx`, `G` |-> `G`]
       (SPEC_ALL grouped_empty_registration_state)) >>
     simp_tac (srw_ss()) [] >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> first_x_assum (qspec_then `([],[])` strip_assume_tac) >>
     qpat_assum `cx = _` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     first_assum ACCEPT_TAC) >>
  `tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {}` by
    fs[selected_registration_frame_def, entry_taint_def] >>
  `fresh_vars_wrt sa u` by
    (irule fresh_vars_wrt_mono >> qexists_tac `reg` >>
     conj_tac >- (drule compile_register_positional_args_next_var >> simp[]) >>
     fs[selected_registration_resources_def]) >>
  `LENGTH (args:(string # type) list) = LENGTH (tvs:type_value list) /\
   LENGTH args = LENGTH tx.args` by
    (conj_tac >- fs[LIST_REL_EL_EQN] >> drule bind_arguments_length >> simp[]) >>
  suspend "register"
QED

Resume grouped_legacy_bound_registration[register]:
  mp_tac (Q.INST [`kw` |-> `[]`, `kwtvs` |-> `[]`, `kwvals` |-> `[]`,
    `pos` |-> `args:(string # type) list`, `ptvs` |-> `tvs:type_value list`, `pvals` |-> `tx.args`,
    `ce` |-> `ce0`, `entry` |-> `reg`, `last` |-> `sa`,
    `es` |-> `ev`, `s` |-> `u`, `env` |-> `type_env tops`, `PG` |-> `[]`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] grouped_register_body_arguments))) >>
  simp_tac (srw_ss()) [selected_registration_owners_def] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`J`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`ev with scopes := [envb]`,`t`,`J`,`tz`] >>
  asm_simp_tac (srw_ss()) [] >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Finalise grouped_legacy_bound_registration
