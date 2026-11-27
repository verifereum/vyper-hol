(* Bind a canonical legacy call using the reached registration resources. *)
Theory groupedCanonicalBoundRegistration
Ancestors
  groupedCanonicalRegistrationFinish entryPtrSeamRegister externalEntryBound
  selectedAcceptedFold defaultConcreteRegistrationDefs entryStateRel
  fragGasOriginPtr fragExec bodyPtrDefs vyperStorageFootprint vyperCall
  vyperInterpreter vyperState vyperCalldata vyperValue vyperABI
  loweringStateRelDefs compileEnv moduleLowering ptrDiscipline
  venomExecSemantics venomState venomInst finite_map list words

Theorem grouped_canonical_bound_registration:
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
  calldata_encodes (type_env tops) tx.function_name (MAP SND args)
    tx.args u.vs_call_ctx.cc_calldata /\
  LIST_REL value_has_type tvs tx.args /\
  LENGTH u.vs_call_ctx.cc_calldata < dimword (:256) /\
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
  `LENGTH args = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
  `LIST_REL (abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields)
     (MAP SND args) tvs` by
    (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     `MEM (EL n args,EL n tvs) (ZIP (args,tvs))` by
       (simp[MEM_EL, EL_ZIP] >> qexists_tac `n` >> simp[EL_ZIP]) >>
     first_x_assum (qspecl_then [`ce0`,`EL n args`,`EL n tvs`] mp_tac) >> simp[]) >>
  `!j. j < LENGTH args ==> type_memory_size (EL j tvs) < dimword (:256)` by
    fs[EVERY_EL] >>
  drule_at (Pat `LIST_REL (abi_decoder_coherent _ _ _) _ _`)
    registration_owned_source_ready >>
  disch_then (drule_at (Pat `calldata_encodes _ _ _ _ _`)) >>
  simp[] >> disch_tac >>
  suspend "register"
QED

Resume grouped_canonical_bound_registration[register]:
  mp_tac (Q.SPECL [`\aid q n. MEM (mk_inst aid ALLOCA [Lit (n2w n)] [q]) (fn_insts fn)`,
    `ce0`,`args`,`tvs`,`tx.args`,`type_env tops`,`ce0.ce_struct_fields`,
    `u.vs_call_ctx`,`ctx`,`fn`,`site`,`0`,`[]`] registration_owned_suffix_joint) >>
  impl_tac >- (rpt gen_tac >> strip_tac >>
    BETA_TAC >> drule_all_then ACCEPT_TAC registration_singleton_owner_instruction) >>
  disch_then (qspecl_then [`0`,`ce0`,`reg`,`u`,`G`,`tn`,`cf`,`sa`] mp_tac) >>
  simp_tac (srw_ss()) [] >>
  impl_tac >- (
    `!j. j < LENGTH args ==> ?loc.
       FLOOKUP ce0.ce_vars (FST (EL j args)) = SOME loc /\
       var_location_memory_size loc = SOME (type_memory_size (EL j tvs))` by
      (rpt strip_tac >>
       qpat_assum `LIST_REL _ args tvs` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
       simp[] >> disch_then (qspec_then `j` mp_tac) >>
       Cases_on `EL j args` >> fs[]) >>
    fs[selected_registration_resources_def] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`J`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "finish"
QED

Resume grouped_canonical_bound_registration[finish]:
  drule_all (SIMP_RULE (srw_ss()) [] grouped_canonical_registration_finish) >>
  disch_then (qx_choose_then `es` assume_tac) >>
  qexistsl_tac [`es`,`t`,`J`,`tz`] >> simp[]
QED

Finalise grouped_canonical_bound_registration
