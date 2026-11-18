(* Initialize registration at the endpoint of the selected entry checks. *)
Theory calldataNoneRegisterInit
Ancestors
  defaultEntryResourceInit defaultConcreteRegistrationDefs abiDecoderCoherence
  e2eDefs vyperLoweringCorrect moduleLoweringProps compileVyper moduleLowering
  compileEnv fragExec valueEncoding vyperCalldata vyperTypeABI venomInst
  venomState ptrDiscipline finite_map words list

Theorem none_selected_registration_inputs:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ initial_venom_state_rel tops am tx vs /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  compile_entry_checks mincd pay opened = ((),checked) /\
  opened.cs_current_insts = [] /\ fn_has_code opened checked func /\
  tys = MAP SND args /\ OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
  LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args (ZIP (tys,tvs)) /\
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  compile_register_positional_args ce pos 4 checked = (ce',last) /\
  fn_has_code checked last func /\
  mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
  vars_pc_only vs p /\ p.vs_call_ctx = vs.vs_call_ctx /\
  LENGTH p.vs_call_ctx.cc_calldata < dimword (:256) /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} /\
  mincd <= LENGTH p.vs_call_ctx.cc_calldata /\
  vars_pc_only p t /\ fresh_vars_wrt checked t /\ ~t.vs_halted /\
  t.vs_current_bb = checked.cs_current_bb /\
  t.vs_inst_idx = LENGTH checked.cs_current_insts /\ t.vs_call_ctx = p.vs_call_ctx /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm ==>
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  compile_register_positional_args ce (build_positional_args ce args) 4 checked = (ce',last) /\
  fn_has_code checked last func /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256) /\
  t.vs_call_ctx.cc_calldata = vs.vs_call_ctx.cc_calldata /\
  default_registration_resources unit.cu_context func site 0 checked t u /\
  default_registration_entry_frame vs t
Proof
  strip_tac >>
  `vars_pc_only vs t` by (drule_all vars_pc_only_trans >> simp[]) >>
  `u.t_mem = {} /\ u.t_stor = {} /\ u.t_trans = {} /\ u.t_imm = {}` by simp[] >>
  drule_all default_post_checks_resources >> strip_tac >> gvs[] >>
  drule OPT_MMAP_LENGTH >> strip_tac >>
  simp[LIST_REL_EL_EQN] >> qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `LIST_REL _ args _`
    (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  Cases_on `EL i args` >> simp[EL_ZIP, EL_MAP]
QED
