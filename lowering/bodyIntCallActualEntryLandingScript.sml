(* Semantic boundary for the actual internal entry, including constructor reservation. *)
Theory bodyIntCallActualEntryLanding
Ancestors
  bodyIntCallActualEntryWitness bodyIntCallActualEntrySemantic
  bodyIntCallActualEntryResource bodyIntCallActualEntryFields
  intCallCallee compileEnv loweringStateRelDefs exprLoweringProps context venomState finite_map list

Theorem state_rel_imm_alloca:
  state_rel func (ce with ce_imm_alloca := imm) cx vs s =
  state_rel func ce cx vs s
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def, local_backed_def,
       storage_vars_rel_def, transient_vars_rel_def, immutables_rel_def,
       logs_rel_def, LIST_REL_EL_EQN, log_entry_equiv_def]
QED

Theorem internal_entry_landing_state_rel:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u ==>
  state_rel func (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    cx (vs with scopes := [env]) u
Proof
  strip_tac >> drule_all internal_entry_landing_resources >> strip_tac >>
  drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  simp[state_rel_imm_alloca] >>
  irule internal_body_state_rel >>
  conj_tac >- fs[mat_inv_def] >>
  qpat_assum `materialize_internal_params _ _ _ = _`
    (irule_at (Pat `materialize_internal_params _ _ _ = _`)) >>
  qpat_assum `state_rel _ _ _ _ _` (irule_at Any) >>
  qpat_assum `setup_callee _ _ _ = _` (irule_at Any) >>
  qpat_assum `mat_frame _ _ _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`SOME (PtrVar rpc 0)`, `stage_ce.ce_return_buf`] >>
  conj_tac >- gvs[] >>
  drule internal_entry_prefix_shapes >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST c) (MAP FST params)` by metis_tac[MEM_MAP] >>
  fs[MEM_EL] >>
  fs[internal_args_rel_def, EL_MAP] >>
  qpat_x_assum `!i. i < LENGTH params ==> _` drule >>
  strip_tac >> goal_assum (drule_at Any)
QED

Theorem internal_entry_landing_immutable_sep:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  (ce.ce_is_ctor ==> !i po psz name tv iv io.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv)
      (w2n (EL ((if has_rb then 1 else 0) + i) args)) psz) ==>
  immutable_alloca_sep func
    (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    cx (vs with scopes := [env]) u
Proof
  strip_tac >> drule_all internal_entry_landing_resources >> strip_tac >>
  drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  fs[mat_inv_def, internal_immutable_regions_def] >>
  simp[immutable_alloca_sep_def] >> strip_tac >> fs[] >>
  rpt gen_tac >> strip_tac >>
  `off + type_memory_size tv <= caller.vs_alloca_next` by
    (qpat_x_assum `!name tv v off. _ ==> _` drule_all >> simp[]) >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b sz. FLOOKUP u.vs_allocas aid = _ ==> _` drule >>
      simp[regions_disjoint_def]) >>
  rpt strip_tac >>
  `local_region ce2 [env] u id b sz` by fs[local_region_def] >>
  qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` drule >>
  strip_tac >- simp[regions_disjoint_def] >>
  gvs[] >>
  qpat_x_assum `!i po psz name tv iv io. _` irule >>
  simp[] >> qexistsl_tac [`v`, `name`] >> simp[]
QED

Theorem internal_entry_landing_base_zero:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP caller.vs_labels "runtime_begin")) ==>
  immutable_base_zero
    (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) u
Proof
  strip_tac >> drule_all internal_entry_operand_landing >> strip_tac >>
  drule_all internal_entry_landing_resources >> strip_tac >>
  drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  `u.vs_labels = caller.vs_labels` by
    (qpat_x_assum `mat_frame _ _ _` mp_tac >>
     qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs(), mat_frame_def] >>
     rpt strip_tac >> gvs[venomStateTheory.venom_state_component_equality]) >>
  simp[immutable_base_zero_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[eval_operand_def]
QED

Theorem internal_entry_landing_stmt_state_rel:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  alloca_room ctx func s0 /\ fmp_room ctx func s0 /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP caller.vs_labels "runtime_begin")) /\
  (ce.ce_is_ctor ==> !i po psz name tv iv io.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv)
      (w2n (EL ((if has_rb then 1 else 0) + i) args)) psz) ==>
  stmt_state_rel ctx func
    (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    cx (vs with scopes := [env]) (u with vs_inst_idx := k)
Proof
  strip_tac >> drule_all internal_entry_landing_state_rel >> strip_tac >>
  drule_all internal_entry_landing_immutable_sep >> strip_tac >>
  drule_all internal_entry_landing_base_zero >> strip_tac >>
  drule_all internal_entry_landing_resources >> strip_tac >>
  drule_all internal_entry_landing_rooms >> strip_tac >>
  simp[stmt_state_rel_inst_idx, stmt_state_rel_def] >> fs[mat_inv_def] >>
  first_assum ACCEPT_TAC
QED
