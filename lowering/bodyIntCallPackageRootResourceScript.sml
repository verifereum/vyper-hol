(* Context-insensitive resources used to instantiate the actual root. *)
Theory bodyIntCallPackageRootResource
Ancestors
  bodyIntCallPackageRootSemantic bodyIntCallPackageGeometry
  bodyIntCallActualJointInit bodyIntCallPackageInputs bodyIntCallJointInputs
  bodyIntCallActualEntryProtection bodyIntCallActualEntryLanding
  bodyIntCallActualEntryFields bodyIntCallActualEntryWitness
  compileEnv vyperContext vyperState accountsRelProps compileVyper moduleLowering
  bodyIntCallActualEntryReservation bodyIntCallSemanticEntry intCallCallee list pair
  bodyIntCallJointContract

Theorem state_rel_call_stack:
  state_rel func ce (cx with stk updated_by f) es s =
  state_rel func ce cx es s
Proof
  `storage_dead (cx with stk updated_by f) = storage_dead cx` by
    (irule storage_dead_cx_cong >> simp[]) >>
  `accounts_agree (cx with stk updated_by f) = accounts_agree cx /\
   transient_agree (cx with stk updated_by f) = transient_agree cx /\
   request_agree (cx with stk updated_by f) = request_agree cx` by
    (irule agree_cx_cong >> simp[]) >>
  simp[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
       storage_vars_rel_def, transient_vars_rel_def, get_module_code_def]
QED

Theorem packaged_internal_entry_reserved:
  supported_function_body tops Internal args ss /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  local_ptrs_reserved (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) st1
Proof
  strip_tac >> irule internal_entry_installed_reserved >>
  goal_assum (drule_at Any) >>
  drule supported_body_param_separation >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  simp[cj 1 MAP_ZIP, LENGTH_compute_pass_via_stack, LENGTH_MAP] >>
  rpt conj_tac
  >- (rpt strip_tac >> drule (cj 2 build_compile_env_vars) >> simp[])
  >- simp[cj 3 build_compile_env_vars]
  >- (rpt strip_tac >>
      simp[EL_ZIP, LENGTH_compute_pass_via_stack, LENGTH_MAP] >>
      irule (cj 1 build_compile_env_vars) >>
      simp[MEM_EL] >> goal_assum (drule_at Any) >> simp[EL_MAP]) >>
  simp[build_compile_env_def, pairTheory.ELIM_UNCURRY]
QED

Theorem packaged_internal_entry_return_fields:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  cenv_module_pins tops (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
  ce2.ce_return_pc = SOME (PtrVar pc 0) /\
  ce2.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce2.ce_struct_fields name)) ret /\
  (has_rb <=> ce2.ce_returns_count = 0 /\ ret <> NoneT) /\
  (has_rb ==> ?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
  (~has_rb ==> ce.ce_return_buf = NONE)
Proof
  strip_tac >> drule internal_entry_return_pc >> strip_tac >>
  drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  `cenv_module_pins tops ce` by
    (gvs[package_internal_fn_def, set_internal_package_target_def,
         update_cenv_nonreentrant_def] >>
     simp[cenv_module_pins_def] >>
     metis_tac[SRULE [cenv_module_pins_def] build_compile_env_module_pins]) >>
  drule_all internal_entry_module_pins >> strip_tac >>
  simp[] >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  simp[build_compile_env_returns_count, build_compile_env_ce_struct_fields] >>
  simp[build_compile_env_def, pairTheory.ELIM_UNCURRY] >>
  simp[allocate_internal_special_vars_def] >>
  Cases_on `ret = NoneT` >> simp[]
QED

Theorem internal_entry_installed_operands:
  compile_internal_function_entry ce params has_rb ctor n rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  (has_rb ==> ?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
  (~has_rb ==> ce.ce_return_buf = NONE) ==>
  (?x. rpc = Var x /\ not_fresh_at st1 x /\
    lookup_var x u = SOME s0.vs_return_pc_token) /\
  (!op sz. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).
    ce_return_buf = SOME (PtrVar op sz) ==>
    ?x w. op = Var x /\ not_fresh_at st1 x /\ lookup_var x u = SOME w) /\
  (!op. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).
    ce_imm_alloca = SOME op ==>
    ?x w. op = Var x /\ not_fresh_at st1 x /\ lookup_var x u = SOME w)
Proof
  strip_tac >> drule_all internal_entry_operand_landing >> strip_tac >>
  simp[] >> conj_tac
  >- (Cases_on `has_rb`
      >- (gvs[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
      gvs[] >> drule internal_entry_no_return_buffer >> simp[]) >>
  metis_tac[]
QED
