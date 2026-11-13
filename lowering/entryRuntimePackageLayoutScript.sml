(* Stable runtime environment fields across packaging and registration. *)
Theory entryRuntimePackageLayout
Ancestors
  entryStateRel entryLocals immutableLocationProps immutableRelation compileVyper compileEnv exprLowering list

Theorem targeted_external_package_layout:
  set_external_package_target target
    (package_external_fn tops locks keys
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr',key,locks',view,fbody',rt) ==>
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_buf = NONE /\ immutable_section_layout ce tops
Proof
  strip_tac >>
  qspecl_then [`tops`, `External`, `mut`, `name`, `args`, `ret`,
    `fbody`, `locks`] mp_tac immutable_build_compile_env_layout >>
  gvs[set_external_package_target_def, package_external_fn_def,
    update_cenv_nonreentrant_def] >>
  rw[update_cenv_ret_abi_def] >>
  gvs[immutable_section_layout_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem registered_runtime_layout:
  compile_register_positional_args ce pa off st = (cer,registered) /\
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_buf = NONE /\ immutable_section_layout ce tops ==>
  cer.ce_module = NONE /\ ~cer.ce_is_ctor /\ cer.ce_imm_alloca = NONE /\
  cer.ce_return_buf = NONE /\ immutable_section_layout cer tops
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cer = _` (fn th => once_rewrite_tac[th]) >>
  fs[immutable_section_layout_def]
QED

Theorem targeted_external_package_vars:
  set_external_package_target target
    (package_external_fn tops locks keys
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr',key,locks',view,fbody',rt) ==>
  pa = build_positional_args ce args /\
  (!n. MEM n (MAP FST args) ==>
    ?off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz)) /\
  (!n off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==>
    MEM n (MAP FST args)) /\
  (!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar p sz))
Proof
  strip_tac >>
  qspecl_then [`tops`, `External`, `mut`, `name`, `args`, `ret`,
    `fbody`, `locks`] mp_tac build_compile_env_vars >>
  gvs[set_external_package_target_def, package_external_fn_def,
    update_cenv_nonreentrant_def] >>
  rw[update_cenv_ret_abi_def] >>
  gvs[build_positional_args_def] >>
  irule listTheory.MAP_CONG >> simp[] >> Cases >>
  simp[build_positional_arg_def, type_to_abi_dec_info_layout_cong]
QED

Theorem targeted_registered_locals:
  set_external_package_target target
    (package_external_fn tops locks keys
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr',key,locks',view,fbody',rt) /\
  compile_register_positional_args ce pa 4 st = (cer,registered) ==>
  local_ptrs_reserved cer registered /\
  EVERY (\a. ?p sz. FLOOKUP cer.ce_vars (FST a) = SOME (PtrVar (Var p) sz)) args
Proof
  strip_tac >> drule targeted_external_package_vars >> strip_tac >>
  drule targeted_external_package_layout >> strip_tac >>
  drule compile_register_positional_args_reserved >>
  (impl_tac >- gvs[build_positional_args_FST]) >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
  gvs[MEM_MAP] >> metis_tac[]
QED
