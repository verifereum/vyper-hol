(* Package environments preserve the caller's module interpretation.
   Module-pin equalities are parameters here to avoid a seam-theory cycle. *)
Theory bodyIntCallPackageGlobals
Ancestors
  compileVyper compileEnv exprLoweringProps stmtSimReturn
  immutableLocationProps bodyIntCallImmutableBoundary intCallCallee
  list pair finite_map

Theorem internal_package_global_fields:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) ==>
  ce.ce_module = NONE /\
  ce.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  ce.ce_is_ctor = ctor
Proof
  rpt gen_tac >>
  simp[set_internal_package_target_def, package_internal_fn_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[build_compile_env_module_vars]
QED

Theorem package_globals_state_rel:
  state_rel func caller cx es s /\
  ce.ce_module = caller.ce_module /\
  ce.ce_module_vars = caller.ce_module_vars /\
  ce.ce_is_ctor = caller.ce_is_ctor ==>
  state_rel func ce cx (es with scopes := []) s
Proof
  strip_tac >> drule state_rel_scopes_nil >> strip_tac >>
  irule state_rel_cenv_cong >>
  qexists_tac `caller` >> simp[vyperStateTheory.lookup_scopes_def]
QED

Theorem package_initialized_immutable_regions:
  stmt_state_rel ctx func caller cx es s /\
  ce.ce_module = caller.ce_module /\
  ce.ce_module_vars = caller.ce_module_vars /\
  ce.ce_is_ctor = caller.ce_is_ctor ==>
  internal_immutable_regions ce cx es s.vs_alloca_next
Proof
  simp[internal_immutable_regions_def] >> rpt strip_tac >>
  `immutables_rel caller cx.txn.target caller.ce_module caller.ce_is_ctor es s` by
    gvs[stmt_state_rel_def, state_rel_def]
  >~ [`val_wf tv v`]
  >- (gvs[immutables_rel_def] >>
      irule (cj 1 loweringSliceTheory.immutable_admissible_val_wf) >>
      metis_tac[]) >>
  drule_all initialized_immutable_regions >> simp[]
QED
