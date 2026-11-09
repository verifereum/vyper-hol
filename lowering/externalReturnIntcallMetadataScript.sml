Theory externalReturnIntcallMetadata
Ancestors
  externalReturnPhysicalMetadata externalReturnPackage compileVyper compileEnv
  bodySim entryStateRel structFieldsProps vyperAST

Theorem return_compute_info_bufferless:
  compute_func_info sft ret sz ats = (0,0,pvs) ==>
  ret = NoneT \/ sz = 0
Proof
  Cases_on `ret` >> simp[compute_func_info_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem return_build_info_bufferless:
  !tops sft name pvs.
  build_func_info sft tops name = (0,0,pvs) ==>
  build_func_return_type tops name = NoneT \/
  type_mem_bytes sft (build_func_return_type tops name) = 0
Proof
  Induct >> simp[build_func_info_def, build_func_return_type_def] >>
  Cases_on `h` >> simp[build_func_info_def, build_func_return_type_def] >>
  rpt gen_tac >> rpt IF_CASES_TAC >> simp[] >>
  metis_tac[return_compute_info_bufferless]
QED

Theorem return_package_info_struct_tables:
  package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (lbl,ce,pos_args,min_cds,is_payable,nr',nkey,ut,iv,ss,rt) ==>
  ce.ce_func_info = build_func_info (get_struct_fields ce.ce_struct_fields) tops
Proof
  Cases_on `ret = NoneT` >>
  simp[package_external_fn_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[] >> simp[update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem return_register_info_struct_tables:
  compile_register_positional_args ce args off st = (ce',st') ==>
  ce'.ce_func_info = ce.ce_func_info /\
  ce'.ce_struct_fields = ce.ce_struct_fields
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `ce' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem return_same_frame_info_struct_tables:
  same_frame ce ce' ==>
  ce'.ce_func_info = ce.ce_func_info /\
  ce'.ce_struct_fields = ce.ce_struct_fields
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem return_selected_bufferless:
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv ce /\ ce.ce_func_info name = (0,0,pvs) ==>
  ce.ce_func_return_type name = NoneT \/
  type_memory_bytes ce (ce.ce_func_return_type name) = 0
Proof
  strip_tac >>
  drule_all return_selected_same_frame_return_table >> strip_tac >>
  drule return_package_target_inversion >> strip_tac >>
  drule return_package_info_struct_tables >> strip_tac >>
  drule return_register_info_struct_tables >> strip_tac >>
  drule return_same_frame_info_struct_tables >> strip_tac >>
  gvs[] >> drule return_build_info_bufferless >>
  simp[type_mem_bytes_type_memory_bytes] >>
  metis_tac[type_memory_bytes_struct_fields]
QED
