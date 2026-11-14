(* Package projections shared by locked entry and return assembly. *)
Theory bodyIntCallNRMetadata
Ancestors
  bodyIntCallMetadata compileVyper compileEnv bodySim supportedNames
  supportedProgram memoryLocalRhsProps

Theorem internal_package_nr_metadata:
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
    (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,ilen,ss,rt) ==>
  ce.ce_nonreentrant = (nr,keys name,trans,mut = View)
Proof
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[]
QED

Theorem body_internal_decl_return_type_generic:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  ce.ce_func_return_type (nsid_to_string (NONE,name)) = ret
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  `build_func_return_type tops name = ret` by
    (irule build_func_return_type_distinct >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[body_inv_def, nsid_to_string_def]
QED
