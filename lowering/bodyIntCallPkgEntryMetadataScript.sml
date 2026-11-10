(* Metadata projections used at the staged package boundary. *)
Theory bodyIntCallPkgEntryMetadata
Ancestors
  bodyIntCallMetadata bodyIntCallStageBinding bodyIntCallPackageBoundary
  bodyIntCallAssembly bodySim supportedProgram supportedNames compileVyper
  compileEnv exprSimHyps list pair

Theorem body_internal_decl_pass_flags:
  body_inv tops ctx caller cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret bd) tops /\
  caller.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs) ==>
  pvs = compute_pass_via_stack (MAP SND args)
    (returns_stack_count
      (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n)) ret)
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  drule_all (SRULE [] (Q.SPEC `Internal`
    (Q.GEN `vis` (SPEC_ALL build_func_info_distinct)))) >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  fs[body_inv_def, nsid_to_string_def, compute_func_info_def] >>
  qpat_x_assum `caller.ce_func_info = _` (fn th =>
    qpat_x_assum `caller.ce_func_info name = _` (mp_tac o REWRITE_RULE [th])) >>
  simp[]
QED

Theorem internal_package_entry_fields:
  !target tops trans keys ctor imm mut nr rr name args dflts ret bd
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) ==>
  lbl = FST (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) /\
  (has_rb <=> returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n))
      ret = 0 /\ ret <> NoneT) /\
  ce.ce_struct_fields = make_struct_fields_map tops
Proof
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[build_compile_env_ce_struct_fields]
QED

Theorem body_internal_package_metadata:
  !tops ctx caller cx mut rr name args ret bd rcn rbs pvs
   trans keys imm lbl ce params has_rb is_nr key use_tr view is_ctor il ss rt.
  body_inv tops ctx caller cx /\
  MEM (FunctionDecl Internal mut F rr name args [] ret bd) tops /\
  caller.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs) /\
  set_internal_package_target caller.ce_target
    (package_internal_fn tops trans keys caller.ce_is_ctor imm
      (mut,F,rr,name,args,[],ret,bd)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,il,ss,rt) ==>
  lbl = internal_fn_label (caller.ce_func_ids (nsid_to_string (NONE,name)))
    (nsid_to_string (NONE,name))
    (caller.ce_func_param_types (nsid_to_string (NONE,name))) caller.ce_is_ctor /\
  (has_rb <=> rcn = 0 /\ ret <> NoneT) /\
  (has_rb <=> rcn = 0 /\
    caller.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT) /\
  MAP SND params = pvs /\
  MAP FST params = MAP FST args /\
  ALL_DISTINCT (MAP FST args) /\
  ce.ce_struct_fields = caller.ce_struct_fields
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_internal_decl_return_count >> strip_tac >>
  drule_all body_internal_decl_pass_flags >> strip_tac >>
  drule_all body_internal_decl_return_type >> strip_tac >>
  drule internal_package_entry_fields >> strip_tac >>
  drule internal_package_staging_layout >> strip_tac >>
  `supported_program tops /\
   caller.ce_func_ids = build_func_ids 0 tops /\
   caller.ce_func_param_types = build_func_param_types tops /\
   caller.ce_struct_fields = make_struct_fields_map tops` by fs[body_inv_def] >>
  drule_all internal_call_package_label >>
  disch_then (qspecl_then [`trans`,`keys`,`imm`] assume_tac) >>
  `supported_declaration_names tops` by metis_tac[supported_program_names] >>
  `ALL_DISTINCT (MAP FST args)` by
    (gvs[supported_declaration_names_def, EVERY_MEM,
         supported_function_header_names_def, supported_function_bindings_def] >>
     qpat_x_assum `!e. MEM e tops ==> _` drule >> simp[]) >>
  gvs[] >> simp[package_internal_fn_def]
QED

Theorem internal_package_descriptor_alignment:
  !target tops trans keys ctor imm mut nr rr name args dflts ret bd
   lbl ce params has_rb is_nr key use_tr view is_ctor il ss rt
   caller cx tenv es D vals penv.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,il,ss,rt) /\
  ALL_DISTINCT (MAP FST args) /\
  ce.ce_struct_fields = caller.ce_struct_fields /\
  expr_sim_inv caller cx tenv es /\
  MAP (\(ty,tv,v,flag,op). ty) D = MAP SND args /\
  MAP (\(ty,tv,v,flag,op). flag) D = MAP SND params /\
  MAP (\(ty,tv,v,flag,op). v) D = vals /\
  bind_arguments (get_tenv cx) args vals = SOME penv /\
  EVERY (\(ty,tv,v,flag,op).
    evaluate_type (get_tenv cx) ty = SOME tv /\
    (flag ==> is_word_type ty)) D ==>
  LENGTH params = LENGTH D /\ ALL_DISTINCT (MAP FST params) /\
  FDOM penv = set (MAP FST params) /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\ evaluate_type (get_tenv cx) ty = SOME tv /\
      (flag ==> is_word_type ty) /\
      FLOOKUP penv (FST (EL i params)) =
        SOME <|assignable := T; type := tv; value := v; popped := []|> /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(ty,tv,v,flag,op).
     evaluate_type (get_tenv cx) ty = SOME tv /\
     type_memory_bytes ce ty = type_memory_size tv /\
     (flag ==> is_word_type ty)) D` by
    (qpat_x_assum `EVERY _ D` mp_tac >>
     simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >>
     drule_all expr_sim_inv_memory_size >>
     metis_tac[type_memory_bytes_struct_fields]) >>
  drule_all internal_package_staged_alignment >> simp[]
QED
