(* Exact declared-parameter capacities in an internal package. *)
Theory bodyIntCallPackageLayout
Ancestors
  compileVyper compileEnv entryStateRel structFieldsProps intCallArgs list pair
  bodyIntCallSource exprSimHyps exprSimHypsDefs bodySim supportedProgram supportedNames

Theorem build_compile_env_arg_sizes:
  !args nm ty tops vis mut fname ret body trans.
  ALL_DISTINCT (MAP FST args) /\ MEM (nm,ty) args ==>
  ?off. FLOOKUP
    (build_compile_env tops vis mut fname args ret body trans).ce_vars nm =
    SOME (MemLoc off
      (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`args`,`get_struct_fields (make_struct_fields_map tops)`,
               `0`,`FEMPTY`] mp_tac allocate_args_lookup >>
  simp[] >> strip_tac >>
  qpat_x_assum `EVERY _ args` mp_tac >> simp[EVERY_MEM] >>
  disch_then (drule_at Any) >>
  simp[build_compile_env_def, pairTheory.UNCURRY]
QED

Theorem internal_package_parameter_layout:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt i po psz.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) /\
  ALL_DISTINCT (MAP FST args) /\ i < LENGTH params /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
  LENGTH params = LENGTH args /\
  FST (EL i params) = FST (EL i args) /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  psz = type_memory_bytes ce (SND (EL i args))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[set_internal_package_target_def, package_internal_fn_def,
      update_cenv_nonreentrant_def, LENGTH_compute_pass_via_stack,
      LENGTH_ZIP, EL_ZIP, EL_MAP] >>
  `MEM (FST (EL i args),SND (EL i args)) args` by
    (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  rewrite_tac[GSYM type_mem_bytes_type_memory_bytes] >>
  simp[build_compile_env_ce_struct_fields] >>
  metis_tac[build_compile_env_arg_sizes, var_location_11, optionTheory.SOME_11]
QED

(* This also applies to constructor packages and to stack parameters: the
   location's capacity is the declared type's footprint in either case. *)
Theorem internal_package_argument_capacity:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt i po psz
   caller cx env es es0 tv.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) /\
  ALL_DISTINCT (MAP FST args) /\ MAP expr_type es = MAP SND args /\
  caller.ce_struct_fields = make_struct_fields_map tops /\
  expr_sim_inv caller cx env es0 /\
  i < LENGTH params /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
  evaluate_type (get_tenv cx) (expr_type (EL i es)) = SOME tv ==>
  psz = type_memory_bytes caller (expr_type (EL i es)) /\
  psz = type_memory_size tv /\
  type_memory_size tv <= psz /\
  psz <= MAX 32 (type_memory_bytes caller (expr_type (EL i es)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all internal_package_parameter_layout >> strip_tac >>
  `i < LENGTH es` by metis_tac[LENGTH_MAP] >>
  `expr_type (EL i es) = SND (EL i args)` by
    metis_tac[EL_MAP] >>
  `type_memory_bytes ce (SND (EL i args)) =
   type_memory_bytes caller (SND (EL i args))` by
    (irule type_memory_bytes_struct_fields >> simp[]) >>
  drule_all expr_sim_inv_memory_size >> simp[]
QED

Theorem body_intcall_selected_parameter_capacity:
  !tops ctx caller cx env ann name es dflt es0 mut args ret ss rr
   trans keys ctor imm lbl ce params has_rb is_nr key use_tr view is_ctor
   imm_len ss' rt target i po psz tv.
  body_inv tops ctx caller cx /\
  expr_body_pre caller cx env
    (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,F,args,[],ret,ss) /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,F,rr,name,args,[],ret,ss)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss',rt) /\
  i < LENGTH params /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
  evaluate_type (get_tenv cx) (expr_type (EL i es)) = SOME tv ==>
  psz = type_memory_bytes caller (expr_type (EL i es)) /\
  psz = type_memory_size tv /\
  type_memory_size tv <= psz /\
  psz <= MAX 32 (type_memory_bytes caller (expr_type (EL i es)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_intcall_source_selection >> strip_tac >> gvs[] >>
  `supported_declaration_names tops` by
    metis_tac[body_inv_def, supported_program_names] >>
  `ALL_DISTINCT (MAP FST args)` by
    (gvs[supported_declaration_names_def, EVERY_MEM,
         supported_function_header_names_def, supported_function_bindings_def] >>
     qpat_x_assum `!e. MEM e tops ==> _` drule >> simp[]) >>
  `caller.ce_struct_fields = make_struct_fields_map tops /\
   expr_sim_inv caller cx env es0` by
    gvs[body_inv_def, expr_body_pre_def] >>
  drule_all internal_package_argument_capacity >> simp[]
QED
