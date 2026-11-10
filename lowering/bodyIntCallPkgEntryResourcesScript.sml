(* Resource transfer across internal-call setup. *)
Theory bodyIntCallPkgEntryResources
Ancestors
  bodyIntCallUnitCharge bodySim bodyIntCallResource venomExecSemantics
  vyperCompiler stmtSimDefs intCallCallee exprLoweringProps
  moduleLowering compileEnv externalEntryShape compileVyper
  bodyIntCallPackageLayout bodyIntCallPackageResource entryStateRel
  venomExecProofs list words

Theorem internal_call_setup_room:
  stmt_state_rel ctx func caller cx es t /\
  fn_directly_calls ctx func.fn_name lbl /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  margin <= unit_alloca_frame ctx ==>
  t.vs_alloca_next + margin < dimword (:256) /\
  alloca_room ctx callee setup /\ fmp_room ctx callee setup
Proof
  rpt strip_tac >>
  `callee.fn_name = lbl` by metis_tac[lookup_function_result_name] >>
  `alloca_room ctx func t /\ fmp_room ctx func t` by
    gvs[stmt_state_rel_def] >>
  drule setup_callee_frontier >> strip_tac >>
  drule setup_callee_frame >> strip_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`] alloca_room_call_reserve)) >>
      metis_tac[]) 
  >- (irule alloca_room_callee >> metis_tac[])
  >> irule fmp_room_callee >> metis_tac[]
QED

Theorem internal_bodies_compilation:
  !packages lbl ce params has_rb is_nr key trans view ctor imm bd rt se sf.
  MEM (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm,bd,rt) packages /\
  compile_internal_fn_bodies packages se = ((),sf) ==>
  ?sa sb. compile_internal_function ce params has_rb is_nr key trans view
    ctor imm bd rt sa = ((),sb) /\ cs_extends sb sf
Proof
  Induct >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def,
       comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[]
  >- (mp_tac (Q.SPECL [`packages`,`K T`]
        compile_internal_fn_bodies_labels) >> simp[] >>
      metis_tac[pairTheory.SND])
  >> first_x_assum drule >> metis_tac[]
QED

Theorem runtime_internal_bodies_compilation:
  compile_generate_runtime sels exts ints fb dispatch buckets metadata dense
    entry sa = ((),sb) ==>
  ?sm. compile_internal_fn_bodies ints sm = ((),sb)
Proof
  simp[compile_generate_runtime_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem deploy_internal_bodies_compilation:
  compile_generate_deploy T runtime_size imm args data_size ints ce bd
    pay nr key trans sa = ((),sb) ==>
  ?sm. compile_internal_fn_bodies ints sm = ((),sb)
Proof
  simp[compile_generate_deploy_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem internal_package_charge_premises:
  !target tops trans keys ctor imm mut nr rr name args dflts ret bd
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) /\
  ALL_DISTINCT (MAP FST args) /\
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,bd) ==>
  ALL_DISTINCT (MAP FST params) /\
  (!nm off sz. MEM nm (MAP FST params) /\
    FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==> sz < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule internal_package_stack_layout >> strip_tac >>
      gvs[MAP_ZIP, LENGTH_compute_pass_via_stack]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM nm (MAP FST params)` mp_tac >>
  simp[MEM_EL, PULL_EXISTS] >> qx_gen_tac `i` >> strip_tac >>
  `FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz)` by
    metis_tac[EL_MAP] >>
  drule_all internal_package_parameter_layout >> strip_tac >>
  qpat_x_assum `fn_allocs_ok _ _` mp_tac >>
  simp[fn_allocs_ok_def] >> strip_tac >>
  `i < LENGTH args` by metis_tac[] >>
  qpat_x_assum `EVERY _ args` mp_tac >>
  simp[EVERY_EL] >> disch_then (qspec_then `i` mp_tac) >> simp[] >>
  Cases_on `EL i args` >> rename1 `EL i args = (argname,argty)` >>
  simp[] >> strip_tac >>
  `type_memory_bytes ce argty =
   type_memory_bytes (build_compile_env tops Internal mut name args ret bd F) argty` by
    (irule type_memory_bytes_struct_fields >>
     simp[build_compile_env_ce_struct_fields]) >>
  gvs[] >> irule vyperArithTheory.lt_dimword_256 >>
  qexists_tac `64` >> simp[]
QED

Theorem internal_package_stack_size_options:
  !tops mut nr rr name args dflts ret bd
   target trans keys ctor imm lbl ce params has_rb is_nr key use_tr view
   is_ctor imm_len ss rt
   target' trans' keys' ctor' imm' lbl' ce' params' has_rb' is_nr' key'
   use_tr' view' is_ctor' imm_len' ss' rt'.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
      (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) /\
  set_internal_package_target target'
    (package_internal_fn tops trans' keys' ctor' imm'
      (mut,nr,rr,name,args,dflts,ret,bd)) =
      (lbl',ce',params',has_rb',is_nr',key',use_tr',view',is_ctor',imm_len',ss',rt') ==>
  internal_stack_size ce params = internal_stack_size ce' params'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `set_internal_package_target target _ = _`
    (strip_assume_tac o MATCH_MP internal_package_stack_layout) >>
  qpat_x_assum `set_internal_package_target target' _ = _`
    (strip_assume_tac o MATCH_MP internal_package_stack_layout) >>
  gvs[] >> irule internal_stack_size_vars >> simp[]
QED
