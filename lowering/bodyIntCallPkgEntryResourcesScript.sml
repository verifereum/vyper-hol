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

Theorem runtime_internal_charge_witness:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  classify_functions tops = (exts,ints,fb,ctor) ==>
  ?se sf.
    compile_internal_fn_bodies
      (MAP (set_internal_package_target policy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) F 0) ints)
      se = ((),sf) /\
    SUM (MAP alloca_lit_size
      (FILTER (\inst. inst.inst_opcode = ALLOCA) (state_insts sf))) <=
      unit_alloca_frame unit.cu_context
Proof
  rpt strip_tac >>
  Cases_on `compile_generate_runtime
      (build_selectors (type_env tops) exts)
      (MAP (set_external_package_target policy.rpol_target o
        package_external_fn tops F (assign_nkeys tops 0)) exts)
      (MAP (set_internal_package_target policy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) F 0) ints)
      (set_fallback_package_target policy.rpol_target
        (package_fallback_fn tops F (assign_nkeys tops 0) fb))
      policy.rpol_frontend_dispatch 0 0 []
      (build_dense_entry_info (build_selectors (type_env tops) exts)
        (MAP (set_external_package_target policy.rpol_target o
          package_external_fn tops F (assign_nkeys tops 0)) exts))
      (initial_compile_state "__entry")` >>
  rename1 `_ = (uv,sf)` >> Cases_on `uv` >>
  drule_all runtime_unit_alloca_charge >> strip_tac >>
  drule runtime_internal_bodies_compilation >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem deploy_internal_charge_witness:
  lower_vyper_deploy_unit tops policy bytes = SOME unit /\
  classify_functions tops = (exts,ints,fb,ctor) /\
  IS_SOME ctor /\
  set_constructor_package_target policy.rpol_target
    (case ctor of
       SOME cf => package_constructor tops F (assign_nkeys tops 0) cf
     | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                F,F,0n,F,([] : stmt list),NoneT)) =
    (ce,cargs,pay,nr,key,trans,bd,rt) ==>
  ?se sf.
    compile_internal_fn_bodies
      (MAP (set_internal_package_target policy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) T
          (compute_immutables_len
            (get_struct_fields (make_struct_fields_map tops)) tops)) ints)
      se = ((),sf) /\
    SUM (MAP alloca_lit_size
      (FILTER (\inst. inst.inst_opcode = ALLOCA) (state_insts sf))) <=
      unit_alloca_frame unit.cu_context
Proof
  rpt strip_tac >>
  Cases_on `compile_generate_deploy (IS_SOME ctor) (LENGTH bytes)
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops)
      cargs 0
      (if IS_SOME ctor then
         MAP (set_internal_package_target policy.rpol_target o
           package_internal_fn tops F (assign_nkeys tops 0) T
             (compute_immutables_len
               (get_struct_fields (make_struct_fields_map tops)) tops)) ints
       else [])
      ce bd pay nr key trans (initial_compile_state "__deploy")` >>
  rename1 `_ = (uv,sf)` >> Cases_on `uv` >>
  drule_all deploy_unit_alloca_charge >> strip_tac >>
  gvs[] >> drule deploy_internal_bodies_compilation >> strip_tac >>
  metis_tac[]
QED

Theorem packaged_internal_bodies_compilation:
  MEM source_fn ints /\
  compile_internal_fn_bodies
    (MAP (set_internal_package_target target o
      package_internal_fn tops trans keys ctor imm) ints) se = ((),sf) ==>
  ?lbl ce ps hr isn key use_tr view is_ctor il ss rt sa sb.
    set_internal_package_target target
      (package_internal_fn tops trans keys ctor imm source_fn) =
      (lbl,ce,ps,hr,isn,key,use_tr,view,is_ctor,il,ss,rt) /\
    compile_internal_function ce ps hr isn key use_tr view is_ctor il ss rt
      sa = ((),sb) /\ cs_extends sb sf
Proof
  rpt strip_tac >>
  `MEM (set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm source_fn))
    (MAP (set_internal_package_target target o
      package_internal_fn tops trans keys ctor imm) ints)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  Cases_on `set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm source_fn)` >>
  PairCases_on `r` >> gvs[] >>
  drule_all internal_bodies_compilation >> simp[]
QED

Theorem body_inv_internal_charge_witness:
  body_inv tops ctx caller cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret bd) tops ==>
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,bd) /\
  ?keys imm lbl ce ps hr isn key tr view ctor il ss rt sa sb sf.
    set_internal_package_target caller.ce_target
      (package_internal_fn tops F keys caller.ce_is_ctor imm
        (mut,nr,rr,name,args,dflts,ret,bd)) =
      (lbl,ce,ps,hr,isn,key,tr,view,ctor,il,ss,rt) /\
    compile_internal_function ce ps hr isn key tr view ctor il ss rt sa = ((),sb) /\
    cs_extends sb sf /\
    SUM (MAP alloca_lit_size
      (FILTER (\inst. inst.inst_opcode = ALLOCA) (state_insts sf))) <=
      unit_alloca_frame ctx
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_fn)` >>
  `MEM (mut,nr,rr,name,args,dflts,ret,bd) ints` by
    metis_tac[loweringShapePropsTheory.MEM_classify_internal,
      pairTheory.FST, pairTheory.SND] >>
  gvs[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
  >- (`fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,bd)` by
        metis_tac[lower_vyper_deploy_unit_allocs_ok] >>
      Cases_on `set_constructor_package_target rpolicy.rpol_target
        (case ctor_fn of
           SOME cf => package_constructor tops F (assign_nkeys tops 0) cf
         | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                    F,F,0n,F,([] : stmt list),NoneT))` >>
      PairCases_on `r` >>
      drule_all deploy_internal_charge_witness >> strip_tac >>
      drule_all packaged_internal_bodies_compilation >> strip_tac >>
      conj_tac >- simp[] >>
      metis_tac[]) >>
  `fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,bd)` by
    metis_tac[lower_vyper_runtime_unit_allocs_ok] >>
  drule_all runtime_internal_charge_witness >> strip_tac >>
  drule_all packaged_internal_bodies_compilation >> strip_tac >>
  conj_tac >- simp[] >> metis_tac[]
QED

Theorem body_internal_package_stack_bound:
  body_inv tops ctx caller cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret bd) tops /\
  ALL_DISTINCT (MAP FST args) /\
  set_internal_package_target caller.ce_target
    (package_internal_fn tops trans keys caller.ce_is_ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
    (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,il,ss,rt) ==>
  internal_stack_size ce params <= unit_alloca_frame ctx
Proof
  strip_tac >> drule_all body_inv_internal_charge_witness >> strip_tac >>
  drule_all internal_package_charge_premises >> strip_tac >>
  drule_all bodyIntCallFunctionChargeTheory.compile_internal_function_stack_charge >> strip_tac >>
  drule state_alloca_charge_mono >> strip_tac >>
  qpat_x_assum `set_internal_package_target _
    (package_internal_fn _ trans keys _ imm _) = _`
    (mp_then Any mp_tac internal_package_stack_size_options) >>
  disch_then drule >> strip_tac >> decide_tac
QED

Theorem body_internal_package_room:
  body_inv tops ctx caller cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret bd) tops /\
  ALL_DISTINCT (MAP FST args) /\
  set_internal_package_target caller.ce_target
    (package_internal_fn tops trans keys caller.ce_is_ctor imm
      (mut,nr,rr,name,args,dflts,ret,bd)) =
    (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,il,ss,rt) /\
  stmt_state_rel ctx func caller cx es t /\
  fn_directly_calls ctx func.fn_name lbl /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup ==>
  t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  alloca_room ctx callee setup /\ fmp_room ctx callee setup
Proof
  strip_tac >> drule_all body_internal_package_stack_bound >> strip_tac >>
  irule internal_call_setup_room >> metis_tac[]
QED
