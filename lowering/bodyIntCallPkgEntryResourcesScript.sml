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

