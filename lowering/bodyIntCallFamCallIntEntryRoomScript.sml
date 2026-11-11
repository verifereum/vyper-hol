Theory bodyIntCallFamCallIntEntryRoom
Ancestors
  exprLoweringProps intCallLookup compileVyper bodyIntCallFamCallIntEntryCharge
  bodyIntCallFamCallIntEntryCalleeCode

Theorem fmp_room_callee:
  !ctx caller callee s t.
    alloca_room ctx caller s /\ fmp_room ctx caller s /\
    fn_directly_calls ctx caller.fn_name callee.fn_name /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp ==>
    fmp_room ctx callee t
Proof
  rpt gen_tac >> rewrite_tac[alloca_room_def] >> strip_tac >>
  `TC (fn_directly_calls ctx) caller.fn_name callee.fn_name`
    by metis_tac[relationTheory.TC_RULES] >>
  `{g | TC (fn_directly_calls ctx) callee.fn_name g} SUBSET
   {g | TC (fn_directly_calls ctx) caller.fn_name g}`
    by (rw[pred_setTheory.SUBSET_DEF] >> metis_tac[relationTheory.TC_RULES]) >>
  `FINITE {g | TC (fn_directly_calls ctx) callee.fn_name g}`
    by metis_tac[pred_setTheory.SUBSET_FINITE] >>
  `CARD {g | TC (fn_directly_calls ctx) callee.fn_name g} <
   CARD {g | TC (fn_directly_calls ctx) caller.fn_name g}`
    by (irule pred_setTheory.CARD_PSUBSET >> simp[pred_setTheory.PSUBSET_MEMBER] >>
        qexists_tac `callee.fn_name` >> simp[]) >>
  rewrite_tac[fmp_room_def] >> strip_tac >>
  `s.vs_alloca_next + pending_alloca_size caller s +
     CARD {g | TC (fn_directly_calls ctx) caller.fn_name g} *
       unit_alloca_frame ctx <= w2n s.vs_fmp /\
   w2n s.vs_fmp + 2 ** 65 < dimword (:256)` by
    (qpat_x_assum `fmp_room _ _ _` mp_tac >>
     simp[fmp_room_def] >> impl_tac
     >- metis_tac[relationTheory.TC_RULES, venomInstTheory.lookup_function_MEM] >>
     simp[]) >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qmatch_asmsub_abbrev_tac `CARD below < CARD above` >>
  `pending_alloca_size callee t <= frame`
    by (simp[Abbr `frame`] >> irule pending_alloca_size_le_frame >>
        metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `frame * SUC (CARD below) <= frame * CARD above`
    by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  full_simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem setup_callee_rooms:
  !ctx caller callee s t args.
    alloca_room ctx caller s /\ fmp_room ctx caller s /\
    fn_directly_calls ctx caller.fn_name callee.fn_name /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    setup_callee callee args s = SOME t ==>
    alloca_room ctx callee t /\ fmp_room ctx callee t
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()] >>
     strip_tac >> gvs[]) >>
  conj_tac
  >- (irule alloca_room_callee >> metis_tac[]) >>
  irule fmp_room_callee >> metis_tac[]
QED

Theorem alloca_room_call_frame:
  !ctx caller s g charge.
    alloca_room ctx caller s /\
    fn_directly_calls ctx caller.fn_name g /\
    charge <= unit_alloca_frame ctx ==>
    s.vs_alloca_next + charge < dimword (:256)
Proof
  rpt gen_tac >> simp[alloca_room_def] >> strip_tac >>
  `TC (fn_directly_calls ctx) caller.fn_name g`
    by metis_tac[relationTheory.TC_RULES] >>
  `0 < CARD {g | TC (fn_directly_calls ctx) caller.fn_name g}` by
    (spose_not_then assume_tac >>
     `CARD {g | TC (fn_directly_calls ctx) caller.fn_name g} = 0` by decide_tac >>
     `{g | TC (fn_directly_calls ctx) caller.fn_name g} = {}` by
       metis_tac[pred_setTheory.CARD_EQ_0] >>
     gvs[pred_setTheory.EXTENSION]) >>
  `unit_alloca_frame ctx <=
    CARD {g | TC (fn_directly_calls ctx) caller.fn_name g} * unit_alloca_frame ctx`
    by (once_rewrite_tac[GSYM arithmeticTheory.MULT_LEFT_1] >>
        simp[arithmeticTheory.LE_MULT_RCANCEL]) >>
  decide_tac
QED

Theorem intcall_selected_allocs_ok:
  !tops ctx caller cx mut nr rr name args dflts ret ss.
    body_inv tops ctx caller cx /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
    fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,ss)
Proof
  rpt gen_tac >> simp[bodySimTheory.body_inv_def] >> strip_tac >>
  `MEM (mut,nr,rr,name,args,dflts,ret,ss)
    (FST (SND (classify_functions tops)))` by
    metis_tac[loweringShapePropsTheory.MEM_classify_internal] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- (irule lower_vyper_deploy_unit_allocs_ok >> metis_tac[]) >>
  irule lower_vyper_runtime_unit_allocs_ok >> metis_tac[]
QED

Theorem targeted_package_entry_stack_charge_le_frame:
  !tops target ut keys ctor il mut nr rr name args dflts ret body
    lbl ce params rb nr' key ut' view ctor' il' body' rt
    s ce2 rpc imm t func ctx.
    set_internal_package_target target
      (package_internal_fn tops ut keys ctor il
        (mut,nr,rr,name,args,dflts,ret,body)) =
      (lbl,ce,params,rb,nr',key,ut',view,ctor',il',body',rt) /\
    fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,body) /\
    ALL_DISTINCT (MAP FST args) /\
    compile_internal_function_entry ce params rb ctor' il' rt s =
      ((ce2,rpc,imm),t) /\
    fn_has_code s t func /\ MEM func ctx.ctx_functions ==>
    internal_stack_size ce params <= unit_alloca_frame ctx
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `set_internal_package_target target pkg` >>
  PairCases_on `pkg` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  gvs[set_internal_package_target_def] >>
  irule internal_entry_stack_charge_le_frame >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `_ = package_internal_fn _ _ _ _ _ _`
        (assume_tac o SYM) >>
      drule_all package_internal_fn_memloc_size_bound >> simp[]) >>
  qpat_x_assum `_ = package_internal_fn _ _ _ _ _ _` mp_tac >>
  simp[package_internal_fn_def] >> strip_tac >> gvs[] >>
  simp[listTheory.MAP_ZIP, compileEnvTheory.LENGTH_compute_pass_via_stack] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem intcall_selected_entry_charge:
  !tops ctx caller cx mut rr name args ret ss
    ut nk im lbl ce params rb nr key tr view ctor il body rt b ce2 rpc imm m callee.
    body_inv tops ctx caller cx /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    set_internal_package_target caller.ce_target
      (package_internal_fn tops ut nk caller.ce_is_ctor im
        (mut,F,rr,name,args,([]:expr list),ret,ss)) =
      (lbl,ce,params,rb,nr,key,tr,view,ctor,il,body,rt) /\
    compile_internal_function_entry ce params rb ctor il rt b =
      ((ce2,rpc,imm),m) /\
    fn_has_code b m callee /\
    lookup_function lbl ctx.ctx_functions = SOME callee ==>
    internal_stack_size ce params <= unit_alloca_frame ctx
Proof
  rpt gen_tac >> strip_tac >>
  `fn_allocs_ok tops (mut,F,rr,name,args,[],ret,ss)` by
    (irule intcall_selected_allocs_ok >> metis_tac[]) >>
  `supported_function_body tops Internal args ss` by
    (irule supportedProgramTheory.supported_program_function >>
     gvs[bodySimTheory.body_inv_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule supportedProgramTheory.supported_function_body_binding_contract >>
     simp[supportedNamesTheory.supported_function_bindings_def,
          listTheory.ALL_DISTINCT_APPEND]) >>
  irule targeted_package_entry_stack_charge_le_frame >>
  rpt (goal_assum (drule_at Any)) >>
  metis_tac[venomInstTheory.lookup_function_MEM]
QED

Theorem compiled_callee_setup_rooms:
  !ctx caller callee s argv ce params b m.
    alloca_room ctx caller s /\ fmp_room ctx caller s /\
    fn_directly_calls ctx caller.fn_name callee.fn_name /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    fn_has_code b m callee /\
    internal_stack_size ce params <= unit_alloca_frame ctx ==>
    ?t. setup_callee callee argv s = SOME t /\
        s.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
        alloca_room ctx callee t /\ fmp_room ctx callee t
Proof
  rpt gen_tac >> strip_tac >>
  `~NULL callee.fn_blocks` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fragExecTheory.fn_has_code_def] >> strip_tac >>
     Cases_on `callee.fn_blocks` >>
     gvs[venomInstTheory.lookup_block_def, listTheory.FIND_thm]) >>
  `?t. setup_callee callee argv s = SOME t` by
    simp[venomExecSemanticsTheory.setup_callee_def] >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule alloca_room_call_frame >> metis_tac[]) >>
  irule setup_callee_rooms >> metis_tac[]
QED

Theorem intcall_selected_callee_ready:
  !tops ctx caller cx mut rr name args ret ss.
    body_inv tops ctx caller cx /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops ==>
    ?ut nk im lbl ce params rb nr key tr view ctor il body rt b c callee
     ce2 rpc imm m.
      set_internal_package_target caller.ce_target
        (package_internal_fn tops ut nk caller.ce_is_ctor im
          (mut,F,rr,name,args,([]:expr list),ret,ss)) =
        (lbl,ce,params,rb,nr,key,tr,view,ctor,il,body,rt) /\
      lookup_function lbl ctx.ctx_functions = SOME callee /\
      compile_internal_function ce params rb nr key tr view ctor il body rt b =
        ((),c) /\ fn_has_code b c callee /\
      compile_internal_function_entry ce params rb ctor il rt b =
        ((ce2,rpc,imm),m) /\
      cs_extends b m /\ cs_extends m c /\ fn_has_code b m callee /\
      internal_stack_size ce params <= unit_alloca_frame ctx /\
      (!caller_fn s argv.
        alloca_room ctx caller_fn s /\ fmp_room ctx caller_fn s /\
        fn_directly_calls ctx caller_fn.fn_name lbl ==>
        ?t. setup_callee callee argv s = SOME t /\
            s.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
            alloca_room ctx callee t /\ fmp_room ctx callee t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_selected_callee_entry_code >> strip_tac >>
  `internal_stack_size ce params <= unit_alloca_frame ctx` by
    (irule intcall_selected_entry_charge >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiled_callee_setup_rooms >>
  rpt (goal_assum (drule_at Any)) >>
  metis_tac[vyperCompilerTheory.lookup_function_result_name]
QED
