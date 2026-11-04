(* Checker syntax boundary for read-only evaluation. *)
Theory vyperReadOnlySyntax
Ancestors
  vyperTypeContract vyperTypeContractStaticMaps vyperAST list rich_list
  vyperInterpreter vyperTypeContractGetter vyperTypeSelectedEntry
  vyperContext vyperLookupStorage

val _ = Parse.hide "body";

Theorem call_target_mutability_pure_view:
  call_target_mutability_ok mods Pure ct ==>
  call_target_mutability_ok mods View ct
Proof
  Cases_on `ct` >> simp[call_target_mutability_ok_def, call_mutability_ok_def] >>
  rename1 `IntCall ns` >> PairCases_on `ns` >>
  simp[call_target_mutability_ok_def] >>
  rpt CASE_TAC >> simp[call_mutability_ok_def]
QED

Theorem expr_target_mutability_view:
  (!mods mut e. (mut = Pure \/ mut = View) ==>
    expr_mutability_ok mods mut e ==> expr_mutability_ok mods View e) /\
  (!mods mut tgt. (mut = Pure \/ mut = View) ==>
    target_mutability_ok mods mut tgt ==> target_mutability_ok mods View tgt)
Proof
  ho_match_mp_tac expr_mutability_ok_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[Once expr_mutability_ok_def] >>
  rpt strip_tac >> gvs[call_mutability_ok_def, EVERY_MEM] >>
  simp[Once expr_mutability_ok_def, EVERY_MEM,
       call_mutability_ok_def, call_target_mutability_pure_view]
QED

Theorem write_mutability_view:
  (mut = Pure \/ mut = View) /\ write_mutability_ok mods mut tgt ==>
  write_mutability_ok mods View tgt
Proof
  simp[write_mutability_ok_def, call_mutability_ok_def] >>
  metis_tac[expr_target_mutability_view]
QED

Theorem atarget_mutability_view:
  !mods mut tgt. (mut = Pure \/ mut = View) ==>
  atarget_mutability_ok mods mut tgt ==> atarget_mutability_ok mods View tgt
Proof
  ho_match_mp_tac atarget_mutability_ok_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> simp[Once atarget_mutability_ok_def] >>
  rpt strip_tac >>
  gvs[EVERY_MEM] >>
  simp[Once atarget_mutability_ok_def, EVERY_MEM,
       write_mutability_view]
QED

Theorem iterator_mutability_view:
  (mut = Pure \/ mut = View) /\ iterator_mutability_ok mods mut iter ==>
  iterator_mutability_ok mods View iter
Proof
  Cases_on `iter` >> simp[iterator_mutability_ok_def] >>
  metis_tac[expr_target_mutability_view]
QED

Theorem reason_mutability_view:
  (!reason. (mut = Pure \/ mut = View) /\
    assert_reason_mutability_ok mods mut reason ==>
    assert_reason_mutability_ok mods View reason) /\
  (!reason. (mut = Pure \/ mut = View) /\
    raise_reason_mutability_ok mods mut reason ==>
    raise_reason_mutability_ok mods View reason)
Proof
  conj_tac >> Cases >>
  simp[assert_reason_mutability_ok_def, raise_reason_mutability_ok_def,
       EVERY_MEM] >> rpt strip_tac >>
  metis_tac[expr_target_mutability_view]
QED

Theorem stmt_mutability_view:
  (!mods mut stmt. (mut = Pure \/ mut = View) ==>
    stmt_mutability_ok mods mut stmt ==> stmt_mutability_ok mods View stmt) /\
  (!mods mut stmts. (mut = Pure \/ mut = View) ==>
    stmts_mutability_ok mods mut stmts ==> stmts_mutability_ok mods View stmts)
Proof
  ho_match_mp_tac stmt_mutability_ok_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> simp[Once stmt_mutability_ok_def] >>
  rpt strip_tac >> gvs[call_mutability_ok_def] >>
  simp[Once stmt_mutability_ok_def] >>
  metis_tac[expr_target_mutability_view, atarget_mutability_view,
    write_mutability_view, iterator_mutability_view, reason_mutability_view]
QED

Theorem checked_function_mutability:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
  function_mutability_ok mods vis mut nr dflts body
Proof
  rpt strip_tac >> drule_all check_contract_toplevel_decl_MEM >>
  simp[check_toplevel_decl_def]
QED

Theorem checked_function_read_only:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts /\
  (mut = Pure \/ mut = View) ==>
  EVERY (expr_mutability_ok mods View) dflts /\
  stmts_mutability_ok mods View body
Proof
  rpt strip_tac >> drule_all checked_function_mutability >>
  simp[function_mutability_ok_def, EVERY_MEM] >> rpt strip_tac >>
  metis_tac[expr_target_mutability_view, stmt_mutability_view]
QED

Theorem checked_internal_read_only:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) /\
  (mut = Pure \/ mut = View) ==>
  EVERY (expr_mutability_ok mods View) dflts /\
  stmts_mutability_ok mods View body
Proof
  rpt strip_tac >> drule lookup_callable_function_F_SOME_MEM >>
  strip_tac >> drule checked_function_read_only >>
  disch_then drule >> disch_then drule >> simp[]
QED

Theorem build_getter_mutability:
  !e kt vt n. expr_mutability_ok mods View e ==>
    expr_mutability_ok mods View (SND (SND (build_getter e kt vt n)))
Proof
  ho_match_mp_tac build_getter_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> simp[Once build_getter_def] >>
  rpt strip_tac >>
  simp[pairTheory.UNCURRY] >>
  gvs[Once expr_mutability_ok_def] >>
  rw[] >> gvs[expr_mutability_ok_def]
QED

Theorem getter_mutability:
  expr_mutability_ok mods View e /\
  getter e kt vt = (mut,nr,args,(dflts:expr list),ret,body) ==>
  stmts_mutability_ok mods View body
Proof
  simp[getter_def, pairTheory.UNCURRY] >> strip_tac >> gvs[] >>
  simp[stmt_mutability_ok_def] >> irule build_getter_mutability >> simp[]
QED

Theorem variable_getter_mutability[local]:
  external_getter_tuple src (VariableDecl vis vm id typ init) =
    SOME (mut,nr,args,(dflts:expr list),ret,body) ==>
  stmts_mutability_ok mods View body
Proof
  Cases_on `vis` >> simp[external_getter_tuple_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[stmt_mutability_ok_def, expr_mutability_ok_def] >>
  irule getter_mutability >> goal_assum (drule_at Any) >>
  simp[expr_mutability_ok_def]
QED

Theorem hashmap_getter_mutability[local]:
  external_getter_tuple src (HashMapDecl vis transient id kt vt init) =
    SOME (mut,nr,args,(dflts:expr list),ret,body) ==>
  stmts_mutability_ok mods View body
Proof
  Cases_on `vis` >> simp[external_getter_tuple_def] >> rpt strip_tac >>
  irule getter_mutability >> goal_assum (drule_at Any) >>
  simp[expr_mutability_ok_def]
QED

Theorem external_getter_mutability:
  external_getter_tuple src decl = SOME (mut,nr,args,(dflts:expr list),ret,body) ==>
  stmts_mutability_ok mods View body
Proof
  Cases_on `decl` >> simp[external_getter_tuple_def] >>
  metis_tac[variable_getter_mutability, hashmap_getter_mutability]
QED

Theorem selected_entry_read_only:
  check_contract F am.layouts tx.target mods = SOME art /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  (mut = Pure \/ mut = View) ==>
  stmts_mutability_ok mods View body
Proof
  rpt strip_tac >> drule selected_entry_checked_cases >>
  disch_then drule >>
  disch_then (qspec_then `find_function_module am tx.target tx.function_name` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >>~- ([`external_getter_tuple _ _ = SOME _`],
        drule external_getter_mutability >> simp[]) >>
  drule checked_function_read_only >> disch_then drule >>
  disch_then drule >> simp[]
QED

Theorem external_getter_defaults:
  external_getter_tuple src decl = SOME (mut,nr,args,(dflts:expr list),ret,body) ==>
  dflts = []
Proof
  Cases_on `decl` >> simp[external_getter_tuple_def]
  >- (rename1 `VariableDecl vis _ _ _ _` >> Cases_on `vis` >>
      simp[external_getter_tuple_def, getter_def, pairTheory.UNCURRY] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  rename1 `HashMapDecl vis _ _ _ _ _` >> Cases_on `vis` >>
  simp[external_getter_tuple_def, getter_def, pairTheory.UNCURRY]
QED

Theorem selected_entry_defaults_read_only:
  check_contract F am.layouts tx.target mods = SOME art /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  (mut = View \/ mut = Pure) ==>
  EVERY (expr_mutability_ok mods View) dflts
Proof
  rpt strip_tac >> drule selected_entry_checked_cases >>
  disch_then drule >>
  disch_then (qspec_then `find_function_module am tx.target tx.function_name` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >>~- ([`external_getter_tuple _ _ = SOME _`],
        drule external_getter_defaults >> simp[]) >>
  drule checked_function_read_only >> disch_then drule >>
  disch_then drule >> simp[]
QED

(* get_module_code_stk from vyperLookupStorage supplies stack transport. *)
Theorem context_internal_read_only:
  check_contract F layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) /\
  (mut = Pure \/ mut = View) ==>
  EVERY (expr_mutability_ok mods View) dflts /\
  stmts_mutability_ok mods View body
Proof
  strip_tac >> gvs[get_module_code_def] >>
  metis_tac[checked_internal_read_only]
QED

Theorem checked_context_stk[simp]:
  (ALOOKUP (cx with stk := stk').sources (cx with stk := stk').txn.target = SOME mods) =
  (ALOOKUP cx.sources cx.txn.target = SOME mods)
Proof
  simp[]
QED

Definition read_only_context_def:
  read_only_context mods cx <=>
    ~cx.in_deploy /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ?art. check_contract F cx.layouts cx.txn.target mods = SOME art
End

Theorem read_only_context_stk[simp]:
  read_only_context mods (cx with stk := stk') = read_only_context mods cx
Proof
  simp[read_only_context_def]
QED

Theorem read_only_context_callee:
  read_only_context mods cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
  (mut = View \/ mut = Pure) ==>
  EVERY (expr_mutability_ok mods View) dflts /\
  stmts_mutability_ok mods View body
Proof
  strip_tac >> gvs[read_only_context_def] >>
  drule context_internal_read_only >> disch_then drule >>
  disch_then drule >> disch_then drule >> simp[]
QED
