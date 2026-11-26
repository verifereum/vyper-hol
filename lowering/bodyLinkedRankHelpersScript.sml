Theory bodyLinkedRankHelpers
Ancestors
  vyperInterpreter vyperContext alist list rich_list

(* Successful callable lookup identifies a member removed by the stack push. *)
Theorem body_callable_remcode_decreases:
  ~MEM (src,fn) cx.stk /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (dflts,ss) <> ([],[]) ==>
  LENGTH (remcode (cx with stk updated_by CONS (src,fn))) < LENGTH (remcode cx)
Proof
  strip_tac >>
  drule_all_then (qspec_then `src` assume_tac) lookup_callable_function_eq_ALOOKUP_module_fns >>
  fs[vyperContextTheory.get_module_code_def, AllCaseEqs()] >>
  drule_all ALOOKUP_FLAT_MAP_module_fns >> strip_tac >>
  qabbrev_tac `all_fns = FLAT (MAP (\(sid,tl). module_fns sid tl) mods)` >>
  `MEM ((src,fn),(dflts,ss)) all_fns` by
    (irule alistTheory.ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  `FILTER (\((sid,f),ss). ~MEM (sid,f) ((src,fn)::cx.stk)) all_fns =
     FILTER (\(k,ss). k <> (src,fn))
       (FILTER (\((sid,f),ss). ~MEM (sid,f) cx.stk) all_fns)` by
    (simp[rich_listTheory.FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM, pairTheory.FORALL_PROD]) >>
  simp[remcode_def, GSYM markerTheory.Abbrev_def] >>
  qpat_assum `FILTER _ all_fns = FILTER _ (FILTER _ all_fns)`
    (once_rewrite_tac o single o SIMP_RULE (srw_ss()) []) >>
  irule rich_listTheory.LENGTH_FILTER_LESS >>
  simp[EXISTS_MEM, MEM_FILTER] >>
  qexists_tac `((src,fn),(dflts,ss))` >> simp[]
QED
