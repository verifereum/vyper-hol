(* Live activation order and once-per-site scratch charges. *)
Theory lowerDloadLiveAllocation
Ancestors
  lowerDloadSafetyBoundary lowerDloadConfiguredOrigins
  ctxLookupAgreeHelpers fcgBridge venomFnScheduleRunnerProps
  list rich_list sorting venomInst o1PassContract venomFnScheduleRunner venomExecSemantics ptrDiscipline

Theorem active_invoke_target:
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) ==>
  MEM nm (fn_invoke_targets fn)
Proof
  rpt strip_tac >>
  `MEM inst (fn_insts fn)` by
    (drule_at Any EVERY_active_inst >>
     disch_then (qspec_then `\i. MEM i (fn_insts fn)` mp_tac) >> simp[EVERY_MEM]) >>
  gvs[fn_invoke_targets_def, fcgDefsTheory.fcg_scan_function_def,
    mem_get_invoke_targets, decode_invoke_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem frame_reachable_live_order:
  !vs0 C stk PG G tn fn inst s.
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  !names. callee_first names C.ctx_functions ==>
  MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
  SORTED (\f g. list_precedes f.fn_name g.fn_name names)
    (fn :: MAP (\f. f.cf_fn) stk)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (drule lookup_function_MEM >> simp[]) >>
  first_x_assum drule >> strip_tac
  >- (drule lookup_function_MEM >> strip_tac >>
      drule_all active_invoke_target >> strip_tac >>
      `list_precedes fn'.fn_name fn.fn_name names` by
        (drule lookup_function_selected_name >> strip_tac >>
         gvs[callee_first_def] >> metis_tac[]) >>
      gvs[SORTED_DEF, EVERY_MEM, MEM_MAP] >>
      metis_tac[list_precedes_transitive]) >>
  gvs[SORTED_DEF]
QED

Theorem frame_reachable_live_precedes:
  frame_reachable vs0 C stk PG G tn fn inst s /\
  callee_first names C.ctx_functions ==>
  !j k. j < k /\ k < LENGTH (fn :: MAP (\f. f.cf_fn) stk) ==>
    list_precedes (EL j (fn :: MAP (\f. f.cf_fn) stk)).fn_name
      (EL k (fn :: MAP (\f. f.cf_fn) stk)).fn_name names
Proof
  strip_tac >> drule_all frame_reachable_live_order >> strip_tac >>
  `transitive (\f g. list_precedes f.fn_name g.fn_name names)` by
    (simp[relationTheory.transitive_def] >> metis_tac[list_precedes_transitive]) >>
  drule SORTED_EL_LESS >>
  disch_then (qspec_then `fn :: MAP (\f. f.cf_fn) stk` mp_tac) >> simp[]
QED

Theorem frame_reachable_live_names_distinct:
  frame_reachable vs0 C stk PG G tn fn inst s /\
  callee_first names C.ctx_functions ==>
  ALL_DISTINCT (MAP (\f. f.fn_name) (fn :: MAP (\f. f.cf_fn) stk))
Proof
  strip_tac >> drule frame_reachable_live_precedes >>
  strip_tac >>
  simp[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> rpt strip_tac >>
  qmatch_goalsub_rename_tac `(EL a _).fn_name = (EL b _).fn_name` >>
  Cases_on `a = b` >- gvs[] >>
  `a < b \/ b < a` by decide_tac >>
  `LENGTH (fn :: MAP (\f. f.cf_fn) stk) = SUC (LENGTH stk)` by simp[] >>
  metis_tac[list_precedes_distinct]
QED
