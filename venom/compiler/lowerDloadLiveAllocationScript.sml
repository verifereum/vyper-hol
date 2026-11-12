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

Theorem sum_map_distinct_set[local]:
  !xs f. ALL_DISTINCT xs ==> SUM (MAP f xs) = SIGMA f (set xs)
Proof
  Induct >> simp[pred_setTheory.SUM_IMAGE_THM] >>
  rpt strip_tac >>
  `set xs DELETE h = set xs` by (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[]
QED

Theorem sum_map_sublist_bound:
  ALL_DISTINCT xs /\ set xs SUBSET set ys /\
  (!x. MEM x xs ==> f x <= g x) ==>
  SUM (MAP f xs) <= SUM (MAP g ys)
Proof
  strip_tac >>
  `SUM (MAP f xs) <= SIGMA g (set xs)` by
    (simp[sum_map_distinct_set] >>
     irule pred_setTheory.SUM_IMAGE_MONO_LESS_EQ >> simp[]) >>
  `SIGMA g (set xs) <= SIGMA g (set ys)` by
    (irule pred_setTheory.SUM_IMAGE_SUBSET_LE >> simp[]) >>
  mp_tac (Q.SPEC `ys` (Q.INST [`f` |-> `g`] SUM_IMAGE_LIST_TO_SET_upper_bound)) >>
  decide_tac
QED

Theorem subset_ids_card_bound:
  E SUBSET set (MAP id xs) ==> CARD E <= LENGTH xs
Proof
  strip_tac >>
  `CARD E <= CARD (set (MAP id xs))` by
    (irule pred_setTheory.CARD_SUBSET >> simp[]) >>
  mp_tac (Q.INST [`ls` |-> `MAP id xs`] CARD_LIST_TO_SET) >> simp[]
QED

Theorem live_scratch_charge_bound:
  ALL_DISTINCT frames /\ set frames SUBSET set C.ctx_functions /\
  (!fn. MEM fn frames ==> E fn SUBSET
    set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)))) ==>
  SUM (MAP (\fn. CARD (E fn)) frames) <= ctx_dload_count C
Proof
  strip_tac >> simp[lowerDloadDefsTheory.ctx_dload_count_def] >>
  irule sum_map_sublist_bound >> simp[] >>
  rpt strip_tac >> irule subset_ids_card_bound >>
  qexists_tac `\i. i.inst_id` >> simp[]
QED

Theorem live_scratch_charge_fresh_bound:
  ALL_DISTINCT (fn::frames) /\ set (fn::frames) SUBSET set C.ctx_functions /\
  (!f. MEM f (fn::frames) ==> E f SUBSET
    set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f)))) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = DLOAD /\
  inst.inst_id NOTIN E fn ==>
  CARD (E fn) + SUM (MAP (\f. CARD (E f)) frames) + 1 <= ctx_dload_count C
Proof
  strip_tac >>
  `FINITE (E fn)` by
    (irule pred_setTheory.SUBSET_FINITE >>
     qexists_tac `set (MAP (\i. i.inst_id)
       (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)))` >> simp[]) >>
  mp_tac (Q.INST [`frames` |-> `fn::frames`,
    `E` |-> `\f. if f = fn then inst.inst_id INSERT E f else E f`]
    live_scratch_charge_bound) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      Cases_on `fn' = fn` >> gvs[] >>
      simp[pred_setTheory.INSERT_SUBSET, MEM_MAP, MEM_FILTER] >>
      metis_tac[]) >>
  `MAP (\f. CARD (if f = fn then inst.inst_id INSERT E fn else E f)) frames =
   MAP (\f. CARD (E f)) frames` by
    (irule MAP_CONG >> gvs[] >> rpt strip_tac >>
     `x <> fn` by metis_tac[] >> simp[]) >>
  simp[pred_setTheory.CARD_INSERT] >> decide_tac
QED

Theorem frame_reachable_live_functions:
  frame_reachable vs0 C stk PG G tn fn inst s /\
  callee_first names C.ctx_functions ==>
  ALL_DISTINCT (fn :: MAP (\f. f.cf_fn) stk) /\
  set (fn :: MAP (\f. f.cf_fn) stk) SUBSET set C.ctx_functions
Proof
  strip_tac >>
  drule_all frame_reachable_live_names_distinct >> strip_tac >>
  drule_all frame_reachable_live_order >> strip_tac >>
  conj_tac >- metis_tac[ALL_DISTINCT_MAP] >>
  gvs[pred_setTheory.SUBSET_DEF, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

(* k=0 gives the synchronized frontier bound; k=1 reserves the fresh
   active scratch allocation.  Larger k can reserve an entire pending suffix. *)
Theorem scratch_charge_headroom:
  dload_headroom_ok C fn inst s /\ q + k <= ctx_dload_count C /\
  t.vs_alloca_next = s.vs_alloca_next + 32 * q ==>
  t.vs_alloca_next + 32 * k < dimword (:256)
Proof
  simp[lowerDloadDefsTheory.dload_headroom_ok_def] >> decide_tac
QED
