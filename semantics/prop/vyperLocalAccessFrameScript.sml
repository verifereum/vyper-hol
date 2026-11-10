(*
 * What expr_accesses says about a caller's locals at run time: evaluating
 * an expression changes the caller's local id only if the expression's own
 * accesses write it.  Only pop() writes a local inside an expression (the
 * length word of its target's root), and an internal call restores the
 * caller's scopes, so a callee's writes never reach them (callee_accesses
 * drops the callee's locals for that reason).
 *
 * TOP-LEVEL:
 *   eval_expr_unwritten_local, eval_exprs_unwritten_local
 *)

Theory vyperLocalAccessFrame
Ancestors
  vyperSubscriptOverlap vyperInterpreter vyperState vyperScopePreservation
  pair list rich_list vyperAST vyperContext vyperMisc vyperLookup
  vyperEvalExprPreservesScopesDom vyperStatePreservation vyperCallFrame
  vyperCreateFrame vyperPlaceFrames vyperStoragePlaceProvenance
Libs
  pairLib

(* Why it holds (a reader may ignore this): Pop ty tgt runs
   eval_target_place then pop_place, which changes scopes only on a
   MemoryPlace id0 path; that place comes from a target whose root is
   NameTarget id0, and accesses_target emits WriteAcc (LocalRef id0) for it,
   so id <> id0 and lookup_scopes_update_other applies.  IntCall evaluates
   its arguments in the caller's scopes and wraps defaults and body in
   finally ... set_scopes prev / pop_function prev, restoring scopes.
   lowering/targetSubscriptSplitScript.sml's target_subscript_nopop_scopes_mutual
   (no Pop => scopes unchanged) is the same induction with a stronger
   premise and conclusion; lowering/stmtSimAugAssignPlaceScript.sml's
   aug_place_name_root_memory is the MemoryPlace-root fact.  Both live in
   lowering/, which this theory can't import. *)

Theorem extend_place_memory_origin:
  extend_place cx r sb s = (INL (PlaceR (MemoryPlace id path)),t) ==>
  ?path0. r = PlaceR (MemoryPlace id path0)
Proof
  Cases_on `r` >> simp[extend_place_def, raise_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, extend_memory_place_def, bind_def,
           ignore_bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule extend_storage_place_subregion >> simp[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[value_type_CASE_rator, return_def, raise_def, bind_def, AllCaseEqs()]
QED

Theorem lookup_global_not_memory:
  !cx src id es es' root path.
    lookup_global cx src id es <> (INL (PlaceR (MemoryPlace root path)),es')
Proof
  rpt strip_tac >>
  gvs[lookup_global_def, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem eval_base_place_memory_access:
  !t cx st id path st'.
    eval_base_place cx t st = (INL (PlaceR (MemoryPlace id path)),st') ==>
    MEM (WriteAcc (LocalRef id)) (accesses_target t)
Proof
  measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def,
           type_check_def, assert_def, ignore_bind_def, return_def, raise_def,
           accesses_expr_def, AllCaseEqs()] >> rpt strip_tac >> gvs[])
  >- (PairCases_on `p` >> simp[Once evaluate_def] >>
      metis_tac[lookup_global_not_memory])
  >- (simp[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def] >>
      rpt strip_tac >> drule extend_place_memory_origin >>
      strip_tac >> gvs[] >> first_x_assum (qspec_then `b` mp_tac) >>
      simp[] >> metis_tac[])
  >> simp[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def] >>
  rpt strip_tac >> drule extend_place_memory_origin >>
  strip_tac >> gvs[] >> first_x_assum (qspec_then `b` mp_tac) >>
      simp[] >> metis_tac[]
QED

Theorem eval_target_place_memory_access:
  eval_target_place cx t st = (INL (MemoryPlace id path),st') ==>
  MEM (WriteAcc (LocalRef id)) (accesses_target t)
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_memory_access]
QED

Theorem pop_place_other_local:
  pop_place cx p st = (res,st') /\
  (!path. p <> MemoryPlace id path) ==>
  lookup_scopes id st'.scopes = lookup_scopes id st.scopes
Proof
  Cases_on `p`
  >- (rpt strip_tac >> drule_at (Pos last) pop_nonmemory_scopes >> simp[])
  >- (rpt strip_tac >> drule pop_memory_scope_trace_events >>
      strip_tac >>
      gvs[scope_pop_trace_def, scope_pop_step_def] >>
      drule find_containing_scope_structure >> strip_tac >>
      metis_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND,
                lookup_scopes_update_other]) >>
  rpt strip_tac >> drule_at (Pos last) pop_nonmemory_scopes >> simp[]
QED

Theorem accesses_exprs_unwritten:
  !es id. ~MEM (WriteAcc (LocalRef id)) (accesses_exprs es) <=>
    EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e)) es
Proof
  Induct >> simp[accesses_expr_def]
QED

Theorem accesses_named_exprs_map:
  !kes. accesses_named_exprs kes = accesses_exprs (MAP SND kes)
Proof
  Induct >> simp[accesses_expr_def, FORALL_PROD]
QED

Theorem unlock_if_nr_scopes:
  unlock_if_nr cx nr is_view st = (res,st') ==> st'.scopes = st.scopes
Proof
  Cases_on `nr /\ ~is_view` >>
  simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
  metis_tac[release_nonreentrant_lock_scopes]
QED

Theorem call_cleanup_scopes:
  finally source (ignore_bind (pop_function prev) (unlock_if_nr cx nr is_view))
    st = (res,st') ==> st'.scopes = prev
Proof
  strip_tac >> drule finally_pop_function_then_scopes >>
  impl_tac >- metis_tac[unlock_if_nr_scopes] >> simp[]
QED

Theorem evaluate_unwritten_local[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st' id.
    eval_expr cx e st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_expr e) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes) /\
  (!cx es st res st' id.
    eval_exprs cx es st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_exprs es) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes) /\
  (!cx bt st res st' id.
    eval_base_place cx bt st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_target bt) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes) /\
  (!cx bt st res st' id.
    eval_target_place cx bt st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_target bt) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st' id.
    eval_expr_results cx es st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_exprs es) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[accesses_expr_def]
  >- suspend "name"
  >- suspend "global"
  >- suspend "flag"
  >- suspend "ifexp"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "pop"
  >- suspend "typebuiltin"
  >- suspend "send"
  >- suspend "extcall"
  >- suspend "intcall"
  >- suspend "rawcall"
  >- suspend "rawcalldata"
  >- suspend "rawlog"
  >- suspend "rawrevert"
  >- suspend "selfdestruct"
  >- suspend "create"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- suspend "exprs"
  >- suspend "basename"
  >- suspend "baseglobal"
  >- suspend "baseattribute"
  >- suspend "basesubscript"
  >- suspend "target"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >> suspend "results"
QED

Resume evaluate_unwritten_local[name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED
Resume evaluate_unwritten_local[global]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  imp_res_tac lookup_global_scopes >> gvs[]
QED
Resume evaluate_unwritten_local[flag]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  imp_res_tac lookup_flag_mem_scopes >> gvs[]
QED
Resume evaluate_unwritten_local[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def,
      AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume evaluate_unwritten_local[struct]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def,
      accesses_named_exprs_map] >> metis_tac[]
QED
Resume evaluate_unwritten_local[subscript]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[attribute]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      Cases_on `bt = Env MsgGas` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >>
      imp_res_tac next_gas_reading_state >>
      imp_res_tac precompile_call_success_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      Cases_on `es` >>
      gvs[builtin_args_length_ok_def, accesses_expr_def] >> metis_tac[]) >>
  simp[Once evaluate_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, raise_def]
QED
Resume evaluate_unwritten_local[pop]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ (Pop _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> reverse strip_tac
  >- metis_tac[] >>
  rename1 `pop_place cx p mid = _` >>
  `!path. p <> MemoryPlace id path` by
    metis_tac[eval_target_place_memory_access] >>
  drule_all pop_place_other_local >> metis_tac[]
QED
Resume evaluate_unwritten_local[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[send]:
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac eval_send_preserves_non_accounts >>
  gvs[type_check_def, assert_def, return_def] >> metis_tac[]
QED
Resume evaluate_unwritten_local[extcall]:
  rpt strip_tac >>
  fs[accesses_exprs_unwritten] >>
  `EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
     (TAKE 1 es)` by metis_tac[EVERY_TAKE] >>
  `EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
     (TAKE (LENGTH (FST (SND sig))) (DROP 1 es))` by
    metis_tac[EVERY_TAKE, EVERY_DROP] >>
  `EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
     (DROP (LENGTH (FST (SND sig)) + 1) es)` by metis_tac[EVERY_DROP] >>
  fs[GSYM accesses_exprs_unwritten] >>
  qpat_x_assum `eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  metis_tac[]
QED
Resume evaluate_unwritten_local[intcall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, option_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac (call_cleanup_scopes |>
    Q.INST [`is_view` |-> `mut = View \/ mut = Pure`] |>
    SRULE [unlock_if_nr_def, ignore_bind_def]) >>
  imp_res_tac read_results_state >>
  gvs[get_scopes_def] >>
  rpt (qpat_x_assum `!a b c d. _` drule_all >> strip_tac) >>
  gvs[return_def, push_function_def] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >>
  simp[bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `cx.nonreentrant_slot` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED
Resume evaluate_unwritten_local[rawcall]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[rawcalldata]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[rawlog]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, push_log_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED
Resume evaluate_unwritten_local[rawrevert]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def] >>
  strip_tac >> metis_tac[]
QED
Resume evaluate_unwritten_local[selfdestruct]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, get_accounts_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac transfer_value_scopes >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[create]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[accesses_exprs_unwritten] >>
  `!n. EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
      (TAKE n es)` by metis_tac[EVERY_TAKE] >>
  `!n. EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
      (DROP n es)` by metis_tac[EVERY_DROP] >>
  `!n. EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
      (TAKE n (DROP 2 es))` by metis_tac[EVERY_TAKE, EVERY_DROP] >>
  `!n. EVERY (\e. ~MEM (WriteAcc (LocalRef id)) (accesses_expr e))
      (DROP n (DROP 2 es))` by metis_tac[EVERY_DROP] >>
  fs[GSYM accesses_exprs_unwritten] >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c d e f g h i j. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule >> strip_tac) >>
  rpt (qpat_x_assum `!a b c d. _` drule >> simp[] >> strip_tac) >>
  rpt (qpat_x_assum `!id'. _` (qspec_then `id` mp_tac) >> simp[] >> strip_tac) >>
  gvs[]
QED
Resume evaluate_unwritten_local[exprs]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[basename]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED
Resume evaluate_unwritten_local[baseglobal]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  imp_res_tac lookup_global_scopes >> gvs[]
QED
Resume evaluate_unwritten_local[baseattribute]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[basesubscript]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[target]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED
Resume evaluate_unwritten_local[results]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  metis_tac[]
QED
Finalise evaluate_unwritten_local

Theorem eval_expr_unwritten_local:
  !cx e st res st' id.
    eval_expr cx e st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_expr e) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes
Proof
  metis_tac[cj 5 evaluate_unwritten_local]
QED

Theorem eval_exprs_unwritten_local:
  !cx es st res st' id.
    eval_exprs cx es st = (res,st') /\
    ~MEM (WriteAcc (LocalRef id)) (accesses_exprs es) ==>
    lookup_scopes id st'.scopes = lookup_scopes id st.scopes
Proof
  metis_tac[cj 6 evaluate_unwritten_local]
QED
