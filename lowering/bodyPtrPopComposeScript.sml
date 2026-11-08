(*
 * pop_expr_ptr_ok's cases by the target's root, for bodyPtrPop:
 *   - a top-level name: bodyPtrPopRootCase's body_pop_root_ptr_ok;
 *   - a bare local: the seam bodyPtrPopSeamLocalRoot;
 *   - a nested target rooted at a module name (storage, transient,
 *     immutable, constant): no such pop is compiled into a supported
 *     runtime function (bodyPtrPopNestedSlot's
 *     pop_nested_module_root_exclusion);
 *   - a nested target rooted at a local: live (the seam
 *     bodyPtrPopSeamNestedLocalLive) or held only by the local's popped
 *     history (the residual bodyPtrPopResidualNestedLocalPopped).
 *
 * TOP-LEVEL:
 *   pop_vv_ptr_cases
 *)
Theory bodyPtrPopCompose
Ancestors
  bodyPtrPopSeamLocalRoot bodyPtrPopSeamNestedLocalLive
  bodyPtrPopResidualNestedLocalPopped bodyPtrPopNestedSlot
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs targetPlaceSim
  vyperInterpreter vyperState vyperAST

Theorem pop_target_root_cases[local]:
  !bt. (?id. target_root bt = NameTarget id) \/
       (?src id. target_root bt = TopLevelNameTarget (src,id))
Proof
  `(!e:expr. T) /\
   !bt. (?id. target_root bt = NameTarget id) \/
        (?src id. target_root bt = TopLevelNameTarget (src,id))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[target_root_def] >> Cases_on `p` >> simp[]
QED

(* A nested target rooted at a module name: the compiled pop can't be in
   a runtime function of a supported program. *)
Theorem pop_nested_module_root_vv_ptr[local]:
  !tops ctx cenv cx env ann bt ty es d PG func src name.
    body_inv tops ctx cenv cx /\
    (!x. bt <> NameTarget x) /\ (!nid. bt <> TopLevelNameTarget nid) /\
    target_root bt = TopLevelNameTarget (src,name) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> rewrite_tac[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  `cenv.ce_is_ctor <=> cx.in_deploy` by fs[body_inv_def] >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  PairCases_on `q` >>
  `F` suffices_by simp[] >>
  metis_tac[pop_nested_module_root_exclusion]
QED

(* A nested target rooted at a local: live or popped. *)
Theorem pop_nested_local_root_vv_ptr[local]:
  !tops ctx cenv cx env ann bt ty es d PG func id.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    (!x. bt <> NameTarget x) /\ target_root bt = NameTarget id /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  Cases_on `?s path t entry err v.
              eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
              lookup_scopes id t.scopes = SOME entry /\
              evaluate_subscripts entry.type entry.value path = INR err /\
              read_popped entry.type path entry.popped = SOME v`
  >- (fs[] >> metis_tac[pop_nested_local_popped_case_ptr]) >>
  `!s path t entry err.
     eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
     lookup_scopes id t.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE` by
    (rpt strip_tac >>
     Cases_on `read_popped entry.type path entry.popped` >> fs[] >>
     metis_tac[]) >>
  metis_tac[pop_nested_local_live_vv_ptr]
QED

(* Every target but a top-level name, by its root. *)
Theorem pop_vv_ptr_cases:
  !tops ctx cenv cx env ann bt ty es d PG func.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    (!nid. bt <> TopLevelNameTarget nid) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `?id. bt = NameTarget id`
  >- (gvs[] >> metis_tac[pop_local_root_vv_ptr]) >>
  `!x. bt <> NameTarget x` by metis_tac[] >>
  qspec_then `bt` strip_assume_tac pop_target_root_cases
  >- metis_tac[pop_nested_local_root_vv_ptr] >>
  metis_tac[pop_nested_module_root_vv_ptr]
QED
