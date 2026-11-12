(* Complete argument-head enrichment on the ordinary counted witness.
   The code/dynamic-array cases use the owner-held shared boundary. *)
Theory bodyIntCallHeadProducer
Ancestors
  bodyIntCallPostProvenance bodyIntCallProducerInterface
  bodyIntCallArgEligibility bodySim exprSimDefs exprSimMemDefs

Theorem intcall_arg_provenance:
  body_inv tops ctx cenv cx /\ body_expr_ok cx e /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `(?t' p. vv = LocatedValue t' p /\ p.ptr_location = LocCode) \/
    (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~dynarray_free tvt)`
  >- (irule intcall_arg_provenance_held >> simp[] >> metis_tac[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    (gvs[body_expr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >> disch_then drule_all >> strip_tac >>
  drule gas_outcome_strengthen_witness >>
  disch_then (qspec_then
    `\res ee t. !tv. res = INL tv ==>
       intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv vv t` mp_tac) >>
  impl_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_all vv_post_intcall_provenance >> simp[]) >>
  strip_tac >> irule gas_outcome_post_mono >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
