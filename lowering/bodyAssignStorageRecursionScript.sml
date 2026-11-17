(* Temporary worker: storage-result shape recursion. *)
Theory bodyAssignStorageRecursion
Ancestors
  bodyAssignStorageShape vyperPlaceResultTyping vyperState vyperInterpreter
  bodySim exprLowering context compileEnv vyperAST exprSimHyps pair

Theorem body_assign_select_nonvalue[local]:
  (!v. raw <> Value v) /\
  select_result cx ty raw sub st = (INL out,st') ==>
  !v. out <> Value v
Proof
  Cases_on `raw` >> simp[select_result_def] >> rpt strip_tac >>
  drule extend_place_result_shape >> strip_tac >> gvs[]
QED

Theorem body_assign_storage_result_shape_from_cases:
  body_inv tops ctx cenv cx /\
  (!e ty sa t p sb.
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
    (case e of TopLevelName _ _ => T | Pop _ _ => T |
       Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)) /\
  (!e ty sa t p sb es pv es1.
    (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)) ==>
  !e ty sa t p sb es pv es1.
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >> measureInduct_on `expr_size e` >>
  rpt gen_tac >> disch_tac >>
  `case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F` by metis_tac[] >>
  Cases_on `case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F`
  >- (qpat_x_assum `!e ty sa t p sb es pv es1. _` irule >>
      metis_tac[]) >>
  qpat_x_assum `!e ty sa t p sb es pv es1. _` kall_tac >>
  qpat_x_assum `!e ty sa t p sb. _` kall_tac >>
  Cases_on `e` >> gnvs[] >>
  qpat_x_assum `_ /\ _` (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_subscript_storage_origin >>
      simp[] >> strip_tac >>
      `~subscript_reads_base cx e' e0` by
        metis_tac[body_inv_copies_subscript_base] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_attribute_storage_origin >>
      simp[] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
QED
