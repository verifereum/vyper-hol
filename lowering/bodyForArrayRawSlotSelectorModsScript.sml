(* Recover the syntactic slot root while the raw Array landing is available. *)
Theory bodyForArrayRawSlotSelectorMods
Ancestors
  bodyForArrayExprRunMods bodyForArraySelectionMods vyperStorageFootprint
  compileEnv context

Theorem for_array_raw_slot_selector_mods:
  contract_inv mods exps ctx c cx /\
  expr_body_pre_mods mods c cx env e es /\
  well_typed_iterator env sty (Array e) /\ expr_type e = ArrayT sty bd /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
          (INL raw,em with gas_obs := tail)) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
       for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx c env e vv sbExpr
         (es,sa0,s0,G0,tn0) H raw em Gu tu u) ==>
  (is_slot_addressed loc ==>
   ?tgt nid. loop_iterator_place e = SOME tgt /\
             target_root tgt = TopLevelNameTarget nid)
Proof
  strip_tac >> disch_tac >>
  fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def])) >>
  drule_all_then (qx_choose_then `et` (map_every assume_tac o CONJUNCTS))
    for_array_reached_selection_mods >>
  qpat_x_assum `(?tr slot p tgt src name tops. _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
      (DISJ_CASES_THEN2 strip_assume_tac
        (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)))
  >- (qexistsl_tac [`tgt`,`(src,name)`] >> simp[]) >>
  qpat_x_assum `is_slot_addressed _` mp_tac >>
  fs[vv_location_def,is_slot_addressed_def]
QED
