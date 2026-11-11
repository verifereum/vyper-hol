Theory bodyIntCallImmutableFrame
Ancestors
  exprLoweringProps vyperImmutableMetadataFrame

(* Immutable values may change during a call, but separation depends only
   on their presence and declared type, not on their values. *)
Theorem immutable_alloca_sep_metadata_frame:
  immutable_alloca_sep func cenv cx es s /\
  immutable_metadata_frame es ee /\ ee.scopes = es.scopes ==>
  immutable_alloca_sep func cenv cx ee s
Proof
  rw[immutable_alloca_sep_def] >>
  `?imms. ALOOKUP es.immutables cx.txn.target = SOME imms` by
    (fs[immutable_metadata_frame_def] >>
     qpat_x_assum `!addr. IS_SOME _ <=> _`
       (qspec_then `cx.txn.target` mp_tac) >>
     Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
     Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[]) >>
  `?old. FLOOKUP (get_source_immutables cenv.ce_module imms) name =
           SOME (tv,old)` by
    (fs[immutable_metadata_frame_def] >>
     Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
     qpat_x_assum `!addr imms imms' src id. _`
       (drule_all_then (qspecl_then [`cenv.ce_module`,`name`] mp_tac)) >>
     Cases_on `FLOOKUP (get_source_immutables cenv.ce_module imms) name` >>
     gvs[] >> rename1 `FST pair = tv` >>
     Cases_on `pair` >> simp[]) >>
  qpat_x_assum `immutable_metadata_frame _ _` kall_tac >>
  gvs[] >> metis_tac[]
QED

Theorem eval_stmts_immutable_alloca_sep:
  eval_stmts cxf ss es = (res,ee) /\
  immutable_alloca_sep func cenv cx (es with scopes := prev) s ==>
  immutable_alloca_sep func cenv cx (ee with scopes := prev) s
Proof
  strip_tac >> drule (cj 2 eval_metadata_frame_mutual) >> strip_tac >>
  irule immutable_alloca_sep_metadata_frame >>
  qexists_tac `es with scopes := prev` >> simp[] >>
  fs[immutable_metadata_frame_def] >> metis_tac[]
QED
