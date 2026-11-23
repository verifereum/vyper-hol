(* The root is instruction-free even when it extends the source storage
   trace. Its precise pure run supplies both the scoped outcome and the
   exclusion of an interior visit. *)
Theory entryCreateTargetPlace
Ancestors
  bodyFullTargetRoots bodyFullTargetDefs entryCreateCompositeFocus
  entryCreateFocusSpec entryCreateCompletedCut pair

Theorem target_root_outcome_scoped:
  target_root_outcome bundle tops cx st0 sa sb source (es,s,G,tn) Q R ==>
  scoped_operand_outcome bundle tops cx st0 sa sb source (es,s,G,tn) Q R
Proof
  PairCases_on `bundle` >>
  rw[target_root_outcome_def] >> irule scoped_operand_pure >>
  simp[create_operand_at_def] >> qexistsl_tac [`ee`,`res`] >> simp[]
QED

Definition target_sim_scoped_def:
  target_sim_scoped bundle cenv cx env bt es <=>
  target_sim_judgment scoped_operand_outcome bundle cenv cx env bt es
End

Theorem target_name_sim_scoped:
  target_pre cenv cx env (NameTarget id) es ==>
  target_sim_scoped (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (NameTarget id) es
Proof
  strip_tac >> simp[target_sim_scoped_def] >>
  irule target_sim_judgment_mono >> qexists_tac `target_root_outcome` >>
  simp[target_name_root_outcome, FORALL_PROD, target_root_outcome_scoped]
QED

Theorem target_toplevel_sim_scoped:
  target_pre cenv cx env (TopLevelNameTarget (src,id)) es ==>
  target_sim_scoped (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (TopLevelNameTarget (src,id)) es
Proof
  strip_tac >> simp[target_sim_scoped_def] >>
  irule target_sim_judgment_mono >> qexists_tac `target_root_outcome` >>
  simp[target_toplevel_root_outcome, FORALL_PROD, target_root_outcome_scoped]
QED

Theorem create_target_root_cut:
  ((?id. bt = NameTarget id) \/ (?nsid. bt = TopLevelNameTarget nsid)) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
  create_operand_at sa s ==>
  create_operand_cut sa sb explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> gvs[] >>
  FIRST [drule_then SUBST_ALL_TAC compile_target_name_no_code,
         drule_then SUBST_ALL_TAC compile_target_toplevel_no_code] >>
  simp[create_operand_cut_def, create_operand_empty_scope]
QED

Definition imm_target_place_sim_scoped_def:
  imm_target_place_sim_scoped bundle cenv cx env bt es <=>
  imm_target_place_sim_judgment scoped_operand_outcome bundle cenv cx env bt es
End

Theorem immutable_toplevel_target_sim_scoped:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  immutable_root cx (TopLevelNameTarget (NONE,id)) /\ ~cx_const_name cx (NONE,id) ==>
  imm_target_place_sim_scoped (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (TopLevelNameTarget (NONE,id)) es
Proof
  strip_tac >> simp[imm_target_place_sim_scoped_def] >>
  irule imm_target_place_sim_judgment_mono >>
  qexists_tac `target_root_outcome` >>
  simp[FORALL_PROD, target_root_outcome_scoped] >>
  irule immutable_toplevel_target_root_outcome >> metis_tac[]
QED
