(* The root is instruction-free even when it extends the source storage
   trace. Its precise pure run supplies both the scoped outcome and the
   exclusion of an interior visit. *)
Theory entryCreateTargetPlace
Ancestors
  bodyFullTargetRoots bodyFullTargetDefs entryCreateCompositeFocus
  entryCreateFocusSpec entryCreateCompletedCut entryCreateAdminSequence
  bodyFullTargetAttribute loweringShapeRules emitHelperProps emitHelper
  fragExec venomExecSemantics venomInst venomState abiEncoderProps
  exprLoweringProps gasSummary gasStorage
  vyperStorageFootprint vyperState fragGasOriginPtr arithmetic pair

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

(* The semantic supplier's exact update is the endpoint of this installed
   single-instruction slice, not just an arbitrary state at the exit PC. *)
Theorem create_target_field_add_scope:
  emit_op ADD [arg; Lit (n2w off)] a = (Var out,b) /\
  fn_has_code a b f /\ create_operand_at a s /\ ~s.vs_halted /\
  eval_operand arg s = SOME w ==>
  create_operand_full_scope a b E C f s []
    (OK (update_var out (w + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `SUC s.vs_inst_idx = LENGTH b.cs_current_insts` by
    fs[create_operand_at_def, ADD1] >>
  `!id. step_inst_base (mk_inst id ADD [arg; Lit (n2w off)]
          [STRING #"%" (toString a.cs_next_var)]) s =
        OK (update_var (STRING #"%" (toString a.cs_next_var)) (w + n2w off) s)` by
    (gen_tac >> irule step_ADD >> simp[eval_operand_def]) >>
  qpat_x_assum `SUC _ = LENGTH _` (fn th => PURE_REWRITE_TAC [th]) >>
  irule create_admin_sequence_scope >>
  simp[frag_ids_def, is_terminator_def, run_inst_seq_def, GSYM mk_inst_def] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem create_target_field_add_cut:
  emit_op ADD [arg; Lit (n2w off)] a = (dst,b) /\
  fn_has_code a b f /\ create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  irule create_admin_sequence_cut >> simp[mk_inst_def, is_terminator_def]
QED

Theorem create_target_field_add_scoped:
  emit_op ADD [arg; Lit (n2w off)] a = (Var out,b) /\
  fn_has_code a b f /\ create_operand_at a s /\ ~s.vs_halted /\
  eval_operand arg s = SOME w /\
  u = (update_var out (w + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK u,G',tn') /\
    Q H res (ee with gas_obs := []) G' tn' u) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    source (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[scoped_operand_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`ee`,`OK u`,`G'`,`tn'`] >>
  conj_tac >- (qpat_x_assum `u = _` SUBST_ALL_TAC >>
               irule create_target_field_add_scope >> simp[] >>
               qexists_tac `arg` >> simp[]) >>
  simp[gas_explicit_def] >> rpt strip_tac >> res_tac >> gvs[exit_result_def]
QED
