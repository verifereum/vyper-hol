(* Identify the two sides of the restored INVOKE before installing the
   callee frame. The saved heads are the actual caller states. *)
Theory gasFocusFmpCutInvokeSite
Ancestors
  gasFocusFmpStagePin fmpStageFmpStepsInvokePosition fmpStageRel
  o1PassContract contextCodegenRel venomExecSemantics venomExecProps
  venomInst venomState venomWf ptrDiscipline finite_map pred_set list

Theorem focus_fmp_cut_invoke_saved_site:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\ o1_pre 3 C3 C4 /\
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  lookup_function nm C3.ctx_functions = SOME callee /\
  callee.fn_fmp_signature = NONE /\
  active_inst fn ivk s /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom T stk PG G tn fn s lo t ts ==>
  fmp_saved_rel C4 sm fmp0 raw0
    (<|cf_fn := fn; cf_inst := ivk; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk) ((t,lo)::ts) /\
  ?fn' bb bb' j infos ctx runner callee' ci cc cr.
    lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx =
      fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
      (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
       then 1 else 0) /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    t.vs_inst_idx < LENGTH bb'.bb_instructions /\
    EL t.vs_inst_idx bb'.bb_instructions = j /\
    active_inst fn' j t /\ MEM j (fn_insts fn') /\
    j.inst_opcode = INVOKE /\ j.inst_id = ivk.inst_id /\
    lookup_function nm C4.ctx_functions = SOME callee' /\
    fn_entry_label callee' = fn_entry_label callee /\
    fmp_stage_lowered ci cc cr callee callee' /\
    (fn_is_context_entry cc callee <=> C3.ctx_entry = SOME nm)
Proof
  strip_tac >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_stage_rel_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (qx_choose_then `fn'` strip_assume_tac) strip_assume_tac)) >>
  conj_tac
  >- (simp[fmp_saved_rel_def] >> qexists `fn'` >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
   ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM, o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  `pre_fmp_ops callee` by
    (fs[o1_pre_def, EVERY_MEM, o1_fn_row_def] >> metis_tac[lookup_function_MEM]) >>
  drule_all focus_fmp_selected_root_pin >>
  disch_then (qx_choose_then `callee'` (qx_choose_then `ci`
    (qx_choose_then `cc` (qx_choose_then `cr` strip_assume_tac)))) >>
  drule_all fmp_frame_invoke_position >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (fs[active_inst_def] >> metis_tac[MEM_lookup_block]) >>
  `?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
         t.vs_inst_idx < LENGTH bb'.bb_instructions /\
         EL t.vs_inst_idx bb'.bb_instructions = j` by
    (fs[active_inst_def] >> metis_tac[MEM_lookup_block]) >>
  qhdtm_x_assum `fmp_frame_rel` mp_tac >>
  simp[fmp_frame_rel_def] >>
  disch_then (qx_choose_then `infos` (qx_choose_then `ctx`
    (qx_choose_then `runner` strip_assume_tac))) >>
  (metis_tac[])
QED
