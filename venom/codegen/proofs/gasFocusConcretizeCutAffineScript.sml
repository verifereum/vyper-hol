Theory gasFocusConcretizeCutAffine
Ancestors
  gasFocusConcretizeTaggedSupport concretizePtrAffineTransport
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrOrdinaryNext
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrSourceOwnership
  concretizePtrStructuralTrace concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrLedgerProbe
  concretizePtrParamSupport concretizeStepStructure concretizePtrOperationalOpcodes
  o1PassContract o1ScheduleDecomp ptrDiscipline pointerConfinedDefs
  contextCodegenRel codegenRel frameViewFacts unitLabelMapIdentity
  unitShapeDefs venomWf venomState venomInst venomExecSemantics opcodeClass
  finite_map list pred_set words

(* The mixed relation also tracks return-PC variables. The affine output is
   not one of those variables, and a scalar operand has zero displacement. *)
Theorem cut_affine_execution_back[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  ptr_nonopaque_operand f x /\ ptr_nonopaque_operand f y /\
  inst.inst_operands = [x;y] /\ inst.inst_outputs = [out] /\
  MEM inst.inst_opcode [ADD;SUB] /\
  (inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG y = NONE) /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK post ==>
  ?sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    post = update_var out tv t /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn)
      f g (update_var out sv s) post
Proof
  strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG x) {}
     (eval_operand x s) (eval_operand x t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  `ptr_lookup_transport births positions (op_prov TG y) {}
     (eval_operand y s) (eval_operand y t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  gvs[MEM] >>
  gvs[ptr_affine_step, exec_pure2_def, AllCaseEqs()] >>
  gvs[ptr_lookup_transport_some_right] >>
  qmatch_goalsub_abbrev_tac `update_var out sv s` >>
  qmatch_goalsub_abbrev_tac `update_var out tv t` >>
  qexistsl_tac [`sv`, `tv`] >> simp[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `op_prov TG x` >> Cases_on `op_prov TG y` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_scalar_empty,
      Abbr `sv`, Abbr `tv`] >>
  rpt conj_tac >> rpt strip_tac >>
  fs[ptr_mixed_vars_def, op_taint_def] >>
  metis_tac[ptr_value_transport_add_left, ptr_value_transport_add_right,
            ptr_value_transport_sub_right, WORD_ADD_COMM]
QED

Theorem cut_affine_provenance[local]:
  fn_ptr_ok P f /\ ptr_static_support P f TG /\
  MEM i (fn_insts f) /\ i.inst_operands = [x;y] /\
  MEM i.inst_opcode [ADD; SUB] ==>
  (i.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (i.inst_opcode = SUB ==> op_prov TG y = NONE)
Proof
  strip_tac >>
  `~(?u v. x = Var u /\ y = Var v /\ u IN fn_pv P f /\ v IN fn_pv P f) /\
    (i.inst_opcode = SUB ==> !v. y = Var v ==> v NOTIN fn_pv P f)` by
    (fs[fn_ptr_ok_def, affine_pointer_ops_def, fn_insts_MEM, fn_pv_def, MEM] >>
     metis_tac[]) >>
  Cases_on `x` >> Cases_on `y` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP TG s` >> gvs[ptr_static_support_def] >>
  Cases_on `FLOOKUP TG s'` >> gvs[] >> metis_tac[]
QED

Theorem ptr_focus_affine_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [ADD; SUB] /\ ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def] >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `?x y out. a.po_inst.inst_operands = [x;y] /\ a.po_inst.inst_outputs = [out]` by
    (`inst_wf a.po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
     fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `ptr_nonopaque_operand a.po_fn x /\ ptr_nonopaque_operand a.po_fn y /\
   op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {} /\
   (a.po_inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
   (a.po_inst.inst_opcode = SUB ==> op_prov TG y = NONE)` by suspend "operands" >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >> strip_tac >>
    drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  suspend "attach"
QED

Resume ptr_focus_affine_step[operands]:
  `opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `ptr_nonopaque_operand a.po_fn x /\ ptr_nonopaque_operand a.po_fn y` by
    (qpat_x_assum `EVERY (ptr_nonopaque_operand _) _` mp_tac >>
     asm_rewrite_tac[EVERY_DEF]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  drule_all cut_affine_provenance >> simp[] >> strip_tac >>
  fs[taint_ok_def, MEM] >>
  qpat_x_assum `!op. _ /\ op_taint _ op <> {} ==> _`
    (fn th => map_every (fn q => qspec_then q mp_tac th) [`x`,`y`]) >> simp[]
QED

Resume ptr_focus_affine_step[attach]:
  markerLib.RESUME_TAC >>
  `?v tv. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
     s' = update_var out tv at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v a.po_state))
       (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out v a.po_state) s'` by
    (fs[ptr_paired_sample_def] >>
     `a.po_state.vs_labels = at.po_state.vs_labels` by
       metis_tac[ptr_history_content_labels] >>
     irule cut_affine_execution_back >> rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl_tac [`C'`, `fuel`] >> simp[]) >>
  `?i. active_inst a.po_fn i
     ((update_var out v a.po_state) with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i (update_var out v a.po_state)` >>
  qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`, `rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >>
          irule ptr_history_content_masks >>
          goal_assum (drule_at Any) >>
          fs[MEM] >>
          simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])) >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
     simp[update_var_def]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def,
       ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl_tac [`0`, `update_var out v a.po_state`] >> fs[update_var_def])
QED

Finalise ptr_focus_affine_step
