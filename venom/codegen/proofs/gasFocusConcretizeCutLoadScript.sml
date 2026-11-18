Theory gasFocusConcretizeCutLoad
Ancestors concretizePtrExecutedCoverage[qualified,ignore_grammar] marker[qualified,ignore_grammar]
  concretizePtrMixedLoadTransport concretizePtrLoadTransport
  concretizePtrOrdinaryNext concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  concretizePtrLedgerProbe concretizePtrSourceOwnership
  concretizePtrRequestHistory concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizeStepStructure o1PassContract unitShapeDefs contextCodegenRel codegenRel stackPlanTypes
  ptrDiscipline unitLabelMapIdentity o1ContractSimplifyCfgSrcFrame
  venomExecSemantics venomState venomWf venomInst
  list finite_map words pred_set

Theorem ptr_focus_load_eval[local]:
  MEM inst.inst_opcode [MLOAD; ILOAD] /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] ==>
  step_inst fuel C inst s =
    case eval_operand op s of
      NONE => Error "undefined operand"
    | SOME x => OK (update_var out (mload (w2n x) s) s)
Proof
  simp[MEM] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def]
QED

Theorem ptr_focus_load_eval_some[local]:
  MEM inst.inst_opcode [MLOAD; ILOAD] /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ eval_operand op s = SOME x ==>
  step_inst fuel C inst s = OK (update_var out (mload (w2n x) s) s)
Proof
  strip_tac >>
  `step_inst fuel C inst s =
     case eval_operand op s of
       NONE => Error "undefined operand"
     | SOME y => OK (update_var out (mload (w2n y) s) s)` by
    (irule ptr_focus_load_eval >> simp[]) >>
  fs[]
QED

Theorem ptr_focus_iload_transport[local]:
  inst.inst_opcode = ILOAD /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  ptr_mixed_vars births positions TG tn f g s t /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
  (!k. k < 32 /\ w2n x + k NOTIN tn.t_mem ==>
    read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory) /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst fuel C inst s = OK s' /\
    ptr_mixed_vars births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) f g s' t'
Proof
  strip_tac >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
     (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ptr_mload_masked_value >> simp[]) >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def] >>
  irule ptr_mixed_vars_update >>
  simp[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
       set_prov_def, set_var_taint_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, ptr_value_transport_def] >>
  fs[ptr_mixed_vars_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]
QED

Theorem ptr_focus_load_chrono[local]:
  ptr_chrono_step C a z /\ MEM a.po_inst.inst_opcode [MLOAD; ILOAD] /\
  a.po_inst.inst_operands = [op] /\ a.po_inst.inst_outputs = [out] ==>
  ?y. eval_operand op a.po_state = SOME y /\
      z.po_stack = a.po_stack /\ z.po_fn = a.po_fn /\
      z.po_state = (update_var out (mload (w2n y) a.po_state) a.po_state
                     with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
      active_inst z.po_fn z.po_inst z.po_state
Proof
  strip_tac >>
  `!fuel. step_inst fuel C a.po_inst a.po_state =
     case eval_operand op a.po_state of
       NONE => Error "undefined operand"
     | SOME y => OK (update_var out (mload (w2n y) a.po_state) a.po_state)` by
    (gen_tac >> irule ptr_focus_load_eval >> simp[]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >> strip_tac >>
  gvs[MEM, is_terminator_def, AllCaseEqs()]
QED

(* The point read premise follows the actual source and target evaluations.
   Both read1 opcodes use the effective byte base w2n of that evaluation. *)
Theorem ptr_focus_load_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  MEM a.po_inst.inst_opcode [MLOAD; ILOAD] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  (!op x y k. a.po_inst.inst_operands = [op] /\
    eval_operand op a.po_state = SOME x /\ eval_operand op at.po_state = SOME y /\
    k < 32 /\ w2n x + k NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+k) a.po_state.vs_memory =
    read_byte (w2n y+k) at.po_state.vs_memory) ==>
  ?z TG'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule ptr_frame_context_membership >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule scfg_frame_reachable_active >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (qpat_x_assum `active_inst _ _ _`
       (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
     simp[fn_insts_MEM] >> qexists_tac `bb` >>
     qpat_assum `EL _ _ = _` (rewrite_tac o single o SYM) >> simp[EL_MEM]) >>
  `o1_fn_shape C a.po_fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `inst_wf a.po_inst /\ fn_shape_ok a.po_fn /\ wf_function a.po_fn` by
    (qpat_assum `o1_fn_shape _ _` (strip_assume_tac o REWRITE_RULE [o1_fn_shape_def]) >>
     qpat_x_assum `MEM a.po_inst (fn_insts a.po_fn)`
       (strip_assume_tac o REWRITE_RULE [fn_insts_MEM]) >>
     simp[] >> qpat_x_assum `fn_inst_wf _` (assume_tac o REWRITE_RULE [fn_inst_wf_def]) >>
     qpat_assum `!bb inst. _ ==> inst_wf inst` drule_all >> simp[]) >>
  `?op out. a.po_inst.inst_operands = [op] /\ a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `at.po_inst = a.po_inst` by (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  drule ptr_focus_load_chrono >> simp[] >>
  (impl_tac >- fs[MEM]) >> strip_tac >>
  suspend "execute"
QED

Resume ptr_focus_load_step[execute]:
  `~retpc_var a.po_fn out` by
    (fs[fn_shape_ok_def, retpc_shape_ok_def] >>
     spose_not_then assume_tac >>
     qpat_x_assum `!inst x. MEM inst (fn_insts a.po_fn) /\ MEM x inst.inst_outputs /\ retpc_var a.po_fn x ==> _`
       (qspecl_then [`a.po_inst`,`out`] mp_tac) >> simp[MEM]) >>
  `~is_label_operand op` by
    (`label_positions_ok a.po_inst` by
        (fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
     fs[MEM] >> gvs[label_positions_ok_def]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `?x. eval_operand op a.po_state = SOME x` by
    (drule_all ptr_mixed_vars_eval_presence >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >>
     Cases_on `eval_operand op a.po_state` >> gvs[]) >>
  `!k. k < 32 /\ w2n x + k NOTIN a.po_taint.t_mem ==>
     read_byte (w2n x+k) a.po_state.vs_memory =
     read_byte (w2n y+k) at.po_state.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!op x y k. _ ==> _` (qspecl_then [`op`,`x`,`y`,`k`] mp_tac) >>
     simp[]) >>
  qabbrev_tac `t' = update_var out (mload (w2n y) at.po_state) at.po_state` >>
  `step_inst 0 C' a.po_inst at.po_state = OK t'` by
    (simp[Abbr `t'`] >> irule ptr_focus_load_eval_some >> simp[]) >>
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
     ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
       (step_taint a.po_inst a.po_state post a.po_taint)
        a.po_fn at.po_fn post t'` by suspend "transport" >>
  suspend "attach"
QED

Resume ptr_focus_load_step[transport]:
  fs[MEM] >-
    (irule ptr_mixed_mload_transport_back >> simp[] >>
     qexistsl_tac [`C'`,`at.po_state`,`y`] >> simp[] >>
     Cases_on `op` >> fs[is_label_operand_def]) >>
  irule ptr_focus_iload_transport >> simp[] >>
  qexistsl_tac [`C'`,`at.po_state`,`y`] >> simp[]
QED

Resume ptr_focus_load_step[attach]:
  `post = update_var out (mload (w2n x) a.po_state) a.po_state` by
    (`step_inst 0 C a.po_inst a.po_state =
        OK (update_var out (mload (w2n x) a.po_state) a.po_state)` by
       (irule ptr_focus_load_eval_some >> simp[]) >> fs[]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >>
     fs[EVERY_MEM, is_terminator_def, wf_function_def, update_var_def] >>
     qexists_tac `a.po_inst` >> simp[is_terminator_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[wf_function_def, ptr_paired_code_def] >>
     metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "sample" >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (qpat_x_assum `ptr_paired_params positions a at _` mp_tac >>
     simp[ptr_paired_params_def, Abbr `z`, Abbr `t'`, ptr_ledger_next_def,
          ptr_observe_def, update_var_def]) >>
  qexists_tac `z` >> simp[] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, is_terminator_def,
       ptr_tagged_step_def, step_prov_def, out_prov_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def, MEM] >>
  fs[MEM, is_terminator_def, ptr_tagged_step_def, step_writes_def,
     source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  simp[Abbr `t'`, update_var_def] >>
  qexistsl [`0`, `post`] >> fs[update_var_def]
QED

Resume ptr_focus_load_step[sample]:
  simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  reverse conj_tac
  >- (fs[ptr_paired_sample_def] >> irule ptr_history_content_masks >>
      qexists_tac `a.po_taint` >>
      simp[step_taint_def, set_var_taint_def, store_taint_def,
           adopt_reset_def, imm_taint_def] >> gvs[Abbr `t'`]) >>
  qpat_x_assum `ptr_mixed_vars _ _ (step_prov _ _ _ _) _ _ _ _ _` mp_tac >>
  simp[Abbr `t'`] >>
  qpat_x_assum `MEM a.po_inst.inst_opcode [MLOAD; ILOAD]` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[MEM] >> strip_tac >>
  qpat_abbrev_tac `ps = update_var out (mload (w2n x) a.po_state) a.po_state` >>
  qpat_abbrev_tac `pt = update_var out (mload (w2n y) at.po_state) at.po_state` >>
  simp[step_prov_def, out_prov_def] >>
  simp[ptr_mixed_vars_def, ptr_opaque_env_def, lookup_var_def] >> metis_tac[]
QED

Finalise ptr_focus_load_step
