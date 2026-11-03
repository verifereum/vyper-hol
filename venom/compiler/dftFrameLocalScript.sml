(* Boundary probes for observation-sensitive local DFT simulation. *)
Theory dftFrameLocal
Ancestors
  dftFramePair dftFrameVars dftFrameLegal dftFrameFacts
  dftFrameSwap dftScheduleOrder venomInst venomEffects venomWf
  unitMemInv contextCodegenRel codegenRel unitShapeDefs dftDefs
  o1PassLift ctxLookupAgreeHelpers venomExecSemantics finite_map list
  unitLabelMapIdentity

Theorem dft_cross_allows_assert_before_mload:
  let a = mk_inst 0 ASSERT [Lit 0w] [];
      b = mk_inst 1 MLOAD [Lit 0w] ["x"]
  in dft_cross a b /\ dft_must_order a b
Proof
  EVAL_TAC >> simp[]
QED

Theorem dft_no_memory_effects_ranges:
  Eff_MEMORY NOTIN read_effects b.inst_opcode /\
  Eff_MEMORY NOTIN write_effects b.inst_opcode ==>
  inst_mem_ranges b s = []
Proof
  Cases_on `b.inst_opcode` >>
  simp[read_effects_def, write_effects_def, empty_effects_def,
       all_effects_def] >>
  rewrite_tac[inst_mem_ranges_def] >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
    [source_memory_read_ranges_def, TypeBase.case_def_of ``:opcode``] >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
    [source_memory_write_ranges_def, TypeBase.case_def_of ``:opcode``] >>
  simp[]
QED

Theorem dft_legal_fallible_unobserved:
  dft_legal_cross a b /\ inst_wf a /\ is_fallible a ==>
  inst_mem_ranges b s = [] /\ b.inst_opcode <> INVOKE
Proof
  strip_tac >> Cases_on `a.inst_opcode` >>
  gvs[is_fallible_def, opcode_fail_class_def] >>
  qpat_x_assum `dft_legal_cross a b` mp_tac >>
  simp[dft_legal_cross_def, dft_must_order_def] >> strip_tac >>
  gvs[read_effects_def, write_effects_def, empty_effects_def,
      all_effects_def] >>
  qpat_x_assum `inst_wf a` mp_tac >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
    [inst_wf_def, TypeBase.case_def_of ``:opcode``] >> strip_tac >>
  gvs[] >>
  `Eff_MEMORY NOTIN read_effects b.inst_opcode /\
   Eff_MEMORY NOTIN write_effects b.inst_opcode` by
    (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     metis_tac[]) >>
  simp[dft_no_memory_effects_ranges] >>
  Cases_on `b.inst_opcode = INVOKE` >>
  gvs[read_effects_def, all_effects_def]
QED

Theorem dft_legal_observed_predecessor_total:
  dft_swap_invariant s.vs_labels f /\
  fn_entry_label f = SOME s0.vs_current_bb /\
  frame_reach C f s0 a s /\ dft_legal_cross a b /\
  (inst_mem_ranges b u <> [] \/ b.inst_opcode = INVOKE) ==>
  ?t. step_inst fuel C a s = OK t
Proof
  strip_tac >>
  `active_inst f a s` by metis_tac[frame_reach_active] >>
  `MEM a (fn_insts f)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a` by
    (fs[dft_swap_invariant_def, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  `~is_fallible a` by metis_tac[dft_legal_fallible_unobserved] >>
  `~is_pseudo a.inst_opcode /\ ~is_terminator a.inst_opcode` by
    fs[dft_legal_cross_def, dft_cross_def] >>
  `a.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_fallible_def, opcode_fail_class_def]) >>
  irule dft_movable_step_total >> simp[] >>
  (conj_tac
   >- (fs[dft_swap_invariant_def, dft_labels_bound_def] >>
       metis_tac[]) >>
   conj_tac
   >- (rpt strip_tac >> irule dft_frame_reach_operands >>
       qexistsl [`C`, `f`, `a`, `s0`] >>
       fs[dft_swap_invariant_def] >>
       Cases_on `a.inst_opcode = PHI` >> gvs[is_pseudo_def]) >>
   fs[dft_swap_invariant_def, fn_shape_ok_def, EVERY_MEM])
QED

Theorem dft_wf_invoke_decode:
  inst_wf i /\ i.inst_opcode = INVOKE ==>
  ?nm ops. decode_invoke i = SOME (nm,ops)
Proof
  simp[inst_wf_def] >> strip_tac >> gvs[decode_invoke_def]
QED

Theorem dft_cross_step_mem_left:
  dft_cross a b /\ b.inst_opcode <> ALLOCA /\
  step_inst fuel C b s = OK t ==>
  mem_corr a s a (t with vs_inst_idx := n)
Proof
  strip_tac >>
  `~is_terminator b.inst_opcode /\ a.inst_opcode <> DRET` by
    (fs[dft_cross_def] >> metis_tac[is_terminator_def]) >>
  irule dft_mem_corr_same_inst >> simp[] >>
  drule_all dft_step_alloca_fields >> strip_tac >>
  `t.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_initial_fmp] >>
  simp[instIdxIndepTheory.eval_op_inst_idx] >>
  `DISJOINT (set (inst_defs b)) (set (inst_uses a))` by
    fs[dft_cross_def] >>
  metis_tac[dft_step_operand_agreement]
QED

Theorem dft_cross_step_mem_right:
  dft_cross a b /\ a.inst_opcode <> ALLOCA /\
  step_inst fuel C a s = OK t ==>
  mem_corr b (t with vs_inst_idx := n) b s
Proof
  strip_tac >>
  `~is_terminator a.inst_opcode /\ b.inst_opcode <> DRET` by
    (fs[dft_cross_def] >> metis_tac[is_terminator_def]) >>
  irule dft_mem_corr_same_inst >> simp[] >>
  drule_all dft_step_alloca_fields >> strip_tac >>
  `t.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_initial_fmp] >>
  simp[instIdxIndepTheory.eval_op_inst_idx] >>
  `DISJOINT (set (inst_defs a)) (set (inst_uses b))` by
    fs[dft_cross_def] >>
  metis_tac[dft_step_operand_agreement]
QED

Theorem dft_fold_execution_frame[local]:
  !pairs s. execution_frame
    (FOLDL (\st (out,value). update_var out value st) s pairs) =
    execution_frame s
Proof
  Induct >- simp[] >> Cases_on `h` >>
  asm_simp_tac std_ss [FOLDL, stateFrameTheory.frame_update_var]
QED

Theorem dft_empty_effect_step_frame:
  inst_wf p /\ inst_shape_ok p /\
  ~is_terminator p.inst_opcode /\ p.inst_opcode <> ALLOCA /\
  p.inst_opcode <> INVOKE /\ ~is_ext_call_op p.inst_opcode /\
  write_effects p.inst_opcode = {} /\ read_effects p.inst_opcode = {} /\
  step_inst fuel C p s = OK t ==> execution_frame t = execution_frame s
Proof
  strip_tac >>
  `step_inst_base p s = OK t` by gvs[step_inst_non_invoke] >>
  drule_at (Pat `step_inst_base _ _ = OK _`) dft_empty_read_replay >>
  disch_then (qspec_then `s` mp_tac) >>
  asm_simp_tac std_ss [] >> strip_tac >>
  metis_tac[dft_fold_execution_frame]
QED

Theorem dft_invoke_cross_effects:
  effects_independent INVOKE p.inst_opcode ==>
  read_effects p.inst_opcode = {} /\ write_effects p.inst_opcode = {} /\
  p.inst_opcode <> INVOKE /\ ~is_ext_call_op p.inst_opcode
Proof
  simp[effects_independent_def, read_effects_def, write_effects_def,
       all_effects_def] >> strip_tac >>
  Cases_on `p.inst_opcode` >>
  gvs[read_effects_def, write_effects_def, empty_effects_def,
      is_ext_call_op_def, all_effects_def]
QED

Theorem dft_independent_step_call:
  effects_independent i.inst_opcode p.inst_opcode /\
  DISJOINT (set (inst_defs p)) (set (inst_uses i)) /\
  inst_wf i /\ inst_wf p /\ inst_shape_ok p /\
  ~is_terminator p.inst_opcode /\ p.inst_opcode <> ALLOCA /\
  step_inst fuel C p s = OK t ==>
  call_corr i s i (t with vs_inst_idx := n)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (`read_effects p.inst_opcode = {} /\
       write_effects p.inst_opcode = {} /\ p.inst_opcode <> INVOKE /\
       ~is_ext_call_op p.inst_opcode` by metis_tac[dft_invoke_cross_effects] >>
      `execution_frame t = execution_frame s` by
        metis_tac[dft_empty_effect_step_frame] >>
      `?nm ops. decode_invoke i = SOME (nm,ops)` by
        metis_tac[dft_wf_invoke_decode] >>
      irule dft_call_corr_decoded >>
      asm_simp_tac std_ss [stateFrameTheory.execution_frame_updates] >>
      `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
        metis_tac[dft_step_operand_agreement] >>
      `i.inst_operands = Label nm :: ops` by
        (gvs[decode_invoke_def, AllCaseEqs()] >> Cases_on `h` >> gvs[]) >>
      simp[instIdxIndepTheory.eval_op_inst_idx]) >>
  simp[call_corr_def]
QED

Theorem dft_call_corr_same_reverse_index:
  call_corr i s i t ==> call_corr i (t with vs_inst_idx := n) i s
Proof
  simp_tac std_ss [call_corr_def, stateFrameTheory.execution_frame_updates,
                   instIdxIndepTheory.eval_ops_inst_idx] >>
  metis_tac[]
QED

Theorem dft_cross_step_observation_left:
  dft_cross a b /\ inst_wf a /\ inst_wf b /\
  inst_shape_ok a /\ inst_shape_ok b /\
  a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA /\
  step_inst fuel C b s = OK t ==>
  mem_corr a s a (t with vs_inst_idx := n) /\
  call_corr a s a (t with vs_inst_idx := n)
Proof
  strip_tac >> conj_tac
  >- metis_tac[dft_cross_step_mem_left] >>
  irule dft_independent_step_call >>
  metis_tac[dft_cross_effects, dft_cross_def]
QED

Theorem dft_cross_step_observation_right:
  dft_cross a b /\ inst_wf a /\ inst_wf b /\
  inst_shape_ok a /\ inst_shape_ok b /\
  a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA /\
  step_inst fuel C a s = OK t ==>
  mem_corr b (t with vs_inst_idx := n) b s /\
  call_corr b (t with vs_inst_idx := n) b s
Proof
  strip_tac >> conj_tac
  >- metis_tac[dft_cross_step_mem_right] >>
  irule dft_call_corr_same_reverse_index >>
  `effects_independent b.inst_opcode a.inst_opcode` by
    (drule dft_cross_effects >>
     simp[effects_independent_def, pred_setTheory.DISJOINT_UNION] >>
     metis_tac[pred_setTheory.DISJOINT_SYM]) >>
  `call_corr b s b (t with vs_inst_idx := t.vs_inst_idx)` by
    (irule dft_independent_step_call >>
     metis_tac[dft_cross_def]) >>
  fs[]
QED
