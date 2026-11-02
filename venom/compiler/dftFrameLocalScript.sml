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
