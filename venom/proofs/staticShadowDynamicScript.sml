Theory staticShadowDynamic
Ancestors
  staticShadowFrame staticShadowPrim staticShadowDefs venomExecSemantics
  venomState venomInst list
Libs
  stepInstBaseLib

Theorem static_shadow_pack_dret:
  !pairs cursor s sh ptrs final s'.
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  pack_dret_dynamic cursor pairs s = (ptrs,final,s') ==>
  ?sh'. pack_dret_dynamic cursor pairs sh = (ptrs,final,sh') /\
        static_shadow_rel s' sh' /\ s'.vs_call_ctx.cc_static
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  gvs[pack_dret_dynamic_def, AllCaseEqs()] >>
  qpat_x_assum `(\(ptrs,final_cursor,s2). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `static_shadow_rel (mcopy (w2n cursor) (w2n h0) (w2n h1) s)
                     (mcopy (w2n cursor) (w2n h0) (w2n h1) sh)` by
    simp[static_shadow_memory_writes] >>
  `(mcopy (w2n cursor) (w2n h0) (w2n h1) s).vs_call_ctx.cc_static` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem static_shadow_dret:
  inst.inst_opcode = DRET /\ s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!ops. eval_operands ops sh = eval_operands ops s` by
    metis_tac[static_shadow_rel_eval_operands] >>
  `sh.vs_call_entry_fmp = s.vs_call_entry_fmp` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  with_opcode_clause simp >>
  Cases_on `inst.inst_outputs = []` >> simp[static_shadow_result_rel_def] >>
  Cases_on `parse_dret_shape inst` >> simp[static_shadow_result_rel_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) x))` >>
  simp[static_shadow_result_rel_def] >>
  pairarg_tac >> simp[] >>
  drule_all static_shadow_pack_dret >> strip_tac >> simp[] >>
  simp[static_shadow_rel_updates]
QED
