(* Classify the paired writes at an actual completed DLOADBYTES expansion. *)
Theory gasFocusLowerDloadBytesWrite
Ancestors
  gasFocusLowerDloadBytesCompletion lowerDloadPublicTrace lowerDloadCodeDataBytes
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyAssemblyPremises
  lowerDloadOracleCallAssembly o1SafeUpto

Theorem ld_focus_bytes_classified_write:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs s /\ ~in_revert_forward fn s /\
  ir_supply_covers_fn f.lf_supply fn /\ ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  t0.vs_inst_idx = p /\ ld_prefix C' gn X p 1 t0 t1 /\
  step_inst fuel C' (EL 1 X) t1 = OK u ==>
  ?ss bs dw dw' ow nw z v.
    step_inst 0 C inst s = OK ss /\ LENGTH X = 2 /\ ~MEM z (fn_ir_vars fn) /\
    t1 = ((update_var z v t0) with vs_inst_idx := p+1) /\
    eval_operand dest s = SOME dw /\ eval_operand off s = SOME ow /\ eval_operand len s = SOME nw /\
    LENGTH bs = w2n nw /\ bs = TAKE (w2n nw) (DROP (w2n ow) s.vs_data_section ++ REPLICATE (w2n nw) 0w) /\
    ss = write_memory_with_expansion (w2n dw) bs s /\ u = write_memory_with_expansion (w2n (dw' : 256 word)) bs t1 /\
    (bs = [] \/ (w2n dw = w2n dw' /\ w2n dw + LENGTH bs <= lo) \/
     (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\ w2n dw = b+delta /\ w2n dw' = c+delta /\ delta+LENGTH bs <= sz) \/
     (w2n dw = w2n dw' /\ dyn_floor C vs <= w2n dw))
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  qpat_x_assum `o1_safe_upto _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [o1_safe_upto_def]) >>
  `dload_offset_ok C fn inst s` by
    (first_x_assum (qspecl_then [`fn`,`inst`,`s`] mp_tac) >> simp[]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (qpat_x_assum `o1_ptr_safe_upto _ _ _ _ _` mp_tac >>
     simp[o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> strip_tac >>
     first_x_assum (qspecl_then [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`] mp_tac) >> simp[]) >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule_all ld_sync_fn_shape >> disch_then (strip_assume_tac o MATCH_MP o1_fn_shape_components) >>
  drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
  drule_all ld_dloadbytes_trace_operands >>
  disch_then (qx_choose_then `ow` (qx_choose_then `basew`
    (qx_choose_then `dw'` (qx_choose_then `nw` strip_assume_tac)))) >>
  drule ld_active_inst_member >> strip_tac >>
  drule ld_sync_ptr_ok >> strip_tac >>
  drule ld_sync_labels >> strip_tac >>
  drule ld_dloadbytes_source_operands >> simp[] >>
  disch_then drule >> simp[] >> disch_then (qspec_then `tn` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `dw` strip_assume_tac) >>
  drule_all ld_sync_source_code_layout_static >> strip_tac >>
  `eval_operand (Label "code_end") s = SOME basew` by
    fs[venomStateTheory.eval_operand_def] >>
  `t1.vs_code = s.vs_code` by
    (drule ld_sync_memory >> simp[lowerDloadSafetyKernelTheory.ld_nonghost_def]) >>
  `w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256)` by
    (qpat_x_assum `dload_offset_ok _ _ _ _`
       (qspecl_then [`off`,`ow`] mp_tac o REWRITE_RULE [lowerDloadDefsTheory.dload_offset_ok_def]) >>
     simp[]) >>
  qpat_x_assum `X = _` SUBST_ALL_TAC >>
  qabbrev_tac `a = <|inst_id := ai; inst_opcode := ADD;
                     inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>` >>
  qabbrev_tac `c = <|inst_id := ci; inst_opcode := CODECOPY;
                     inst_operands := [dest;Var z;len]; inst_outputs := []|>` >>
  `a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
   a.inst_outputs = [z] /\ c.inst_opcode = CODECOPY /\ c.inst_operands = [dest;Var z;len]`
    by simp[Abbr `a`, Abbr `c`] >>
  `step_inst fuel C' c t1 = OK u` by
    (qpat_x_assum `step_inst fuel C' (EL 1 [a;c]) t1 = OK u` mp_tac >> simp[]) >>
  `(!v. dest = Var v ==> v <> z) /\ (!v. len = Var v ==> v <> z)` by metis_tac[] >>
  drule_all ld_focus_bytes_actual_completion >>
  disch_then (REPEAT_TCL CHOOSE_THEN
    (CONJUNCTS_THEN2 assume_tac (assume_tac o CONJUNCT1))) >>
  `t1 = (update_var z (ow+basew) t0 with vs_inst_idx := p+1)` by
    (drule_all lowerDloadMacroBoundaryTheory.ld_macro_add_step >>
     disch_then (qspecl_then [`t0`,`0`,`C'`] mp_tac) >>
     simp[arithmeticTheory.ADD1] >> disch_tac >> gvs[]) >>
  `step_inst_base c t1 = OK u` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all ld_dloadbytes_codecopy_payload >>
  disch_then (qx_choose_then `bs` (qx_choose_then `ss` strip_assume_tac)) >>
  `step_inst 0 C inst s = OK ss` by gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule ld_sync_ghosts >> pure_rewrite_tac[listTheory.HD] >> strip_tac >>
  drule ld_sync_slots >> drule ld_sync_maps >> strip_tac >> strip_tac >>
  drule_all ld_sync_ambient_headroom >> strip_tac >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> pure_rewrite_tac[listTheory.HD] >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`dw`,`dw'`,`ow`,`nw`,`z`,`ow+basew`] >>
  qpat_x_assum `bs = TAKE _ _` (SUBST_ALL_TAC o SYM) >>
  `step_inst 0 C inst s = OK (write_memory_with_expansion (w2n dw) bs s)` by
    (qpat_assum `ss = write_memory_with_expansion _ _ _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  simp[] >>
  `tn.t_var = f.lf_tv` by simp[] >>
  qpat_x_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_tgt = t0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  drule_all (Q.INST [`fl` |-> `dyn_floor C vs`] ld_dloadbytes_destinations) >>
  disch_then (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
  simp[] >> metis_tac[]
QED
