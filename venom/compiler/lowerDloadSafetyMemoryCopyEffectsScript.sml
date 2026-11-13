(* Snapshot memory copies at independently classified addresses. *)
Theory lowerDloadSafetyMemoryCopyEffects
Ancestors
  lowerDloadSafetyWriteBytes lowerDloadSafetyBytes lowerDloadSafetyAllocBounds
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline venomExecSemantics venomInst
  venomState memLocDefs codegenRel finite_map pred_set list byte words arithmetic

Theorem ld_mcopy_step[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [d;r;n] /\
  eval_operand d s = SOME dst /\ eval_operand r s = SOME src /\
  eval_operand n s = SOME len ==>
  step_inst_base inst s = OK (mcopy (w2n dst) (w2n src) (w2n len) s)
Proof
  strip_tac >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[]
QED

Theorem ld_mcopy_taint[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [d;r;n] /\
  inst.inst_outputs = [] /\ eval_operand d s = SOME dst /\
  eval_operand r s = SOME src /\ eval_operand n s = SOME len ==>
  step_taint inst s (mcopy (w2n dst) (w2n src) (w2n len) s) tn =
    tn with t_mem := (tn.t_mem DIFF {w2n dst+j | j < w2n len}) UNION
      {w2n dst+j | j < w2n len /\ w2n src+j IN tn.t_mem}
Proof
  strip_tac >>
  `{i | w2n dst <= i /\ i < w2n dst+w2n len} =
   {w2n dst+j | j < w2n len}` by
    (simp[EXTENSION] >> qx_gen_tac `i` >> eq_tac
     >- (strip_tac >> qexists_tac `i-w2n dst` >> decide_tac) >>
     strip_tac >> gvs[] >> decide_tac) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       mcopy_def, write_memory_with_expansion_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       FLOOKUP_DEF, DRESTRICT_UNIV, fixed_source_write_range_def,
       sized_source_write_range_def] >>
  gvs[EXTENSION] >> metis_tac[]
QED

Theorem ld_mcopy_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [d;r;n] /\
  inst.inst_outputs = [] /\
  eval_operand d f.lf_src = SOME dst /\
  eval_operand d f.lf_tgt = SOME dst' /\
  eval_operand r f.lf_src = SOME src /\
  eval_operand r f.lf_tgt = SOME src' /\
  eval_operand n f.lf_src = SOME len /\
  eval_operand n f.lf_tgt = SOME len /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  ld_dyn_agree fl tn.t_mem f.lf_src.vs_memory f.lf_tgt.vs_memory /\
  lo <= fl /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> u+z <= fl /\ v+z <= fl) /\
  ((w2n dst+w2n len <= lo /\ dst'=dst) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+w2n len <= sz) \/
   (dst'=dst /\ fl <= w2n dst)) /\
  ((w2n src+w2n len <= lo /\ src'=src) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n src=b+delta /\ w2n src'=c+delta /\ delta+w2n len <= sz) \/
   (src'=src /\ fl <= w2n src /\ w2n src + w2n len < dimword (:256))) /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_dyn_agree fl (step_taint inst f.lf_src ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
      (ld_erase A o_f f.lf_H) inst ss = ld_erase A o_f f.lf_H /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ss.vs_labels = f.lf_src.vs_labels /\
    ss.vs_return_pc_token = f.lf_src.vs_return_pc_token /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
    ts.vs_labels = f.lf_tgt.vs_labels /\
    ts.vs_return_pc_token = f.lf_tgt.vs_return_pc_token
Proof
  strip_tac >>
  `step_inst_base inst f.lf_src =
     OK (mcopy (w2n dst) (w2n src) (w2n len) f.lf_src)` by
    (irule ld_mcopy_step >> simp[]) >>
  `step_inst_base inst f.lf_tgt =
     OK (mcopy (w2n dst') (w2n src') (w2n len) f.lf_tgt)` by
    (irule ld_mcopy_step >> simp[]) >>
  `step_taint inst f.lf_src (mcopy (w2n dst) (w2n src) (w2n len) f.lf_src) tn =
     tn with t_mem := (tn.t_mem DIFF {w2n dst+j | j < w2n len}) UNION
       {w2n dst+j | j < w2n len /\ w2n src+j IN tn.t_mem}` by
    (irule ld_mcopy_taint >> simp[]) >>
  `!j. j < w2n len /\ w2n src+j NOTIN tn.t_mem ==>
    EL j (read_memory (w2n src) (w2n len) f.lf_src) =
    EL j (read_memory (w2n src') (w2n len) f.lf_tgt)` by
    (rpt strip_tac >> asm_rewrite_tac[] >> FIRST [
       (qpat_assum `fl <= w2n src` kall_tac >>
        irule ld_dyn_read_masked >> metis_tac[]),
       (qpat_assum `w2n src + w2n len <= lo` kall_tac >>
        irule ld_memory_read_low_masked >>
        metis_tac[]),
       (irule ld_memory_read_slot_masked >> conj_tac >- simp[] >>
        goal_assum (drule_at Any) >>
        metis_tac[])]) >>
  qabbrev_tac `M = {j | j < w2n len /\ w2n src+j IN tn.t_mem}` >>
  `{w2n dst+j | j < w2n len /\ w2n src+j IN tn.t_mem} =
   {w2n dst+j | j < w2n len /\ j IN M}` by simp[Abbr `M`, SF CONJ_ss] >>
  `!j. j < w2n len /\ j NOTIN M ==>
    EL j (read_memory (w2n src) (w2n len) f.lf_src) =
    EL j (read_memory (w2n src') (w2n len) f.lf_tgt)` by
    (rpt strip_tac >>
     qpat_assum `!j. j < w2n len /\ w2n src+j NOTIN tn.t_mem ==> _` irule >>
     qpat_x_assum `j NOTIN M` mp_tac >> fs[Abbr `M`]) >>
  `ld_dyn_agree fl
     ((tn.t_mem DIFF {w2n dst+j | j < w2n len}) UNION
       {w2n dst+j | j < w2n len /\ j IN M})
     (mcopy (w2n dst) (w2n src) (w2n len) f.lf_src).vs_memory
     (mcopy (w2n dst') (w2n src') (w2n len) f.lf_tgt).vs_memory` by
    (pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >>
     BETA_TAC >> irule ld_dyn_agree_write >>
     qexistsl_tac [`M`, `w2n len`, `tn`] >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
       (qpat_assum `fl <= w2n dst` kall_tac >> disj2_tac >> disj1_tac >>
        conj_tac >- (qpat_x_assum `dst' = dst` (fn th => rewrite_tac[th])) >>
        first_assum ACCEPT_TAC),
       (disj2_tac >> disj2_tac >> res_tac >> decide_tac)]) >>
  `ld_memory lo A
     (tn with t_mem := (tn.t_mem DIFF {w2n dst+j | j < w2n len}) UNION
       {w2n dst+j | j < w2n len /\ j IN M})
     (mcopy (w2n dst) (w2n src) (w2n len) f.lf_src)
     (mcopy (w2n dst') (w2n src') (w2n len) f.lf_tgt)` by
    (pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >>
     BETA_TAC >>
     FIRST [
       (qpat_assum `fl <= w2n dst` kall_tac >>
        qpat_x_assum `dst' = dst` SUBST_ALL_TAC >>
        irule ld_memory_write_high >> rpt conj_tac >>
        FIRST [qexistsl_tac [`M`, `w2n len`, `tn`] >> simp[] >> NO_TAC,
               decide_tac,
               rpt strip_tac >> res_tac >> decide_tac]),
       (qpat_assum `w2n dst + w2n len <= lo` kall_tac >>
        qpat_x_assum `dst' = dst` SUBST_ALL_TAC >>
        irule ld_memory_write_low >>
        conj_tac >- metis_tac[ld_alloc_bounds] >>
        qexistsl_tac [`M`, `w2n len`, `tn`] >>
        rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC]),
       (qpat_x_assum `w2n dst = _` (fn th => rewrite_tac[th]) >>
        qpat_x_assum `w2n dst' = _` (fn th => rewrite_tac[th]) >>
        irule ld_memory_write_slot >>
        conj_tac >- metis_tac[ld_alloc_bounds] >>
        qexistsl_tac [`M`, `k`, `w2n len`, `sz`, `tn`] >>
        rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
               rpt strip_tac >> metis_tac[ld_alloc_separate]])]) >>
  qexists_tac `mcopy (w2n dst) (w2n src) (w2n len) f.lf_src` >> gvs[] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         gvs[ld_vars_def, mcopy_def, write_memory_with_expansion_def] >> NO_TAC,
         gvs[ld_nonghost_def, mcopy_def, write_memory_with_expansion_def] >> NO_TAC,
         simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, mcopy_def,
              write_memory_with_expansion_def]]
QED
