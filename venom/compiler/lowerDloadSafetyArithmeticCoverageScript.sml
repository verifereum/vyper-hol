(* Aggregated arithmetic effects, consumed by ordinary successor coverage. *)
Theory lowerDloadSafetyArithmeticCoverage
Ancestors
  lowerDloadArithmeticPointEffect
  lowerDloadSafetyScalarEffects lowerDloadSafetyAffineEffects lowerDloadSafetyShiftEffects
  lowerDloadSafetyOrdinaryCoverage lowerDloadOracleCallAssembly
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyAmbient
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline
  venomExecSemantics finite_map pred_set list

Theorem ld_sync_arithmetic_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ld_sync_taint_ok >> strip_tac >>
  drule_all ld_sync_arithmetic_effect_at >> simp[]
QED

Theorem ld_sync_arithmetic_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR] /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ld_pair lo P names Sigma C C' vs0 (ld_image f) ti
    (ts with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_sync_arithmetic_effect >> strip_tac >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >> strip_tac >>
  `~is_alloca_op inst.inst_opcode /\
   Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (rpt (qpat_x_assum `MEM inst.inst_opcode _` mp_tac) >> simp[] >>
     rpt strip_tac >>
     gvs[venomInstTheory.is_alloca_op_def, venomEffectsTheory.write_effects_def,
         venomEffectsTheory.empty_effects_def,
         codegenRelTheory.source_memory_write_ranges_def]) >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_dyn_agree_unwritten >> strip_tac >>
  irule ld_sync_ordinary_coverage >> metis_tac[]
QED
