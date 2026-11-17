Theory o1CodeEndMiddleTransport
Ancestors
  o1CodeEndConcretizeTransport o1CodeEndFmpTransport o1CodeEndSsaTransport
  o1CodeEndConcretizeLifetime o1CodeEndFmpLifetime
  o1PassContract venomPassSchedule venomInst ptrDiscipline list

Theorem code_end_middle_stage_contracts:
  ctx_pass_stage rpolicy (EL 2 o1_fn_passes) (o1_walk_view rpolicy 2) C2 C3 /\
  ctx_pass_stage rpolicy (EL 3 o1_fn_passes)
    (\C' f observed. o1_walk_view rpolicy 3 C' f observed /\
      EVERY fmp_sig_no_param observed.cu_context.ctx_functions) C3 C4 /\
  ctx_pass_stage rpolicy (EL 4 o1_fn_passes) (o1_walk_view rpolicy 4) C4 C5 /\
  o1_pre 2 C2 C3 /\ o1_pre 3 C3 C4 /\ o1_pre 4 C4 C5 /\
  o1_ctx_shape C2 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY no_raw_fmp_ops C2.ctx_functions /\
  EVERY no_raw_fmp_ops C3.ctx_functions /\
  dead_wf D /\ o1_run_state_ok s /\ o1_inv D 2 C2 s /\
  code_end_offset_ok (raw_reachable s) C2 /\
  EVERY (\f. !x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ d::j::b)) C2.ctx_functions ==>
  ctx_sim_fuel (pass_fuel (EL 2 o1_fn_passes) C3) D C2 C3 s s /\
  o1_inv D 3 C3 s /\ code_end_offset_ok (raw_reachable s) C3 /\
  ctx_sim_fuel (pass_fuel (EL 3 o1_fn_passes) C4) D C3 C4 s s /\
  o1_inv D 4 C4 s /\ code_end_offset_ok (raw_reachable s) C4 /\
  ctx_sim_fuel (pass_fuel (EL 4 o1_fn_passes) C5) D C4 C5 s s /\
  o1_inv D 5 C5 s /\ code_end_offset_ok (raw_reachable s) C5
Proof
  strip_tac >>
  `~ctx_has_dalloca C2` by
    (fs[no_raw_fmp_ops_def, ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >>
     metis_tac[is_raw_fmp_opcode_def]) >>
  `ctx_pass_stage rpolicy (EL 3 o1_fn_passes)
     (o1_walk_view rpolicy 3) C3 C4` by
    (qpat_x_assum `ctx_pass_stage _ (EL 3 _) _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  mp_tac concretize_code_end_run_contract >>
  simp[o1_stage_contract_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  mp_tac fmp_lowering_code_end_run_contract >>
  simp[o1_stage_contract_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc /\
   EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering /\
   EL 4 o1_fn_passes = CFP_Simple VP_MakeSSA` by EVAL_TAC >>
  fs[APPEND_ASSOC] >>
  drule_all (SRULE [] concretize_stage_protected_lifetime) >> strip_tac >>
  `EVERY (o1_fn_row 3) C3.ctx_functions` by fs[o1_pre_def] >>
  drule_all (SRULE [] fmp_stage_protected_lifetime) >> strip_tac >>
  mp_tac make_ssa_code_end_run_contract >>
  simp[o1_stage_contract_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
