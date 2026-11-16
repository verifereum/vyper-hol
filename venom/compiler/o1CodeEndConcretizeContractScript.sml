Theory o1CodeEndConcretizeContract
Ancestors
  o1ContractConcretize o1PassContract codegenSymRel o1ScheduleDecomp

Theorem concretize_code_end_contract_from_reflection:
  (!rpolicy D C Ct vs eom ft j t dst x sz w.
    ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
      (o1_walk_view rpolicy 2) C Ct /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_inv D 2 C vs /\
    ~ctx_has_dalloca C /\
    max_live_eom Ct = SOME eom /\ raw_reachable vs Ct ft j t /\
    j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
    code_end_var ft x /\ eval_operand (Var x) t = SOME w ==>
    ?f i s. raw_reachable vs C f i s /\ i.inst_opcode = CODECOPY /\
      i.inst_operands = [dst; Var x; sz] /\ code_end_var f x /\
      eval_operand (Var x) s = SOME w /\ s.vs_labels = t.vs_labels) ==>
  o1_stage_contract rpolicy D (EL 2 o1_fn_passes)
    (o1_walk_view rpolicy 2) (o1_pre 2)
    (\C s. o1_inv D 2 C s /\ ~ctx_has_dalloca C /\
      code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 3 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  strip_tac >>
  simp[o1_stage_contract_def] >> rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel (pass_fuel (EL 2 o1_fn_passes) C') D C C' s s /\
   o1_inv D 3 C' s` by
    (mp_tac (Q.SPECL [`C`, `C'`, `s`] o1_static_stage_concretize_mem_loc_headroom) >>
     simp[fmp_variant_room_def] >>
     impl_tac >- fs[o1_run_state_ok_def] >> metis_tac[]) >>
  simp[] >>
  `EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc` by EVAL_TAC >>
  `?eom. max_live_eom C' = SOME eom` by
    (fs[o1_inv_def, o1_static_inv_def] >> metis_tac[]) >>
  simp[code_end_offset_ok_def] >> rpt strip_tac >>
  `?f i u. raw_reachable s C f i u /\ i.inst_opcode = CODECOPY /\
     i.inst_operands = [dst; Var x; sz] /\ code_end_var f x /\
     eval_operand (Var x) u = SOME w /\ u.vs_labels = vs.vs_labels` by
    metis_tac[] >>
  fs[code_end_offset_ok_def] >> metis_tac[]
QED
