(* Source progress and the residual-run coverage constructor. *)
Theory fmpStageCoverPointBase
Ancestors
  fmpStageCoverInv fmpStageOpBase fmpStageRel
  o1LowerDloadReadiness o1PassContract ptrDiscipline contextCodegenRel
  venomStepProps venomInstProps venomExecSemantics venomExecProps venomWf
  venomState venomInst finite_map words list

Theorem fmp_cov_source_next:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK s1 ==>
  ?inst2.
    frame_reachable vs C stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~(s1 with vs_inst_idx := SUC s.vs_inst_idx).vs_halted
Proof
  rpt strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qexists_tac `inst2` >> simp[] >>
  conj_tac >- metis_tac[frame_reachable_next] >>
  metis_tac[step_inst_ok_halted]
QED

Theorem fmp_cov_endpoint_next:
  (!fn' C' name ti t fuel t2 n u.
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
    ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' name t n u) ==>
    !k. fmp_target_run k C' name
      (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u) /\
  ALL_DISTINCT (fn_labels fn') /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\ 0 < n /\
  (!k. fmp_target_run k C' fn.fn_name t n u) /\
  t.vs_current_bb = u.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx + n /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/
               is_terminator inst.inst_opcode) /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo u ts /\
  fmp_cov_stack C' stk ts stk' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  (!i. SUC t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
    i < LENGTH bb'.bb_instructions /\
    fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode) ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  `t2.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `!k. fmp_target_run k C' fn.fn_name
      (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u` by
    (first_x_assum irule >> metis_tac[]) >>
  simp[fmp_cov_def] >> disj1_tac >>
  qexistsl_tac [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`,
                 `u`, `ts`, `restored`, `bb'`] >>
  simp[] >>
  gvs[] >>
  `n + t.vs_inst_idx - SUC t.vs_inst_idx = n - 1` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[]
QED
