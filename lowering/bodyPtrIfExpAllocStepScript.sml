Theory bodyPtrIfExpAllocStep
Ancestors
  fragGasSeqPtr fragExecPtr allocationPtr fragGasPathPtr bodyPtrDefs
  venomExecProofs venomInstProofs venomExecSemantics venomInst venomState ptrSafeRun ptrDiscipline

Theorem alloca_counted_step:
  !D ctx fn PG G tn s bb id n out u.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id ALLOCA [Lit (n2w n)] [out]) s` by
    simp[ptr_inst_ok_alloca] >>
  `step_inst 0 ctx (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
  `(mk_inst id ALLOCA [Lit (n2w n)] [out]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id ALLOCA [Lit (n2w n)] [out]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  first_x_assum (qspec_then `PG` assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  simp[gas_path_ptr_rules]
QED

Theorem alloca_counted_step_covers:
  !D ctx fn PG G tn s bb id n out u cenv cx es.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) ==>
    ?G1 tn1 t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      t = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
      G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u /\
      tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn /\
      ptr_covers G1 tn1 out t n
Proof
  rpt strip_tac >>
  drule_all alloca_counted_step >> strip_tac >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  qexistsl_tac [`step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u`,
    `step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[ptr_covers_def, lookup_var_def] >>
  gvs[ptr_covers_def, lookup_var_def]
QED
