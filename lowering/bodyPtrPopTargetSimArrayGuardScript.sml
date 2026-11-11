Theory bodyPtrPopTargetSimArrayGuard
Ancestors
  exprSimArrayIndex exprSimSubscriptArraySuffix bodyPtrBopScalarDynamic
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq emitHelperProps compileEnv loweringStateRelDefs exprLoweringProps
  exprLowering list pred_set finite_map ptrDiscipline

Theorem target_scalar_certificate_cons[local]:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op IN A) ops /\ tmp NOTIN R /\
  bop_scalar_seq R (Var tmp INSERT A) code B ==>
  bop_scalar_seq R A (mk_inst id opc ops [tmp] :: code) B
Proof
  strip_tac >> simp[Once bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id`, `opc`, `ops`, `tmp`] >> gvs[]
QED

Theorem target_bounds_valid_certificate_ptr:
  array_bounds_valid idx len sgn sa = (valid,sb) /\
  idx IN A /\ len IN A /\ Lit 0w IN A /\
  (!z. z IN R ==> not_fresh_at sa z) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ valid IN B
Proof
  strip_tac >>
  `!n. sa.cs_next_var <= n ==> STRING #"%" (toString n) NOTIN R` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
  simp[array_bounds_valid_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `sgn` >> gvs[comp_return_def] >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  rpt (irule_at Any target_scalar_certificate_cons >> simp[]) >>
  simp[bop_scalar_seq_def]
QED

Theorem target_bounds_check_certificate_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  idx IN A /\ len IN A /\ Lit 0w IN A /\
  (!z. z IN R ==> not_fresh_at sa z) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all target_bounds_valid_certificate_ptr >> strip_tac >>
  drule bop_scalar_seq_emit_assert >> simp[] >>
  disch_then (qspecl_then [`R`, `B`] mp_tac) >> simp[] >> strip_tac >>
  imp_res_tac emit_void_extends >>
  drule_all emitted_insts_append >> strip_tac >> simp[] >>
  irule_at Any bop_scalar_seq_append >> metis_tac[]
QED

Theorem target_bounds_check_path_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\ idx_in_range sgn i n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
       FLOOKUP H z = FLOOKUP G z /\ FLOOKUP un.t_var z = FLOOKUP tn.t_var z)
Proof
  strip_tac >> drule_all array_bounds_check_ok >> strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z} {idx;len;Lit 0w}
        (emitted_insts sa sb) B` by
    (irule target_bounds_check_certificate_ptr >> simp[] >> metis_tac[]) >>
  `!op. op IN {idx;len;Lit 0w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`ss'`, `G'`, `tn'`] >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem target_bounds_check_abort_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn i n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un fuel pc. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s fuel H un
      (Abort Revert_abort (t with vs_inst_idx := pc)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
       FLOOKUP H z = FLOOKUP G z /\ FLOOKUP un.t_var z = FLOOKUP tn.t_var z)
Proof
  strip_tac >> drule_all array_bounds_check_oob >> strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z} {idx;len;Lit 0w}
        (emitted_insts sa sb) B` by
    (irule target_bounds_check_certificate_ptr >> simp[] >> metis_tac[]) >>
  `!op. op IN {idx;len;Lit 0w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
