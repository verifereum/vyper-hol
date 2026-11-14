(* Runtime and ghost frames for the constructive scalar suffix. *)
Theory bodyPtrBopScalarOutcome
Ancestors bodyPtrBopScalarRun bodyPtrBopScalarDispatch bodyPtrBopScalarSeq
  bodyPtrBopScalarStep bodyPtrBopAssert bodyPtrDefs exprSimPtrProps
  fragGasSeqPtr gasSummaryComposePtr gasStorage vyperStorageFootprint
  bodyPtrBopScalarDynamic fragExec rich_list exprLoweringProps
  appendStorageGhostPtr emitHelperProps freshWrites ptrDiscipline
  exprBopSimProps exprSimDefs fragGasPathPtr fragGasCopyLoop
  fragGasOriginPtr fragExecMem instMemFrontier
  venomExecSemantics venomState venomInst finite_map list pred_set

Theorem bop_scalar_seq_outputs:
  !code R A B i. bop_scalar_seq R A code B /\ MEM i code ==>
    MEM i.inst_opcode
      [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
       EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
       SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN; ASSERT; ASSERT_UNREACHABLE] /\
    (!x. x IN R ==> ~MEM x i.inst_outputs)
Proof
  Induct >> simp[Once bop_scalar_seq_def] >> rpt strip_tac >>
  gvs[mk_inst_def] >> metis_tac[]
QED

Theorem bop_scalar_inst_protected_frame:
  MEM i.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
     SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN; ASSERT; ASSERT_UNREACHABLE] /\
  step_inst_base i s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. ~MEM x i.inst_outputs ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> Cases_on `i.inst_opcode = ASSIGN`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[step_inst_base_opcode_eqs] >>
      Cases_on `i.inst_operands` >> simp[] >>
      Cases_on `t'` >> simp[] >>
      Cases_on `eval_operand h s` >> simp[] >>
      Cases_on `i.inst_outputs` >> simp[] >>
      Cases_on `t'` >> simp[] >>
      strip_tac >> gvs[update_var_def, FLOOKUP_UPDATE] >>
      simp[venom_state_component_equality]) >>
  irule step_pure_opcode_frame >> simp[] >> Cases_on `i.inst_opcode` >> gvs[]
QED

Theorem bop_scalar_seq_runtime_frame:
  bop_scalar_seq R A code B /\ run_inst_seq code s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. x IN R ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> ho_match_mp_tac run_inst_seq_protected_frame >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  rpt strip_tac >>
  drule_all bop_scalar_seq_outputs >> strip_tac >>
  drule_all bop_scalar_inst_protected_frame >> strip_tac >> simp[]
QED

Theorem bop_scalar_success_ghost_frame:
  bop_scalar_seq {z | not_fresh_at sa z} A code B /\
  run_inst_seq code s = OK t /\ ghost_inv H d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
    FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  es'.scopes = es.scopes ==>
  ghost_inv H d cenv cx es' G' tn' (t with vs_inst_idx := j) /\
  ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >> drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `!z. not_fresh_at sa z ==>
    lookup_var z (t with vs_inst_idx := j) = lookup_var z s /\
    FLOOKUP G' z = FLOOKUP G z /\
    op_taint tn' (Var z) = op_taint tn (Var z)` by
    (gvs[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  conj_tac
  >- (irule ghost_inv_fresh_frame >>
      goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _ _`)) >>
      simp[] >> qexists_tac `sa` >> simp[] >>
      qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >> simp[]) >>
  irule ghost_kept_old_transport >> simp[] >> metis_tac[]
QED

Theorem bop_scalar_binop_success_ghost_path:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv H d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  es'.scopes = es.scopes ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ghost_inv H d cenv cx es' G' tn'
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z}
      ({x; y} UNION IMAGE Lit UNIV) (emitted_insts sa sb) B /\ op IN B` by
    (irule bop_scalar_binop_certificate >> simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `!z. z IN {z | not_fresh_at sa z} ==> not_fresh_at sa z` by simp[] >>
  drule_all bop_scalar_binop_success_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  irule bop_scalar_success_ghost_frame >> simp[] >>
  goal_assum (drule_at (Pat `bop_scalar_seq _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* The continuation receives the actual run as well as the ghost frame;
   semantic expression-post assembly stays at the operand-composition layer. *)
Theorem bop_scalar_suffix_outcome_ptr:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv H d cenv cx es G tn s) /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ((?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)) /\
  (!H v t G' tn'. valid_horizon cx st0 H es.storage_trace /\
      bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      ghost_inv H d cenv cx (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G' tn' ==>
      Q H (INL v) (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0
    (\st. (bop_result cx ann bop tys v1 v2 st, st)) (es,s,G,tn) Q
    (\H res fin ghost r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_bad_storage_at_def, storage_trace_domain_def] >> metis_tac[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `ghost_inv H0 d cenv cx es G tn s` by metis_tac[] >>
  qpat_x_assum `(?v t. _) \/ _` strip_assume_tac
  >- suspend "success" >> suspend "abort"
QED

Resume bop_scalar_suffix_outcome_ptr[success]:
  `?G' tn'. inst_seq_ptr (D H0) 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
      gas_path_ptr (D H0) 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      ghost_inv H0 d cenv cx (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G' tn'` by
    (irule bop_scalar_binop_success_ghost_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`, `es`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`] >>
  conj_tac >- simp[] >> qx_gen_tac `H2` >> strip_tac >>
  `ghost_inv H2 d cenv cx es G tn s` by metis_tac[] >>
  `?G2 tn2. inst_seq_ptr (D H2) 0 ctx fn PG G tn (emitted_insts sa sb) s G2 tn2 /\
      gas_path_ptr (D H2) 0 ctx fn PG G tn s 0 G2 tn2
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      op_prov G2 op = NONE /\ op_taint tn2 op = {} /\
      ghost_inv H2 d cenv cx (es with gas_obs := []) G2 tn2
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G2 tn2` by
    (irule bop_scalar_binop_success_ghost_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `G2 = G' /\ tn2 = tn'` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[exit_result_def] >>
  qpat_x_assum `!H v t G' tn'. _` irule >> simp[]
QED

Resume bop_scalar_suffix_outcome_ptr[abort]:
  `!z. z IN {} ==> not_fresh_at sa z` by simp[] >>
  drule_all bop_scalar_binop_certificate >> strip_tac >>
  `!op. op IN ({x;y} UNION IMAGE Lit UNIV) ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    metis_tac[bop_scalar_binop_input_clean] >>
  drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  rename1 `step_inst_base (mk_inst id opc [needle] []) u = Abort Revert_abort t` >>
  `isPREFIX (prefix ++ [mk_inst id opc [needle] []])
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `run_inst_seq (prefix ++ [mk_inst id opc [needle] []]) s = Abort Revert_abort t` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst id opc [needle] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  `EVERY (\i. MEM i.inst_opcode
      [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
       EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
       SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN; ASSERT; ASSERT_UNREACHABLE])
     (prefix ++ [mk_inst id opc [needle] []])` by
    (simp[EVERY_APPEND, mk_inst_def, EVERY_MEM] >>
     rpt strip_tac >> drule_all bop_scalar_seq_outputs >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     (prefix ++ [mk_inst id opc [needle] []])` by
    (rewrite_tac[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (prefix ++ [mk_inst id opc [needle] []]) s` by
    (irule run_inst_seq_mem_ok_every >> rewrite_tac[EVERY_MEM] >>
     rpt gen_tac >> strip_tac >> BETA_TAC >> gen_tac >>
     qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> strip_tac >>
     simp[below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_other]) >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  drule_all run_inst_seq_origin_ptr_abort_lift >>
  disch_then (qspecl_then [`{}`, `ctx`, `PG`]
    (qx_choose_then `j` assume_tac)) >>
  drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`,`PG`,`D H0`] strip_assume_tac) >>
  rename1 `inst_seq_ptr (D H0) 0 ctx fn PG G tn _ s Ga tna` >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError m))`, `es`, `Ga`, `tna`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[expr_exit_def, exit_result_def] >> qx_gen_tac `H2` >> disch_tac >>
  drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`,`PG`,`D H2`] strip_assume_tac) >>
  rename1 `inst_seq_ptr (D H2) 0 ctx fn PG G tn _ s Gb tnb` >>
  `Gb = Ga /\ tnb = tna` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[expr_exit_def, exit_result_def] >>
  first_x_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >> simp[]
QED
Finalise bop_scalar_suffix_outcome_ptr
