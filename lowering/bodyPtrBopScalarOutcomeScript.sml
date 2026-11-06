(* Runtime and ghost frames for the constructive scalar suffix. *)
Theory bodyPtrBopScalarOutcome
Ancestors bodyPtrBopScalarRun bodyPtrBopScalarDispatch bodyPtrBopScalarSeq
  bodyPtrBopScalarStep bodyPtrBopAssert bodyPtrDefs exprSimPtrProps
  appendStorageGhostPtr emitHelperProps freshWrites ptrDiscipline
  exprBopSimProps exprSimDefs fragGasPathPtr
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
      simp[Once step_inst_base_def] >>
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
  run_inst_seq code s = OK t /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
    FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  es'.scopes = es.scopes ==>
  ghost_inv d cenv cx es' G' tn' (t with vs_inst_idx := j) /\
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
      goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
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
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  es'.scopes = es.scopes ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ghost_inv d cenv cx es' G' tn'
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
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ((?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)) /\
  (!v t G' tn'. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      ghost_inv d cenv cx (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G' tn' ==>
      Q (INL v) (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (bop_result cx ann bop tys v1 v2 st, st)) (es,s,G,tn) Q
    (\res fin ghost r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?v t. _) \/ _` strip_assume_tac
  >- (`?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
          (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
        op_prov G' op = NONE /\ op_taint tn' op = {} /\
        ghost_inv d cenv cx (es with gas_obs := []) G' tn'
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
        ghost_kept cenv es sa G tn s G' tn'` by
        (irule bop_scalar_binop_success_ghost_path >> simp[] >>
         goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
         simp[] >> metis_tac[]) >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL v`, `es`, `G'`, `tn'`,
        `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`] >>
      simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!z. z IN {} ==> not_fresh_at sa z` by simp[] >>
  drule_all bop_scalar_binop_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError m))`, `es`, `G'`, `tn'`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED
