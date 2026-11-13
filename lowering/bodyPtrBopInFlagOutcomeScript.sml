(* Successful scalar membership suffix: certificates and ghost framing. *)
Theory bodyPtrBopInFlagOutcome
Ancestors bodyPtrBopInFlagCertificate bodyPtrBopScalarOutcome
  bodyPtrDefs exprSimDefs fragGasPathPtr ptrDiscipline
  finite_map list pred_set gasSummaryComposePtr gasStorage vyperStorageFootprint fragGasSeqPtr fragExec

Theorem membership_flag_success_ghost_path:
  (bop = In \/ bop = NotIn) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z}
      ({x; y} UNION IMAGE Lit UNIV) (emitted_insts sa sb) B /\ op IN B` by
    (drule membership_flag_scalar_certificate >>
     disch_then (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     disch_then (qspecl_then [`{z | not_fresh_at sa z}`,
       `{x; y} UNION IMAGE Lit UNIV`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!z. z IN {z | not_fresh_at sa z} ==> not_fresh_at sa z` by simp[] >>
  `!v. v IN ({x; y} UNION IMAGE Lit UNIV) ==>
    op_prov G v = NONE /\ op_taint tn v = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `x IN ({x; y} UNION IMAGE Lit UNIV) /\
   y IN ({x; y} UNION IMAGE Lit UNIV) /\
   (!w. Lit w IN ({x; y} UNION IMAGE Lit UNIV))` by simp[] >>
  drule_all membership_flag_certificate_result_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  irule bop_scalar_success_ghost_frame >> simp[] >>
  goal_assum (drule_at (Pat `bop_scalar_seq _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem membership_flag_suffix_outcome_ptr:
  (bop = In \/ bop = NotIn) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> ghost_inv H d cenv cx es G tn s) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) /\
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
  qpat_x_assum `?v t. _` strip_assume_tac >>
  reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_bad_storage_at_def, storage_trace_domain_def] >> metis_tac[]) >>
  qpat_x_assum `?H. valid_horizon _ _ H es.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  `ghost_inv H0 d cenv cx es G tn s` by metis_tac[] >>
  `?G' tn'. inst_seq_ptr (D H0) 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
      gas_path_ptr (D H0) 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      ghost_inv H0 d cenv cx (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G' tn'` by
    (irule membership_flag_success_ghost_path >> simp[] >>
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
    (irule membership_flag_success_ghost_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `G2 = G' /\ tn2 = tn'` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[exit_result_def] >>
  qpat_x_assum `!H v t G' tn'. _` irule >> simp[]
QED
