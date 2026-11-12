(* Scalar certificates for both builtin length guards, independent of validity. *)
Theory abiDecodePtrLengthGuard
Ancestors
  abiBuiltinLengthGuard abiBuiltinBoundTests bodyPtrBopScalarCompile
  bodyPtrBopScalarSeq bodyPtrBopScalarDynamic emitHelper exprLoweringProps
  emitHelperProps compileEnv freshWrites ptrDiscipline list pred_set fragGasSeqPtr

Theorem abi_builtin_bound_test_scalar:
  abi_builtin_bound_test opc lhs rhs st = (v,st') /\
  MEM opc [LT; GT; SLT; SGT; EQ] /\ lhs IN A /\ rhs IN A /\
  (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[abi_builtin_bound_test_def] >> strip_tac >>
  drule bop_scalar_compile_emit_iszero >> simp[]
QED

Theorem abi_builtin_interval_guard_scalar:
  abi_builtin_interval_guard len mn mx st = ((),st') /\ len IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
      same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  simp[abi_builtin_interval_guard_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule abi_builtin_bound_test_scalar >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!x. x IN R ==> not_fresh_at m x` by metis_tac[not_fresh_at_mono] >>
      `len IN B /\ !w. Lit w IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule abi_builtin_bound_test_scalar >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!x. x IN R ==> not_fresh_at m' x` by metis_tac[not_fresh_at_mono] >>
          `u IN B'` by metis_tac[SUBSET_DEF] >>
          rename1 `comp_bind (emit_op AND _) _ _ = (result,_)` >>
          Cases_on `result` >> drule bop_scalar_compile_emit_checked >> simp[]) >> simp[]) >> simp[]
QED

Theorem abi_builtin_length_guard_scalar:
  abi_builtin_length_guard len mn mx st = ((),st') /\ len IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
      same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  Cases_on `mn = mx` >> simp[abi_builtin_length_guard_def] >> strip_tac
  >- (fs[abi_builtin_eq_guard_def] >>
      drule bop_scalar_compile_emit_checked >> simp[]) >>
  drule abi_builtin_interval_guard_scalar >> simp[]
QED

(* Literals are intrinsically clean; runtime callers supply only len. *)
Theorem abi_builtin_length_guard_success_path:
  abi_builtin_length_guard len mn mx st = ((),st') /\
  (!x. x IN R ==> not_fresh_at st x) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?G' tn'.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s G' tn' /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule abi_builtin_length_guard_scalar >>
  disch_then (qspecl_then [`R`, `{len} UNION IMAGE Lit UNIV`] mp_tac) >>
  simp[] >> strip_tac >>
  `!op. op IN {len} UNION IMAGE Lit UNIV ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac [IN_UNION, IN_SING, IN_IMAGE, IN_UNIV] >>
     rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (drule bop_scalar_seq_opcodes >>
     simp[EVERY_CONJ] >> strip_tac >>
     fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  simp[]
QED

Theorem abi_builtin_length_guard_abort_path:
  abi_builtin_length_guard len mn mx st = ((),st') /\
  (!x. x IN R ==> not_fresh_at st x) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = Abort a t ==>
  ?G' tn' n j.
    gas_path_ptr D 0 ctx fn PG G tn s n G' tn'
      (Abort a (t with vs_inst_idx := j)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule abi_builtin_length_guard_scalar >>
  disch_then (qspecl_then [`R`, `{len} UNION IMAGE Lit UNIV`] mp_tac) >>
  simp[] >> strip_tac >>
  `!op. op IN {len} UNION IMAGE Lit UNIV ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac [IN_UNION, IN_SING, IN_IMAGE, IN_UNIV] >>
     rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_abort_path >> simp[]
QED
