Theory bodyPtrBopHashRun
Ancestors
  bodyPtrBopHashSequence fragGasSeqPtr exprLoweringProps fragExec
  instIdxIndep ghostPcTransportPtr venomInst venomState venomExecSemantics

Theorem bop_hash_run_checked:
  p <> q /\ l <> q /\ ~ctx_has_dalloca ctx /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
  mem_word_at (w2n w) s.vs_memory = n2w n /\ n < dimword(:256) /\
  FLOOKUP G p = SOME (b,sz) /\
  (0 < n ==> b <= w2n (w + 32w) /\ w2n (w + 32w) + n <= b + sz) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + n ==> i NOTIN tn.t_mem) /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  run_inst_seq [iA;iL;iH] s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn [iA;iL;iH] s G' tn' /\
    op_prov G' (Var h) = NONE /\ op_taint tn' (Var h) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. x <> q /\ x <> l /\ x <> h ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  pure_rewrite_tac[run_inst_seq_def] >>
  simp[AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base (mk_inst aId ADD [Var p; Lit 32w] [q]) s = OK uA` >>
  rename1 `step_inst_base (mk_inst lId MLOAD [Var p] [l]) uA = OK uL` >>
  `step_inst_base iL (uA with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (uL with vs_inst_idx := SUC s.vs_inst_idx)` by
    gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def, exec_result_map_def] >>
  `step_inst_base (mk_inst hId SHA3 [Var q; Var l] [h])
     (uL with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
     OK (t with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def, exec_result_map_def] >>
  qpat_x_assum `iL = _` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst hId SHA3 [Var q; Var l] [h])
     ((uL with vs_inst_idx := SUC s.vs_inst_idx) with
       vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
     OK (t with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (GEN_ALL bop_hash_sequence_checked)) >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem bop_hash_run_ptr:
  p <> q /\ l <> q /\ ~ctx_has_dalloca ctx /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
  mem_word_at (w2n w) s.vs_memory = n2w n /\ n < dimword(:256) /\
  FLOOKUP G p = SOME (b,sz) /\
  (0 < n ==> b <= w2n (w + 32w) /\ w2n (w + 32w) + n <= b + sz) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + n ==> i NOTIN tn.t_mem) /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [iA;iL;iH] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [iA;iL;iH] s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    op_prov G' (Var h) = NONE /\ op_taint tn' (Var h) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. x <> q /\ x <> l /\ x <> h ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_hash_run_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [iA;iL;iH]` by gvs[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  gvs[mk_inst_def] >> metis_tac[]
QED
