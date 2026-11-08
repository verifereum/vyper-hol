(* Memory-input hashing boundaries; offsets retain the allocation even for
   an empty payload. No padding cleanliness is required. *)
Theory bodyPtrEnvBuiltinsMemoryHash
Ancestors bodyPtrEnvBuiltinsHashStep bodyPtrEnvBuiltinsLen typedCopyPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs ptrDiscipline venomInst venomState
  words finite_map pred_set decoderGhostFramePtr ghostPcTransportPtr
  fragGasSeqPtr instIdxIndep venomExecSemantics fragExec exprLoweringProps
  memLocDefs codegenRel

Theorem hash_payload_add_covers:
  FLOOKUP G root = SOME (b,sz) /\ lookup_var root s = SOME a /\
  op_taint tn (Var root) = {} /\
  b <= w2n a + 32 /\ w2n a + 32 + n <= b + sz /\
  w2n a + 32 < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit 32w] [out])
      (update_var out (a + 32w) s))
    (step_taint (mk_inst id ADD [Var root; Lit 32w] [out]) s
      (update_var out (a + 32w) s) tn)
    out (update_var out (a + 32w) s) n
Proof
  strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root; Lit 32w] [out]) s
     (update_var out (a + 32w) s) tn) (Var out) = {}` by
    (irule scalar_builtin_output_clean >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  simp[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, wordsTheory.w2n_add_2] >>
  metis_tac[]
QED

Theorem hash_covered_payload_ok:
  ptr_covers G tn p s (w2n n) /\
  eval_operand (Var p) s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn len = {} /\
  (!i. w2n a <= i /\ i < w2n a + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id SHA3 [Var p; len] [out]) s
Proof
  strip_tac >> irule ptr_inst_ok_hash >>
  gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

Theorem hash_after_payload_add_ok:
  FLOOKUP G root = SOME (b,sz) /\ lookup_var root s = SOME a /\
  op_taint tn (Var root) = {} /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} /\ len <> dst /\
  (!i. w2n a + 32 <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn
    (step_prov PG G (mk_inst aid ADD [Var root; Lit 32w] [dst])
      (update_var dst (a + 32w) s))
    (step_taint (mk_inst aid ADD [Var root; Lit 32w] [dst]) s
      (update_var dst (a + 32w) s) tn)
    (mk_inst hid SHA3 [Var dst; Var len] [out])
    (update_var dst (a + 32w) s)
Proof
  strip_tac >> irule hash_covered_payload_ok >>
  simp[copy_len_binop_ghost_frame] >>
  qexists_tac `n` >>
  simp[copy_len_binop_ghost_frame, wordsTheory.w2n_add_2] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def,
                   FLOOKUP_UPDATE] >>
  irule hash_payload_add_covers >> metis_tac[]
QED

Theorem hash_header_load_frame:
  root <> len /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\ op_taint tn (Var root) = {} /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  lookup_var root (update_var len (mload (w2n a) s) s) = SOME a /\
  FLOOKUP (step_prov PG G (mk_inst id MLOAD [Var root] [len])
    (update_var len (mload (w2n a) s) s)) root = SOME (b,sz) /\
  op_taint (step_taint (mk_inst id MLOAD [Var root] [len]) s
    (update_var len (mload (w2n a) s) s) tn) (Var root) = {} /\
  op_taint (step_taint (mk_inst id MLOAD [Var root] [len]) s
    (update_var len (mload (w2n a) s) s) tn) (Var len) = {} /\
  (step_taint (mk_inst id MLOAD [Var root] [len]) s
    (update_var len (mload (w2n a) s) s) tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  drule_all mload_ghost_clean >> strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT] >>
  simp[step_taint_other_output, mk_inst_def] >> gvs[lookup_var_def]
QED

Theorem memory_hash_instruction_checks:
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n /\
  root <> len /\ len <> dst /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  u = update_var len n s /\
  G1 = step_prov PG G (mk_inst lid MLOAD [Var root] [len]) u /\
  tn1 = step_taint (mk_inst lid MLOAD [Var root] [len]) s u tn /\
  v = update_var dst (a + 32w) u /\
  G2 = step_prov PG G1 (mk_inst aid ADD [Var root; Lit 32w] [dst]) v /\
  tn2 = step_taint (mk_inst aid ADD [Var root; Lit 32w] [dst]) u v tn1 ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst lid MLOAD [Var root] [len]) s /\
  ptr_inst_ok D 0 0 ctx fn G1 tn1 (mk_inst aid ADD [Var root; Lit 32w] [dst]) u /\
  ptr_inst_ok D 0 0 ctx fn G2 tn2 (mk_inst hid SHA3 [Var dst; Var len] [out]) v
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  `(!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all hash_header_load_frame >> strip_tac >>
  `lookup_var root u = SOME a /\ FLOOKUP G1 root = SOME (b,sz) /\
   op_taint tn1 (Var root) = {} /\ op_taint tn1 (Var len) = {} /\
   tn1.t_mem = tn.t_mem` by gvs[] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  conj_tac
  >- (irule ptr_inst_ok_scalar_builtin >> simp[] >>
      rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  gvs[] >> irule hash_after_payload_add_ok >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`b`, `sz`] >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac
QED

Theorem memory_hash_seq_checks:
  code = [mk_inst lid MLOAD [Var root] [len];
          mk_inst aid ADD [Var root; Lit 32w] [dst];
          mk_inst hid SHA3 [Var dst; Var len] [out]] /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n /\
  root <> len /\ len <> dst /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  u = update_var len n s /\ v = update_var dst (a + 32w) u /\
  G1 = step_prov PG G (mk_inst lid MLOAD [Var root] [len]) u /\
  tn1 = step_taint (mk_inst lid MLOAD [Var root] [len]) s u tn /\
  G2 = step_prov PG G1 (mk_inst aid ADD [Var root; Lit 32w] [dst]) v /\
  tn2 = step_taint (mk_inst aid ADD [Var root; Lit 32w] [dst]) u v tn1 /\
  step_inst_base (mk_inst hid SHA3 [Var dst; Var len] [out]) v = OK t ==>
  inst_seq_ptr D 0 ctx fn PG G tn code s
    (step_prov PG G2 (mk_inst hid SHA3 [Var dst; Var len] [out]) t)
    (step_taint (mk_inst hid SHA3 [Var dst; Var len] [out]) v t tn2)
Proof
  strip_tac >>
  `step_inst_base (mk_inst lid MLOAD [Var root] [len]) s = OK u` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  `step_inst_base (mk_inst aid ADD [Var root; Lit 32w] [dst]) u = OK v` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def] >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `~is_terminator (mk_inst lid MLOAD [Var root] [len]).inst_opcode /\
   ~is_terminator (mk_inst aid ADD [Var root; Lit 32w] [dst]).inst_opcode /\
   ~is_terminator (mk_inst hid SHA3 [Var dst; Var len] [out]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep,
       exec_result_map_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  `(!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all hash_header_load_frame >> strip_tac >>
  simp[Once inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_scalar_builtin >> simp[] >>
      rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  gvs[] >> simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[Once inst_seq_ptr_def] >> conj_tac
  >- (irule hash_covered_payload_ok >>
      simp[copy_len_binop_ghost_frame] >>
      simp[copy_len_binop_ghost_frame, wordsTheory.w2n_add_2] >>
      irule hash_payload_add_covers >> simp[] >>
      qexistsl_tac [`b`, `sz`] >> simp[]) >>
  simp[step_inst_inst_idx_indep, exec_result_map_def, inst_seq_ptr_def]
QED

Theorem hash_update_ghosts:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id SHA3 [src; len] [out]) (update_var out w s))
    (step_taint (mk_inst id SHA3 [src; len] [out]) s (update_var out w s) tn)
    (update_var out w s) /\
  ghost_kept cenv es0 sa G0 tn0 s0
    (step_prov PG G (mk_inst id SHA3 [src; len] [out]) (update_var out w s))
    (step_taint (mk_inst id SHA3 [src; len] [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `(step_taint (mk_inst id SHA3 [src; len] [out]) s (update_var out w s) tn).t_mem =
   tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     simp[update_var_def, source_memory_write_ranges_def, mk_inst_def,
          written_taint_def]) >>
  conj_tac
  >- (irule single_output_ghost_inv >> simp[update_var_def] >>
      qexists_tac `sa` >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  irule single_output_ghost_kept >> simp[]
QED

Theorem memory_hash_ghosts:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa len /\ ~not_fresh_at sa dst /\ ~not_fresh_at sa out /\
  u = update_var len n s /\ v = update_var dst p u /\ t = update_var out w v /\
  G1 = step_prov PG G (mk_inst lid MLOAD [src] [len]) u /\
  tn1 = step_taint (mk_inst lid MLOAD [src] [len]) s u tn /\
  G2 = step_prov PG G1 (mk_inst aid ADD [src; Lit 32w] [dst]) v /\
  tn2 = step_taint (mk_inst aid ADD [src; Lit 32w] [dst]) u v tn1 ==>
  ghost_inv d cenv cx es
    (step_prov PG G2 (mk_inst hid SHA3 [Var dst; Var len] [out]) t)
    (step_taint (mk_inst hid SHA3 [Var dst; Var len] [out]) v t tn2) t /\
  ghost_kept cenv es0 sa G0 tn0 s0
    (step_prov PG G2 (mk_inst hid SHA3 [Var dst; Var len] [out]) t)
    (step_taint (mk_inst hid SHA3 [Var dst; Var len] [out]) v t tn2)
Proof
  strip_tac >>
  `ghost_inv d cenv cx es G1 tn1 u /\
   ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1` by
    (simp[] >> irule load_builtin_update_ghosts >> simp[]) >>
  `ghost_inv d cenv cx es G2 tn2 v /\
   ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2` by
    (qpat_x_assum `G2 = _` SUBST1_TAC >> qpat_x_assum `tn2 = _` SUBST1_TAC >>
     qpat_x_assum `v = _` SUBST1_TAC >>
     irule scalar_builtin_update_ghosts >> simp[]) >>
  qpat_x_assum `t = _` SUBST1_TAC >> irule hash_update_ghosts >> simp[]
QED

Theorem memory_hash_counted_path:
  code = [mk_inst lid MLOAD [Var root] [len];
          mk_inst aid ADD [Var root; Lit 32w] [dst];
          mk_inst hid SHA3 [Var dst; Var len] [out]] /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n /\
  root <> len /\ len <> dst /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa len /\ ~not_fresh_at sa dst /\ ~not_fresh_at sa out /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result (Var out) G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  qabbrev_tac `u = update_var len n s` >>
  qabbrev_tac `v = update_var dst (a + 32w) u` >>
  `step_inst_base (mk_inst lid MLOAD [Var root] [len]) s = OK u` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def, Abbr `u`]) >>
  `step_inst_base (mk_inst aid ADD [Var root; Lit 32w] [dst]) u = OK v` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `v`] >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, Abbr `u`]) >>
  `step_inst_base (mk_inst hid SHA3 [Var dst; Var len] [out]) v = OK t` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst lid MLOAD [Var root] [len]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst lid MLOAD [Var root] [len]) s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 (mk_inst aid ADD [Var root; Lit 32w] [dst]) v` >>
  qabbrev_tac `tn2 = step_taint (mk_inst aid ADD [Var root; Lit 32w] [dst]) u v tn1` >>
  qexistsl_tac [`step_prov PG G2 (mk_inst hid SHA3 [Var dst; Var len] [out]) t`,
    `step_taint (mk_inst hid SHA3 [Var dst; Var len] [out]) v t tn2`] >>
  conj_tac
  >- (`inst_seq_ptr D 0 ctx fn PG G tn code s
        (step_prov PG G2 (mk_inst hid SHA3 [Var dst; Var len] [out]) t)
        (step_taint (mk_inst hid SHA3 [Var dst; Var len] [out]) v t tn2)` by
        (drule_at (Pat `_ = [_;_;_]`) memory_hash_seq_checks >>
         disch_then irule >>
         simp[Abbr `u`, Abbr `v`, Abbr `G1`, Abbr `G2`, Abbr `tn1`, Abbr `tn2`] >>
         qexistsl_tac [`a`, `b`, `sz`] >> simp[]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
        simp[mk_inst_def, is_terminator_def] >>
      drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]) >>
  conj_tac >- irule hash_output_clean >>
  `?w. t = update_var out w v` by
    (qpat_x_assum `step_inst_base (mk_inst hid _ _ _) _ = _` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, AllCaseEqs()] >> metis_tac[]) >>
  irule memory_hash_ghosts >>
  simp[Abbr `u`, Abbr `v`, Abbr `G1`, Abbr `G2`, Abbr `tn1`, Abbr `tn2`] >>
  metis_tac[]
QED
