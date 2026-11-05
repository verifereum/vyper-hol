(* Endpoint-parametric frames: these apply to the same checked run and
   ghost witnesses, rather than introducing independently chosen ghosts. *)
Theory forPtrElementFrame
Ancestors bodyPtrDefs forPtrBytes forPtrBulk forPtrWord fragGasSeqPtr
  decoderGhostFramePtr ptrDiscipline venomInst venomExecSemantics venomState
  list finite_map pred_set exprLoweringProps instIdxIndep fragExec

Theorem inst_seq_ptr_nonmemory_taint_frame:
  !is s G tn gf tf.
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
    i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) is /\
  inst_seq_ptr D lo ctx fn PG G tn is s gf tf ==>
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  drule_all step_taint_nonmemory_frame >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem mcopy_checked_exterior_taint_frame:
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MCOPY [Var dst; Var src; count_op] []] s gf tf ==>
  !i. i < w2n b \/ w2n b + w2n n <= i ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MCOPY [Var dst; Var src; count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  gvs[inst_seq_ptr_def] >>
  simp[SRULE [] (cj 5 typedCopyPtrTheory.mcopy_operand_ghost_frame),
       eval_operand_def] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem mstore_checked_exterior_taint_frame:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MSTORE [Var dst; value] []] s gf tf ==>
  !i. i < w2n a \/ w2n a + 32 <= i ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
    OK (mstore (w2n a) w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  gvs[inst_seq_ptr_def] >>
  simp[SRULE [] (cj 5 typedCopyPtrTheory.mstore_ghost_frame)] >>
  rpt strip_tac >> decide_tac
QED

Theorem finite_copy_step_storage_state_frame:
  MEM inst.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY] /\
  step_inst_base inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, exec_pure2_def, exec_write2_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem finite_copy_run_storage_state_frame:
  !is s t.
  EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY]) is /\
  run_inst_seq is s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  irule finite_copy_step_storage_state_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem inst_seq_ptr_ghost_unique:
  !is s G tn g1 t1 g2 t2.
  inst_seq_ptr D lo ctx fn PG G tn is s g1 t1 /\
  inst_seq_ptr D lo ctx fn PG G tn is s g2 t2 ==>
  g1 = g2 /\ t1 = t2
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> metis_tac[]
QED

Theorem inst_seq_ptr_append_tail:
  !pre s t G tn gm tm post gf tf.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  run_inst_seq pre s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn pre s gm tm /\
  inst_seq_ptr D lo ctx fn PG G tn (pre ++ post) s gf tf ==>
  inst_seq_ptr D lo ctx fn PG gm tm post
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH pre) gf tf
Proof
  Induct >> simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  disch_then drule_all >> pure_rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
  disch_then ACCEPT_TAC
QED

Theorem prefix_mcopy_checked_exterior_taint_frame:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  run_inst_seq pre s = OK u /\
  inst_seq_ptr D lo ctx fn PG G tn pre s gm tm /\ tm.t_mem = tn.t_mem /\
  lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
  eval_operand count_op u = SOME n /\ w2n n <= capacity /\
  inst_seq_ptr D lo ctx fn PG G tn
    (pre ++ [mk_inst id MCOPY [Var dst; Var src; count_op] []]) s gf tf ==>
  !i. i < w2n b \/ w2n b + capacity <= i ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> drule_all inst_seq_ptr_append_tail >> strip_tac >>
  `lookup_var src (u with vs_inst_idx := s.vs_inst_idx + LENGTH pre) = SOME a /\
   lookup_var dst (u with vs_inst_idx := s.vs_inst_idx + LENGTH pre) = SOME b /\
   eval_operand count_op (u with vs_inst_idx := s.vs_inst_idx + LENGTH pre) = SOME n` by
    gvs[lookup_var_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ gm tm [_] _ _ _`
    (mp_then Any mp_tac mcopy_checked_exterior_taint_frame) >>
  disch_then (qspecl_then [`n`, `b`, `a`] mp_tac) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem bytes_copy_checked_exterior_taint_frame:
  pre = [mk_inst id MLOAD [Var src] [t0];
    mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
    mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
    mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]] /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  src <> t0 /\ src <> t1 /\ src <> t2 /\ src <> t3 /\
  dst <> t0 /\ dst <> t1 /\ dst <> t2 /\ dst <> t3 /\
  w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) <= capacity /\
  inst_seq_ptr D 0 ctx fn PG G tn
    (pre ++ [mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []]) s gf tf ==>
  !i. i < w2n b \/ w2n b + capacity <= i ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> drule_all for_bytes_length_prefix >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  gen_tac >> disch_tac >> irule prefix_mcopy_checked_exterior_taint_frame >>
  goal_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ (_ ++ _) _ _ _`)) >>
  qpat_x_assum `pre = _` SUBST_ALL_TAC >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
  goal_assum (drule_at (Pat `_.t_mem = _.t_mem`)) >>
  qexistsl_tac [`a`, `b`, `capacity`, `gf'`] >>
  simp[eval_operand_def] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >>
  gvs[] >> simp[mk_inst_def, is_terminator_def]
QED

(* Storage and immutable frames are independent of the payload theorem and
   therefore apply to exactly the caller's checked endpoint witnesses. *)
Theorem finite_copy_endpoint_frames:
  EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY]) is /\
  run_inst_seq is s = OK sf /\
  inst_seq_ptr D lo ctx fn PG G tn is s gf tf ==>
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all finite_copy_run_storage_state_frame >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
    i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) is` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[] >>
     metis_tac[]) >>
  drule_all inst_seq_ptr_nonmemory_taint_frame >> simp[]
QED

Theorem compile_bulk_copy_endpoint_frames:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword (:256) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  run_inst_seq (emitted_insts sa sb) s = OK sf /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s gf tf ==>
  (!i. i < w2n b \/ w2n b+n <= i ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient
Proof
  strip_tac >> drule for_compile_bulk_copy_code >> strip_tac >>
  Cases_on `n = 0`
  >- gvs[inst_seq_ptr_def, run_inst_seq_def] >>
  gvs[] >>
  `EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY])
    [mk_inst sa.cs_next_id MCOPY [Var dst; Var src; Lit (n2w n)] []]` by
    simp[mk_inst_def] >>
  drule_all finite_copy_endpoint_frames >> strip_tac >> simp[] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _`
    (mp_then Any mp_tac mcopy_checked_exterior_taint_frame) >>
  disch_then (qspecl_then [`n2w n`, `b`, `a`] mp_tac) >> simp[]
QED

Theorem compile_bytes_copy_endpoint_frames:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) <= capacity /\
  run_inst_seq (emitted_insts sa sb) s = OK sf /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s gf tf ==>
  (!i. i < w2n b \/ w2n b+capacity <= i ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient
Proof
  strip_tac >> drule for_bytes_copy_code >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY])
    (emitted_insts sa sb)` by simp[mk_inst_def] >>
  drule_all finite_copy_endpoint_frames >> strip_tac >> simp[] >>
  `src <> t0 /\ src <> t1 /\ src <> t2 /\ src <> t3 /\
   dst <> t0 /\ dst <> t1 /\ dst <> t2 /\ dst <> t3` by metis_tac[] >>
  gen_tac >> disch_tac >> irule bytes_copy_checked_exterior_taint_frame >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  simp_tac bool_ss [APPEND] >>
  goal_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`a`, `b`, `capacity`] >> simp[]
QED

(* The word checked endpoint already exports the exact memory-taint
   equation; this companion adds the remaining fields on those witnesses. *)
Theorem word_copy_endpoint_frames:
  tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
  run_inst_seq [mk_inst id MLOAD [Var src] [tmp];
    mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s = OK sf /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s gf tf ==>
  (!i. i < w2n b \/ w2n b+32 <= i ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY])
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst; Var tmp] []]` by simp[mk_inst_def] >>
  drule_all finite_copy_endpoint_frames >> strip_tac >> simp[] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED
