(* Semantic composition of uniform checked immutable-copy fragments. *)
Theory immutableCopySeqPtr
Ancestors
  immutableRegionLoadPtr immutableOffsetPtr immutableSeqCursorPtr
  emittedSeqComposePtr instSeqComposePtr exprSimCopy exprSimStorageCopy
  immutableCopyExecution context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  exprLoweringProps fragGasSeqPtr ptrDiscipline venomInst venomState
  finite_map words list bodyPtrDefs contextCodegenRel appendStorageGhostPtr

Theorem copy_runtime_uniform_compose:
  copy_runtime_frame sa s sm t /\ copy_runtime_frame sm t sb u /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
    (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sm sb)
    (t with vs_inst_idx := k) G2 tn2) ==>
  copy_runtime_frame sa s sb u /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) G2 tn2)
Proof
  strip_tac >> conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  irule emitted_inst_seq_ptr_uniform_compose >>
  qexistsl [`G1`,`sm`,`t`,`tn1`] >>
  gvs[copy_runtime_frame_def, inst_extends_def]
QED

Theorem old_operand_provenance_frame:
  (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x) /\
  copy_old_operand sa op ==> op_prov Gf op = op_prov G op
Proof
  Cases_on `op` >> simp[op_prov_def, copy_old_operand_def]
QED

Theorem copy_runtime_old_ghost_trans:
  copy_runtime_frame sa s sm t /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at sm x ==>
    FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)) ==>
  !x. not_fresh_at sa x ==>
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)
Proof
  simp[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]
QED

Theorem immutable_offset_load_checked:
  compile_lit_byte_offset src off sa = (sop,sm) /\
  compile_imm_load_word ctor imm sop sm = (r,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    copy_old_operand sa region) /\
  (ctor ==> ?lo sz.
    (case imm of NONE => op_prov G src | SOME region => first_prov G [src;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w off) /\
      w2n (a + n2w off) + 32 <= lo + sz) /\
  ~ctx_has_dalloca ctx ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\ copy_old_operand sb r /\
    eval_operand r t = SOME (immutable_copy_read ctor (a + n2w off) s) /\
    t.vs_memory = s.vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\
    op_taint tf r =
      (if ctor then mem_word_taint tn.t_mem (w2n (a + n2w off)) else {}) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all compile_lit_byte_offset_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`]
    (qx_choose_then `t` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac)))) >>
  `!region. ctor /\ imm = SOME region ==>
    eval_operand region t = SOME 0w /\ op_taint tn1 region = {}` by
    (gen_tac >> strip_tac >>
     `copy_old_operand sa region /\ eval_operand region s = SOME 0w /\
      op_taint tn region = {}` by metis_tac[] >>
     conj_tac >- metis_tac[copy_runtime_frame_operand] >>
     `op_taint tn1 region = op_taint tn region` by
       (irule old_operand_taint_frame >> qexists_tac `sa` >>
        gvs[copy_old_operand_def]) >>
     simp[]) >>
  `(ctor ==> ?lo sz.
    (case imm of NONE => op_prov G1 sop | SOME region => first_prov G1 [sop;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w off) /\
      w2n (a + n2w off) + 32 <= lo + sz)` by
    (Cases_on `ctor` >> simp[] >> Cases_on `imm` >> gvs[] >>
     `op_prov G1 x = op_prov G x` by
       (irule old_operand_provenance_frame >> metis_tac[]) >>
     gvs[first_prov_def]) >>
  drule_all compile_imm_load_word_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >>
     metis_tac[is_terminator_def]) >>
  drule_all copy_runtime_uniform_compose >> strip_tac >>
  `immutable_copy_read ctor (a + n2w off) t =
   immutable_copy_read ctor (a + n2w off) s` by
    (irule immutable_copy_read_cong >> simp[] >>
     metis_tac[copy_runtime_frame_def, copy_static_fields]) >>
  qexistsl [`t'`,`Gf`,`tf`] >> gvs[] >>
  gen_tac >> strip_tac >>
  `not_fresh_at sm x` by
    (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem immutable_offset_store_checked:
  compile_lit_byte_offset (Var p) off sa = (dop,sm) /\
  emit_void MSTORE [dop;v] sm = ((),sb) /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  ptr_covers G tn p s cap /\ off < cap /\ off + 32 <= cap /\
  w2n b + off < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\
    t.vs_memory = (mstore (w2n (b + n2w off)) value s).vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem =
      (tn.t_mem DIFF {i | w2n (b + n2w off) <= i /\
                          i < w2n (b + n2w off) + 32}) UNION
      {w2n (b + n2w off) + j | j IN op_taint tn v} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all compile_lit_byte_offset_covered >>
  disch_then (qspecl_then [`D`,`fn`,`PG`]
    (qx_choose_then `q` (qx_choose_then `t` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac))))) >> gvs[] >>
  `eval_operand v t = SOME value /\ copy_old_operand sm v` by
    metis_tac[copy_runtime_frame_operand, copy_old_operand_mono,
              copy_runtime_frame_def] >>
  `op_taint tn1 v = op_taint tn v` by
    (irule old_operand_taint_frame >> qexists_tac `sa` >>
     gvs[copy_old_operand_def]) >>
  `copy_old_operand sm (Var q) /\ eval_operand (Var q) t = SOME (b + n2w off)` by
    simp[copy_old_operand_def, eval_operand_def] >>
  drule_all emit_mstore_payload_checked_uniform >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >>
     metis_tac[is_terminator_def]) >>
  drule_all copy_runtime_uniform_compose >> strip_tac >>
  qexistsl [`mstore (w2n (b + n2w off)) value t`, `G1`,
    `tn1 with t_mem :=
      (tn1.t_mem DIFF {i | w2n (b + n2w off) <= i /\
                          i < w2n (b + n2w off) + 32}) UNION
      {w2n (b + n2w off) + j | j IN op_taint tn1 v}`] >>
  gvs[mstore_def, op_taint_def]
QED

Theorem ptr_covers_copy_runtime_frame:
  copy_runtime_frame sa s sb t /\ not_fresh_at sa p /\
  ptr_covers G tn p s n /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) ==>
  ptr_covers Gf tf p t n
Proof
  strip_tac >> irule ptr_covers_old_transport >>
  qexistsl [`G`,`s`,`sa`,`tn`] >> gvs[copy_runtime_frame_def]
QED

Theorem immutable_load_nonterminators:
  compile_imm_load_word ctor imm op sa = (r,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `ctor`
  >- (gvs[] >> drule copy_ctor_load_shape >> simp[EVERY_MEM] >>
      metis_tac[is_terminator_def]) >>
  gvs[compile_imm_load_word_def] >>
  irule emitted_op_nonterminators >> simp[is_terminator_def] >>
  goal_assum (drule_at Any) >> simp[is_terminator_def]
QED

Theorem immutable_offset_load_nonterminators:
  compile_lit_byte_offset src off sa = (sop,sm) /\
  compile_imm_load_word ctor imm sop sm = (r,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule immutable_byte_offset_extends >> strip_tac >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (Cases_on `ctor`
     >- (gvs[] >> drule copy_ctor_load_shape >> simp[]) >>
     gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    metis_tac[emitted_insts_append] >>
  simp[EVERY_APPEND] >> conj_tac
  >- (drule code_offset_insts >> simp[EVERY_MEM] >>
      metis_tac[is_terminator_def]) >>
  metis_tac[immutable_load_nonterminators]
QED

Theorem immutable_copy_one_checked:
  immutable_copy_one ctor imm src (Var p) off sa = ((),sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    copy_old_operand sa region) /\
  (ctor ==> ?lo sz.
    (case imm of NONE => op_prov G src | SOME region => first_prov G [src;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w off) /\
      w2n (a + n2w off) + 32 <= lo + sz) /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  ptr_covers G tn p s cap /\ off < cap /\ off + 32 <= cap /\
  w2n b + off < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\
    t.vs_memory = (immutable_word_transfer F ctor a b off s).vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem =
      (tn.t_mem DIFF {i | w2n (b + n2w off) <= i /\
                          i < w2n (b + n2w off) + 32}) UNION
      IMAGE (\j. w2n (b + n2w off) + j)
        (if ctor then mem_word_taint tn.t_mem (w2n (a + n2w off)) else {}) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all immutable_offset_load_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `t` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac)))) >>
  rename1 `compile_imm_load_word ctor imm sop sm = (value,s2)` >>
  `not_fresh_at s2 p /\ lookup_var p t = SOME b /\ ptr_covers G1 tn1 p t cap` by
    (conj_tac
     >- (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[copy_runtime_frame_def] >>
     irule ptr_covers_copy_runtime_frame >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  `w2n b + off < dimword(:256)` by decide_tac >>
  drule_all immutable_offset_store_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s2)` by
    metis_tac[immutable_offset_load_nonterminators] >>
  drule_all copy_runtime_uniform_compose >> strip_tac >>
  qexistsl [`t'`,`Gf`,`tf`] >>
  gvs[immutable_word_transfer_def, pred_setTheory.IMAGE_DEF,
      immutable_mstore_memory_cong] >>
  gen_tac >> strip_tac >>
  `not_fresh_at s2 x` by
    (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED
