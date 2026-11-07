(* Iterated checked immutable copies keep one endpoint and uniform ghosts. *)
Theory immutableCopyWordsPtr
Ancestors
  immutableCopySeqPtr immutableCopyTaint immutableCopyExecution exprSimCopy
  exprSimStorageCopy context compileEnv emitHelper exprLoweringProps
  fragGasSeqPtr ptrDiscipline venomState venomInst words list finite_map
  emittedSeqComposePtr contextCodegenRel bodyPtrDefs

Theorem immutable_copy_opcodes:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) ==>
  EVERY (\i. MEM i.inst_opcode [ADD;ILOAD;DLOAD;MSTORE]) (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `ctor`
  >- (gvs[] >> drule code_ctor_copy_insts >> strip_tac >>
      gvs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> metis_tac[]) >>
  gvs[] >> drule code_copy_insts >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> metis_tac[]
QED

Theorem immutable_copy_nonterminators:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule immutable_copy_opcodes >>
  simp[EVERY_MEM] >> metis_tac[is_terminator_def]
QED

Theorem immutable_copy_one_nonterminators:
  immutable_copy_one ctor imm src dst off sa = ((),sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> irule immutable_copy_nonterminators >>
  qexistsl [`ctor`,`dst`,`imm`,`SUC 0`,`off`,`src`] >>
  simp[immutable_copy_suc, compile_imm_copy_to_memory_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

Theorem compile_imm_copy_to_memory_checked:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory ctor imm src (Var p) n off sa = ((),sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    copy_old_operand sa region) /\
  (!j. j < n /\ ctor ==> ?lo sz.
    (case imm of NONE => op_prov G src | SOME region => first_prov G [src;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w (off + 32*j)) /\
      w2n (a + n2w (off + 32*j)) + 32 <= lo + sz) /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  ptr_covers G tn p s cap /\ off + 32*n <= cap /\
  w2n b + off + 32*n <= dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\
    t.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem = immutable_copy_taints ctor a b n off tn.t_mem /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  Induct
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def] >> rpt strip_tac >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[copy_runtime_frame_refl, immutable_transfers_def,
           immutable_copy_taints_def, emitted_insts_def, inst_seq_ptr_def]) >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >> rpt gen_tac >> strip_tac >>
  suspend "step"
QED

Resume compile_imm_copy_to_memory_checked[step]:
  rename1 `immutable_copy_one ctor imm src (Var p) off sa = ((),sm)` >>
  `off < cap /\ off + 32 <= cap /\ w2n b + off < dimword(:256)` by
    (gvs[arithmeticTheory.MULT_SUC] >> decide_tac) >>
  `(ctor ==> ?lo sz.
    (case imm of NONE => op_prov G src | SOME region => first_prov G [src;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w off) /\
      w2n (a + n2w off) + 32 <= lo + sz)` by
    (strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all immutable_copy_one_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `t` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac)))) >>
  `copy_old_operand sm src /\ eval_operand src t = SOME a /\ op_taint tn1 src = {}` by
    (`op_taint tn1 src = op_taint tn src` by
       (irule old_operand_taint_frame >> qexists_tac `sa` >>
        gvs[copy_old_operand_def]) >>
     metis_tac[copy_old_operand_mono, copy_runtime_frame_def,
               copy_runtime_frame_operand]) >>
  `!region. ctor /\ imm = SOME region ==>
    eval_operand region t = SOME 0w /\ op_taint tn1 region = {} /\
    copy_old_operand sm region` by
    (gen_tac >> strip_tac >>
     `copy_old_operand sa region /\ eval_operand region s = SOME 0w /\
      op_taint tn region = {}` by metis_tac[] >>
     `op_taint tn1 region = op_taint tn region` by
       (irule old_operand_taint_frame >> qexists_tac `sa` >>
        gvs[copy_old_operand_def]) >>
     metis_tac[copy_runtime_frame_operand, copy_old_operand_mono, copy_runtime_frame_def]) >>
  `not_fresh_at sm p /\ lookup_var p t = SOME b /\ ptr_covers G1 tn1 p t cap` by
    (conj_tac >- (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[copy_runtime_frame_def] >>
     irule ptr_covers_copy_runtime_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  suspend "tail"
QED

Resume compile_imm_copy_to_memory_checked[tail]:
  `op_prov G1 src = op_prov G src` by
    (irule old_operand_provenance_frame >> metis_tac[]) >>
  `!region. ctor /\ imm = SOME region ==> op_prov G1 region = op_prov G region` by
    (gen_tac >> strip_tac >> irule old_operand_provenance_frame >> metis_tac[]) >>
  `!j. j < n /\ ctor ==> ?lo sz.
    (case imm of NONE => op_prov G1 src | SOME region => first_prov G1 [src;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w (off + 32 + 32*j)) /\
      w2n (a + n2w (off + 32 + 32*j)) + 32 <= lo + sz` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!j. j < SUC n /\ ctor ==> _` (qspec_then `SUC j` mp_tac) >>
     simp[arithmeticTheory.MULT_SUC] >>
     Cases_on `imm` >> gvs[first_prov_def] >>
     simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `off + 32 + 32*n <= cap /\ w2n b + (off + 32) + 32*n <= dimword(:256)` by
    (gvs[arithmeticTheory.MULT_SUC] >> decide_tac) >>
  qpat_x_assum `!off sa sb s G tn. _` drule >>
  disch_then (qspecl_then [`t`,`G1`,`tn1`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `u` (qx_choose_then `Gf`
    (qx_choose_then `tf` strip_assume_tac))) >>
  suspend "compose"
QED
Resume compile_imm_copy_to_memory_checked[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    metis_tac[immutable_copy_one_nonterminators] >>
  drule_all copy_runtime_uniform_compose >> strip_tac >>
  `(immutable_transfers F ctor a b n (off + 32) t).vs_memory =
   (immutable_transfers F ctor a b n (off + 32)
     (immutable_word_transfer F ctor a b off s)).vs_memory` by
    (irule (cj 1 immutable_transfers_cong) >> simp[] >>
     gvs[copy_runtime_frame_def, copy_static_def, venom_state_component_equality,
         immutable_transfer_data, immutable_word_transfer_fields]) >>
  qexistsl [`u`,`Gf`,`tf`] >>
  simp[immutable_transfers_def, immutable_copy_taints_def] >>
  gen_tac >> strip_tac >>
  `not_fresh_at sm x` by
    (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED
Finalise compile_imm_copy_to_memory_checked

(* The ordinary endpoint is chosen before specialization of the checked
   cursor. The counted path keeps its actual final cursor update. *)
Theorem compile_imm_copy_to_memory_path_ptr:
  compile_imm_copy_to_memory ctor imm src (Var p) n off sa = ((),sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    copy_old_operand sa region) /\
  (!j. j < n /\ ctor ==> ?lo sz.
    (case imm of NONE => op_prov G src | SOME region => first_prov G [src;region]) =
      SOME (lo,sz) /\ lo <= w2n (a + n2w (off + 32*j)) /\
      w2n (a + n2w (off + 32*j)) + 32 <= lo + sz) /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  ptr_covers G tn p s cap /\ off + 32*n <= cap /\
  w2n b + off + 32*n <= dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\
    t.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    tf.t_mem = immutable_copy_taints ctor a b n off tn.t_mem /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (off = 0 /\ 0 < n /\ (ctor ==> mem_word_taint tn.t_mem (w2n a) = {}) ==>
      mem_word_taint tf.t_mem (w2n b) = {})
Proof
  strip_tac >> drule_all compile_imm_copy_to_memory_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `t` (qx_choose_then `Gf`
      (qx_choose_then `tf` strip_assume_tac)))) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (drule immutable_copy_opcodes >> simp[EVERY_MEM] >> strip_tac >>
     gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (drule immutable_copy_opcodes >> simp[EVERY_MEM, FILTER_EQ_NIL] >> strip_tac >>
     gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    gvs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> strip_tac >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[] >> strip_tac >> gvs[] >>
  irule immutable_copy_taints_head_clean >> simp[]
QED
