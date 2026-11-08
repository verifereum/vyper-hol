Theory abiDecodePtrBytesSuccess
Ancestors
  abiDecodePtrBytesMember abiDecodePtrBytesTailWindow abiDecodePtrMemberFrame
  abiDecodePtrBytesPrefixLive abiDecodePtrBytesTail
  assignTuplePtrLocalBytesCopy emitHelperProps exprLoweringProps
  abiEncoder compileEnv context bodyPtrDefs ptrDiscipline
  venomExecSemantics venomState venomInst words arithmetic list finite_map

Theorem abi_decode_bytes_member_success_ptr:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ fresh_vars_wrt sa s /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s cap /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p < dimword(:256) /\ n+31 < dimword(:256) /\
  32+contractABI$ceil32 n <= cap /\ w2n d+cap < dimword(:256) /\
  w2n b+h < dimword(:256) /\
  (w2n b+h <= w2n d \/ w2n d+cap <= w2n b) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
    abi_decode_ptr_window Gf tnf u src b h /\
    abi_decode_ptr_window Gf tnf u dst d
      (32+contractABI$ceil32 (w2n (mload (w2n b+p) s))) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n d <= i /\
           i < w2n d+32+contractABI$ceil32 (w2n (mload (w2n b+p) s))) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bytes_member_prefix_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `not_fresh_at c5 src` by metis_tac[] >>
  `abi_decode_ptr_window G5 tn5 s5 src (n2w (w2n b)) h /\
   abi_decode_ptr_window G5 tn5 s5 ar (n2w (w2n b+p))
     (32+w2n (mload (w2n b+p) s))` by
    (conj_tac >- simp[] >>
     pure_rewrite_tac[GSYM word_add_n2w, n2w_w2n] >>
     first_assum ACCEPT_TAC) >>
  `lookup_var dst s5 = SOME (n2w (w2n d))` by simp[] >>
  drule_all abi_decode_bytes_runtime_tail_windows >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule abiDecoderBytesPhasesTheory.abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa c5 ++ emitted_insts c5 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule abiDecoderBytesPhasesTheory.abi_decode_bytes_position_shape >>
     simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
     strip_tac >> fs[EVERY_MEM]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c5) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c5 sb)` by
    metis_tac[EVERY_APPEND] >>
  `s5.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c5) /\
   t.vs_inst_idx = s5.vs_inst_idx + LENGTH (emitted_insts c5 sb)` by
    (fs[inst_extends_def] >> decide_tac) >>
  drule_all inst_seq_ptr_append_normalized >> strip_tac >>
  `u = t with vs_inst_idx := s.vs_inst_idx` by
    (qpat_assum `run_inst_seq (_ ++ _) s = _` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[]) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qpat_assum `abi_decode_ptr_window Gf tnf t src _ h` mp_tac >>
     qpat_assum `u = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[abi_decode_ptr_window_def, ptr_covers_def, lookup_var_def, w2n_lt]) >>
  conj_tac >-
    (qpat_assum `abi_decode_ptr_window Gf tnf t dst _ _` mp_tac >>
     qpat_assum `u = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[abi_decode_ptr_window_def, ptr_covers_def, lookup_var_def, w2n_lt]) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     `not_fresh_at c5 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at c5 x ==> lookup_var x t = _ /\ _` drule >>
     strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s5 = _ /\ _` drule >>
     strip_tac >> gvs[lookup_var_def]) >>
  simp[]
QED
