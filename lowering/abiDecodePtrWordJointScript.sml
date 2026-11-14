(* A primitive decoder's operational and ghost endpoints are fixed before
   choosing a horizon or an explicit GAS-site set. *)
Theory abiDecodePtrWordJoint
Ancestors
  abiDecodePtrWord abiDecodePtrMemberFrame abiDecoderReentryPointer
  abiDecoderClampedWord abiDecoderContract abiDecoderVarSequence
  abiDecoderTypedCompose fragGasCopyLoop fragGasOriginPtrDead
  fragGasOriginPtr fragGasSeqPtr fragExecMem fragExec
  entryDecoderHistoryFrame emitHelperProps exprLoweringProps bodyPtrDefs ptrDiscipline
  venomState venomExecSemantics venomInst words list rich_list arithmetic

Theorem abi_decode_word_joint_code:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecPrimWord clamp) sa = ((),sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    s.vs_inst_idx+LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule abi_decoder_inst_extends_prefix >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       ~is_alloca_op i.inst_opcode` by
       (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then drule >> simp[]) >>
     `abi_decoder_reentry_opcode i.inst_opcode` by
       (qpat_assum `EVERY (\i. abi_decoder_reentry_opcode _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then drule >> simp[]) >>
     `i.inst_opcode <> ALLOCA` by
       (CCONTR_TAC >> gvs[is_alloca_op_def]) >>
     `i.inst_opcode <> GAS` by
       (CCONTR_TAC >> gvs[abi_decoder_reentry_opcode_def]) >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    fs[inst_extends_def] >>
  qexists_tac `bb` >> simp[]
QED

Theorem abi_decode_word_success_joint:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecPrimWord clamp) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s 32 /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= h /\ w2n b+h < dimword(:256) /\
  w2n b+h <= s.vs_alloca_next /\ w2n d+32 <= s.vs_alloca_next /\
  (w2n b+h <= w2n d \/ w2n d+32 <= w2n b) /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    abi_decode_ptr_window G' tn' u dst d 32 /\
    abi_decode_ptr_window G' tn' u src b h /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n d <= i /\ i < w2n d+32) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    allocas_from lo u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all abi_decode_word_mem_ok >> simp[]) >>
  drule_all (abi_decode_word_success_ptr |> Q.INST
    [`D` |-> `<| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |>`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all abi_decode_word_joint_code >> strip_tac >>
  `!explicit. gas_origin_ptr_path
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
     lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
    allocas_from lo u` by
    (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  metis_tac[]
QED

Theorem abi_decode_word_abort_joint:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecPrimWord clamp) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s 32 /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= h /\ w2n b+h < dimword(:256) /\
  w2n b+h <= s.vs_alloca_next /\ w2n d+32 <= s.vs_alloca_next /\
  (w2n b+h <= w2n d \/ w2n d+32 <= w2n b) /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?j G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort a (u with vs_inst_idx := j),G',tn')) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all abi_decode_word_mem_ok >> simp[]) >>
  drule_all (abi_decode_word_abort_ptr |> Q.INST
    [`D` |-> `<| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |>`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all abi_decode_word_joint_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `inst_seq_ptr
    <| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>
    lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (irule (inst_seq_ptr_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
     simp[] >> fs[EVERY_MEM]) >>
  `!explicit. gas_origin_ptr_path
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
     lo,explicit,ctx,func,PG) (s,G,tn) [] (Abort a (u with vs_inst_idx := j),G',tn')` by
    (gen_tac >> qpat_assum `!D lo explicit PG G tn HG th. _`
       (qspecl_then
         [`<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`,
          `lo`, `explicit`, `PG`, `G`, `tn`, `G'`, `tn'`] irule) >> simp[]) >>
  `u.vs_allocas = s.vs_allocas` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _;
        vs_halted := _; vs_returndata := _|>) = s`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_allocas``) >> simp[]) >>
  qexistsl_tac [`j`, `G'`, `tn'`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  fs[allocas_from_def] >> metis_tac[]
QED
