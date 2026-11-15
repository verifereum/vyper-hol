(* Joint certificates for the allocated static-array payload copy. *)
Theory abiDecodePtrBulkJoint
Ancestors
 abiDecoderBulk abiMalformedBulkArray abiDecodePtrArrayJoint
 abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderRange abiDecoderComposition abiDecoderArrayInitExec
 exprSimAccounts stateFrame ghostPcTransportPtr
 abiDecodePtrRead abiDecodePtrBytesTail abiDecodePtrScalarFrame abiDecodePtrMemberFrame
 bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
 assignTuplePtrLocalBytesCopy assignTuplePtrBytesCopy assignTuplePtrCopyLen
 decoderGhostFramePtr instSeqComposePtr
 abiDecodePtrReentry abiDecodePtrReentryGhost abiDecodeMemReentry
 abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderAbortReentry
 fragGasCopyLoop fragGasOriginPtrDead fragGasOriginPtr ptrSafetyTransport
 bodyFullUnwrapRun bodyPtrBopHashSuffix entryDecoderHistoryFrame
 wordLoadStorePtr allocaFootprint abiEncoder abiDecoderContract
 emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
 bodyPtrDefs ptrDiscipline fragExecMem fragExec fragGasSeqPtr
 venomExecSemantics venomState venomInst venomMemDefs instIdxIndep
 finite_map pred_set words list rich_list arithmetic moduleLoweringProps

Theorem abi_decode_bulk_payload_joint_code:
 abi_decode_bulk_payload (Var output) pos cnt mem_sz MLOAD (Var source) sa = ((),sb) ==>
 inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
 EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
 simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
   abi_decode_copy_opcode_def, comp_bind_def, comp_ignore_bind_def,
   emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, comp_return_def, emit_def] >>
 strip_tac >> gvs[emitted_insts_def, inst_extends_def, same_blocks_def] >>
 pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
 simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def, is_terminator_def]
QED

Theorem abi_decode_bulk_payload_scalar_prefix[local]:
 emit_op MUL [cnt;Lit (n2w mem_sz)] sa = (copy_sz,c1) /\
 emit_op ADD [pos;Lit 32w] c1 = (src_data,c2) ==>
 bop_scalar_seq {x | not_fresh_at sa x}
   ({cnt;pos} UNION IMAGE Lit UNIV) (emitted_insts sa c2)
   (src_data INSERT copy_sz INSERT ({cnt;pos} UNION IMAGE Lit UNIV))
Proof
 strip_tac >>
 qpat_assum `emit_op MUL _ sa = _`
   (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
 `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
 `bop_scalar_seq {x | not_fresh_at sa x} ({cnt;pos} UNION IMAGE Lit UNIV)
    (emitted_insts sa c1) (copy_sz INSERT ({cnt;pos} UNION IMAGE Lit UNIV))` by
   (irule bop_scalar_seq_emit_op >> simp[] >>
    qexistsl_tac [`MUL`, `[cnt;Lit (n2w mem_sz)]`] >> simp[]) >>
 `bop_scalar_seq {x | not_fresh_at sa x} (copy_sz INSERT ({cnt;pos} UNION IMAGE Lit UNIV))
    (emitted_insts c1 c2)
    (src_data INSERT copy_sz INSERT ({cnt;pos} UNION IMAGE Lit UNIV))` by
   (irule bop_scalar_seq_emit_op >> simp[] >>
    qexistsl_tac [`ADD`, `[pos;Lit 32w]`] >> simp[]) >>
 imp_res_tac emit_op_extends >>
 `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
   (irule emitted_insts_append >> simp[]) >>
 qpat_assum `emitted_insts sa c2 = _` (fn th => once_rewrite_tac[th]) >>
 irule bop_scalar_seq_append >>
 qexists_tac `copy_sz INSERT ({cnt;pos} UNION IMAGE Lit UNIV)` >>
 conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_bulk_payload_fresh_ptr[local]:
 abi_decode_bulk_payload (Var output) pos cnt mem_sz MLOAD (Var source) sa = ((),sb) /\
 run_inst_seq (emitted_insts sa sb) s = OK u /\ fresh_vars_wrt sa s /\
 fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa output /\ not_fresh_at sa source /\
 (!x. pos = Var x ==> not_fresh_at sa x) /\
 (!x. cnt = Var x ==> not_fresh_at sa x) /\
 lookup_var output s = SOME (n2w d) /\ ptr_covers G tn output s cap /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 eval_operand pos s = SOME (n2w p) /\ eval_operand cnt s = SOME (n2w n) /\
 op_prov G pos = NONE /\ op_taint tn pos = {} /\
 op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
 p+32+n*mem_sz <= L /\ 32+n*mem_sz <= cap /\
 B+L < dimword (:256) /\ d+cap < dimword (:256) /\
 B+L <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
 (B+L <= d \/ d+cap <= B) /\ allocas_from lo s ==>
 ?G' tn'.
 inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
 run_inst_seq_mem_ok (emitted_insts sa sb) s /\
 ptr_covers G' tn' output u cap /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!i. d+32 <= i /\ i < d+32+n*mem_sz ==> i NOTIN tn'.t_mem) /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_mem = tn.t_mem DIFF {i | d+32 <= i /\ i < d+32+n*mem_sz} /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
 allocas_from lo u
Proof
 strip_tac >>
 `?copy_sz c1 src_data c2 src_addr c3 dst_data c4.
   emit_op MUL [cnt;Lit (n2w mem_sz)] sa = (copy_sz,c1) /\
   emit_op ADD [pos;Lit 32w] c1 = (src_data,c2) /\
   compile_abi_dec_addr (Var source) src_data c2 = (src_addr,c3) /\
   emit_op ADD [Var output;Lit 32w] c3 = (dst_data,c4) /\
   emit_void MCOPY [dst_data;src_addr;copy_sz] c4 = ((),sb)` by
   (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
    simp[abi_decode_bulk_payload_def, abi_decode_copy_opcode_def, comp_bind_def] >>
    rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]) >>
 `emit_op ADD [Var source;src_data] c2 = (src_addr,c3)` by
   fs[compile_abi_dec_addr_def] >>
 `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 c3 /\
  inst_extends c3 c4 /\ inst_extends c4 sb` by
   metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
 `same_blocks sa c1 /\ same_blocks c1 c2 /\ same_blocks c2 c3 /\
  same_blocks c3 c4 /\ same_blocks c4 sb` by
   metis_tac[emit_op_extends, emit_void_extends] >>
 `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
  c2.cs_next_var <= c3.cs_next_var /\ c3.cs_next_var <= c4.cs_next_var /\
  c4.cs_next_var <= sb.cs_next_var` by
   (imp_res_tac emit_op_extends_next_var >>
    drule emitted_insts_emit_void >> strip_tac >> simp[]) >>
 `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\
  cs_extends c3 c4 /\ cs_extends c4 sb` by
   (rpt conj_tac >> irule cs_extends_same_block >>
    fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
 `cs_extends c3 sb /\ cs_extends c2 sb /\ cs_extends c1 sb` by
   metis_tac[cs_extends_trans] >>
 `fn_has_code c1 sb func /\ fn_has_code c2 sb func /\
  fn_has_code c3 sb func /\ fn_has_code c4 sb func /\
  fn_has_code c2 c3 func` by metis_tac[fn_has_code_split] >>
 `inst_extends sa c2 /\ inst_extends c2 c4 /\ inst_extends sa sb` by
   metis_tac[inst_extends_trans] >>
 `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2 /\
  emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 c3 ++
    emitted_insts c3 c4 ++ emitted_insts c4 sb` by
   (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
 `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
 drule_all abi_decode_mul_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts sa c1) s = OK r1` >>
 `eval_operand pos r1 = SOME (n2w p) /\
  eval_operand (Lit 32w) r1 = SOME 32w` by
   (simp[eval_operand_def] >> metis_tac[]) >>
 drule_all abi_decode_add_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts c1 c2) r1 = OK r2` >>
 `run_inst_seq (emitted_insts sa c2) s = OK r2` by
   (drule_all abi_decode_sequence_chain >> simp[]) >>
 `eval_operand copy_sz r2 = SOME (n2w (n*mem_sz)) /\
  eval_operand src_data r2 = SOME (n2w (p+32))` by
   (conj_tac
    >- (qpat_assum `!op w. eval_operand op r1 = SOME w ==> _`
          (qspecl_then [`copy_sz`, `n2w n * n2w mem_sz`] mp_tac) >>
        simp[word_mul_n2w, MULT_COMM]) >>
    simp[word_add_n2w]) >>
 drule_all abi_decode_bulk_payload_scalar_prefix >> strip_tac >>
 `!op. op IN {cnt;pos} UNION IMAGE Lit UNIV ==>
   op_prov G op = NONE /\ op_taint tn op = {}` by
   (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
 drule_all abi_decode_scalar_success_frame >>
 disch_then (qspecl_then [`LENGTH c2.cs_current_insts`, `func`, `PG`, `D`]
   strip_assume_tac) >>
 rename1 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa c2) s G1 tn1` >>
 qabbrev_tac `s2 = r2 with vs_inst_idx := LENGTH c2.cs_current_insts` >>
 `abi_decode_ptr_window G1 tn1 s2 source (n2w B) L /\
  ptr_covers G1 tn1 output s2 cap` by
   (conj_tac >> first_x_assum irule >> simp[]) >>
 `B < dimword (:256) /\ p+32 <= L /\ n*mem_sz < dimword (:256)` by decide_tac >>
 `eval_operand src_data s2 = SOME (n2w (p+32)) /\
  op_prov G1 src_data = NONE /\ op_taint tn1 src_data = {} /\
  ~s2.vs_halted /\ s2.vs_current_bb = c2.cs_current_bb /\
  s2.vs_inst_idx = LENGTH c2.cs_current_insts /\ fresh_vars_wrt c2 s2` by
   (fs[Abbr `s2`, eval_operand_def, lookup_var_def, fresh_vars_wrt_def,
       same_blocks_def] >>
    qpat_assum `r2 = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
 mp_tac (abi_decode_ptr_address |> Q.INST
   [`sa` |-> `c2`, `sb` |-> `c3`, `src` |-> `source`, `pos` |-> `src_data`,
    `addr` |-> `src_addr`,
    `s` |-> `s2`, `G` |-> `G1`, `tn` |-> `tn1`, `b` |-> `n2w B`,
    `h` |-> `L`, `p` |-> `p+32`, `D` |-> `D`, `PG` |-> `PG`]) >>
 (impl_tac >- simp[w2n_n2w]) >> strip_tac >>
 rename1 `src_addr = Var source_data` >>
 qpat_x_assum `src_addr = Var source_data` SUBST_ALL_TAC >>
 rename1 `inst_seq_ptr D 0 ctx func PG G1 tn1 (emitted_insts c2 c3) s2 G2 tn2` >>
 rename1 `abi_decode_ptr_window G2 tn2 s3 source_data _ _` >>
 `abi_decoder_operand_live c2.cs_next_var copy_sz` by
   (irule abi_decoder_operand_live_fresh >>
    qexistsl_tac [`r2`, `n2w (n*mem_sz)`] >> simp[]) >>
 `!x. copy_sz = Var x ==> not_fresh_at c2 x` by
   (Cases_on `copy_sz` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `not_fresh_at c2 output /\ not_fresh_at c2 source` by
   (qpat_assum `not_fresh_at sa output` mp_tac >>
    qpat_assum `not_fresh_at sa source` mp_tac >>
    qpat_assum `sa.cs_next_var <= c1.cs_next_var` mp_tac >>
    qpat_assum `c1.cs_next_var <= c2.cs_next_var` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `abi_decode_ptr_window G2 tn2 s3 source (n2w B) L /\
  ptr_covers G2 tn2 output s3 cap /\ lookup_var output s3 = SOME (n2w d)` by
   (conj_tac
    >- (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G1`, `s2`, `tn1`] >>
        simp[] >> qpat_assum `!x. not_fresh_at c2 x ==> _` drule >> simp[]) >>
    conj_tac
    >- (irule ptr_covers_frame >> qexistsl_tac [`G1`, `s2`, `tn1`] >>
        simp[] >> qpat_assum `!x. not_fresh_at c2 x ==> _` drule >> simp[]) >>
    qpat_assum `!x. not_fresh_at c2 x ==> _` (qspec_then `output` mp_tac) >>
    qpat_assum `!x. x IN _ ==> lookup_var x s2 = _ /\ _`
      (qspec_then `output` mp_tac) >> simp[]) >>
 `s3.vs_labels = s2.vs_labels` by
   (qpat_assum `state_frame s3 = _` mp_tac >>
    simp_tac (srw_ss()) [state_frame_def, venom_state_component_equality]) >>
 `eval_operand copy_sz s3 = SOME (n2w (n*mem_sz)) /\ op_taint tn2 copy_sz = {}` by
   (mp_tac (abi_decode_scalar_protected_operand |> Q.INST
      [`op` |-> `copy_sz`, `s` |-> `s2`, `t` |-> `s3`, `G` |-> `G1`, `H` |-> `G2`,
       `tn` |-> `tn1`, `tm` |-> `tn2`, `R` |-> `{x | not_fresh_at c2 x}`]) >>
    (impl_tac >- simp[]) >> strip_tac >> simp[Abbr `s2`, eval_operand_def, lookup_var_def]) >>
 `?dest_data. dst_data = Var dest_data` by
   (qpat_assum `emit_op ADD [Var output;Lit 32w] c3 = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
 qpat_x_assum `dst_data = Var dest_data` SUBST_ALL_TAC >>
 `op_taint tn2 (Var output) = {} /\
  op_taint tn2 (Lit 32w) = {} /\ eval_operand (Lit 32w) s3 = SOME (n2w 32)` by
   fs[ptr_covers_def, eval_operand_def, op_taint_def] >>
 mp_tac (abi_decode_ptr_output_address |> SRULE [LET_THM] |> Q.INST
   [`sa` |-> `c3`, `sb` |-> `c4`, `dst` |-> `output`, `pos` |-> `Lit 32w`,
    `out` |-> `dest_data`, `s` |-> `s3`, `G` |-> `G2`, `tn` |-> `tn2`,
    `b` |-> `n2w d`, `q` |-> `32`, `k` |-> `n*mem_sz`, `cap` |-> `cap`,
    `D` |-> `D`, `PG` |-> `PG`]) >>
 (impl_tac >- (simp[w2n_n2w] >> decide_tac)) >> strip_tac >>
 qabbrev_tac `s4 = update_var dest_data (n2w d+n2w 32) s3 with
    vs_inst_idx := LENGTH c4.cs_current_insts` >>
 qabbrev_tac `G3 = step_prov PG G2
    (mk_inst c3.cs_next_id ADD [Var output;Lit 32w] [dest_data])
    (update_var dest_data (n2w d+n2w 32) s3)` >>
 qabbrev_tac `tn3 = step_taint
    (mk_inst c3.cs_next_id ADD [Var output;Lit 32w] [dest_data]) s3
    (update_var dest_data (n2w d+n2w 32) s3) tn2` >>
 `inst_seq_ptr D 0 ctx func PG G2 tn2 (emitted_insts c3 c4) s3 G3 tn3 /\
  run_inst_seq (emitted_insts c3 c4) s3 = OK (s4 with vs_inst_idx := s3.vs_inst_idx) /\
  ptr_covers G3 tn3 dest_data s4 (n*mem_sz) /\
  lookup_var dest_data s4 = SOME (n2w (d+32))` by
   simp[Abbr `s4`, Abbr `G3`, Abbr `tn3`, word_add_n2w] >>
 `not_fresh_at c3 source_data /\ not_fresh_at c3 source /\
  not_fresh_at c3 output /\ (!x. copy_sz = Var x ==> not_fresh_at c3 x)` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `abi_decode_ptr_window G2 tn2 s3 source_data (n2w (B+p+32)) (L-(p+32))` by
   (qpat_assum `abi_decode_ptr_window G2 tn2 s3 source_data _ _` mp_tac >>
    simp_tac (srw_ss()) [word_add_n2w, ADD_ASSOC]) >>
 `abi_decode_ptr_window G3 tn3 s4 source_data
   (n2w (B+p+32)) (L-(p+32)) /\
  abi_decode_ptr_window G3 tn3 s4 source (n2w B) L /\
  ptr_covers G3 tn3 output s4 cap` by
   (rpt conj_tac
    >- (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G2`, `s3`, `tn2`] >>
        qpat_assum `!x. not_fresh_at c3 x ==> _` (qspec_then `source_data` mp_tac) >>
        asm_simp_tac bool_ss [word_add_n2w, ADD_ASSOC])
    >- (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G2`, `s3`, `tn2`] >>
        qpat_assum `!x. not_fresh_at c3 x ==> _` (qspec_then `source` mp_tac) >>
        asm_simp_tac bool_ss []) >>
    irule ptr_covers_frame >> qexistsl_tac [`G2`, `s3`, `tn2`] >>
    qpat_assum `!x. not_fresh_at c3 x ==> _` (qspec_then `output` mp_tac) >>
    asm_simp_tac bool_ss []) >>
 `s4.vs_labels = s3.vs_labels /\ s4.vs_inst_idx = LENGTH c4.cs_current_insts /\
  s4.vs_alloca_next = s3.vs_alloca_next` by
   simp_tac (srw_ss()) [Abbr `s4`, update_var_def] >>
 `B+p+32 < dimword (:256) /\ d+32 < dimword (:256)` by decide_tac >>
 `eval_operand copy_sz s4 = SOME (n2w (n*mem_sz)) /\ op_taint tn3 copy_sz = {}` by
   (mp_tac (abi_decode_scalar_protected_operand |> Q.INST
      [`op` |-> `copy_sz`, `s` |-> `s3`, `t` |-> `s4`, `G` |-> `G2`, `H` |-> `G3`,
       `tn` |-> `tn2`, `tm` |-> `tn3`, `R` |-> `{x | not_fresh_at c3 x}`]) >>
    (impl_tac >- simp[]) >> simp[]) >>
 mp_tac (abi_decode_ptr_copy_windows |> Q.INST
   [`sa` |-> `c4`, `sb` |-> `sb`, `dst` |-> `dest_data`, `src` |-> `source_data`,
    `count_op` |-> `copy_sz`, `s` |-> `s4`, `G` |-> `G3`, `tn` |-> `tn3`,
    `a` |-> `n2w (B+p+32)`, `b` |-> `n2w (d+32)`, `h` |-> `L-(p+32)`,
    `k` |-> `n*mem_sz`, `D` |-> `D`, `fn` |-> `func`, `PG` |-> `PG`]) >>
 (impl_tac >- (simp[w2n_n2w] >> decide_tac)) >> strip_tac >>
 rename1 `inst_seq_ptr D 0 ctx func PG G3 tn3 (emitted_insts c4 sb) s4 G3 tn4` >>
 rename1 `abi_decode_ptr_window G3 tn4 s5 dest_data _ _` >>
 `c2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c2 /\
  c3.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 c3 /\
  c4.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 c4` by
   (conj_tac
    >- (qpat_assum `inst_extends sa c2` (ACCEPT_TAC o REWRITE_RULE [inst_extends_def])) >>
    conj_tac
    >- (qpat_assum `inst_extends c2 c3` (ACCEPT_TAC o REWRITE_RULE [inst_extends_def])) >>
    qpat_assum `inst_extends c3 c4` (ACCEPT_TAC o REWRITE_RULE [inst_extends_def])) >>
 `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c2) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 c3) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 c4)` by
   (drule abi_decode_bulk_payload_joint_code >> strip_tac >>
    qpat_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
    qpat_assum `emitted_insts sa sb = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
 `run_inst_seq (emitted_insts sa c2) s = OK (s2 with vs_inst_idx := s.vs_inst_idx)` by
   (simp[Abbr `s2`, venom_state_component_equality] >>
    qpat_assum `r2 = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
 mp_tac (emitted_insts_join_normalized_ptr |> Q.INST
   [`sa` |-> `sa`, `sb` |-> `c2`, `sc` |-> `c3`, `t` |-> `s2`, `u` |-> `s3`, `fn` |-> `func`]) >>
 (impl_tac >- (simp[Abbr `s2`] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
 mp_tac (emitted_insts_join_normalized_ptr |> Q.INST
   [`sa` |-> `sa`, `sb` |-> `c3`, `sc` |-> `c4`, `t` |-> `s3`, `u` |-> `s4`, `fn` |-> `func`,
    `G1` |-> `G2`, `tn1` |-> `tn2`, `G2` |-> `G3`, `tn2` |-> `tn3`]) >>
 (impl_tac >- (simp[Abbr `s4`] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
 mp_tac (emitted_insts_join_normalized_ptr |> Q.INST
   [`sa` |-> `sa`, `sb` |-> `c4`, `sc` |-> `sb`, `t` |-> `s4`, `u` |-> `s5`, `fn` |-> `func`,
    `G1` |-> `G3`, `tn1` |-> `tn3`, `G2` |-> `G3`, `tn2` |-> `tn4`]) >>
 (impl_tac >- (simp[Abbr `s4`] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
 `u = s5 with vs_inst_idx := s.vs_inst_idx` by gvs[] >>
 `!x. not_fresh_at sa x ==> not_fresh_at c2 x /\ not_fresh_at c3 x` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `!x. not_fresh_at sa x ==>
   lookup_var x s5 = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
   op_taint tn4 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    qpat_assum `!x. x IN _ ==> lookup_var x s2 = _ /\ _`
      (qspec_then `x` mp_tac) >>
    qpat_assum `!x. not_fresh_at c2 x ==> _` (qspec_then `x` mp_tac) >>
    qpat_assum `!x. not_fresh_at c3 x ==> _` (qspec_then `x` mp_tac) >>
    qpat_assum `!p. lookup_var p s5 = _ /\ _` (qspec_then `x` mp_tac) >>
    qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at c2 x /\ _`
      (qspec_then `x` mp_tac) >>
    qpat_assum `not_fresh_at sa x` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[GSPECIFICATION] >> metis_tac[]) >>
 `tn3.t_mem = tn.t_mem` by asm_simp_tac bool_ss [] >>
 `tn4.t_mem = tn.t_mem DIFF {i | d+32 <= i /\ i < d+32+n*mem_sz}` by
   (simp[EXTENSION, IN_DIFF, GSPECIFICATION] >> rpt gen_tac >>
    Cases_on `d+32 <= x /\ x < d+32+n*mem_sz`
    >- (qpat_assum `abi_decode_ptr_window G3 tn4 s5 dest_data _ _`
          (qspec_then `x` mp_tac o CONJUNCT2 o CONJUNCT2 o
            REWRITE_RULE [abi_decode_ptr_window_def]) >> simp[w2n_n2w]) >>
    qpat_assum `!i. ~(_ /\ _) ==> mem_bytes_at _ _ s5.vs_memory = _ /\ _`
      (qspec_then `x` mp_tac) >> simp[w2n_n2w] >> metis_tac[]) >>
 `!x. not_fresh_at sa x ==>
   lookup_var x u = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
   op_taint tn4 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s5 = _ /\ _`
      (qspec_then `x` mp_tac) >>
    qpat_assum `not_fresh_at sa x` mp_tac >>
    qpat_assum `u = s5 with vs_inst_idx := _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
 `w2n (n2w B:bytes32) = B` by simp[w2n_n2w] >>
 `ptr_covers G3 tn4 output u cap /\
  abi_decode_ptr_window G3 tn4 u source (n2w B) L` by
   (conj_tac
    >- (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
        qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
          (qspec_then `output` mp_tac) >> asm_simp_tac bool_ss []) >>
    irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
      (qspec_then `source` mp_tac) >>
    asm_simp_tac bool_ss [] >> rpt strip_tac >>
    `~(d+32 <= i /\ i < d+32+n*mem_sz)` by decide_tac >>
    simp[IN_DIFF, GSPECIFICATION]) >>
 `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
   (drule abi_decode_bulk_payload_joint_code >> strip_tac >>
    `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       ~is_alloca_op i.inst_opcode) (emitted_insts sa sb)` by
      (qpat_assum `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ _) (emitted_insts sa sb)` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [EVERY_MEM] >>
       strip_tac >> gen_tac >> strip_tac >>
       qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `i` mp_tac) >>
       Cases_on `i.inst_opcode` >> simp[is_alloca_op_def]) >>
    drule_all abi_decoder_guard_sequence_fields >> simp[]) >>
 `allocas_from lo u` by (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
 `run_inst_seq_mem_ok (emitted_insts sa c4) s` by
   (irule run_inst_seq_mem_ok_every >>
    qpat_assum `emit_op MUL _ sa = _` mp_tac >>
    qpat_assum `emit_op ADD [pos;Lit 32w] c1 = _` mp_tac >>
    qpat_assum `emit_op ADD [Var source;src_data] c2 = _` mp_tac >>
    qpat_assum `emit_op ADD [Var output;Lit 32w] c3 = _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[emitted_insts_def] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
    simp[DROP_LENGTH_APPEND, instMemFrontierTheory.below_frontier_no_ranges, mk_inst_def,
      memSafeRunTheory.inst_dload_in_section_other]) >>
 `s3.vs_alloca_next = s2.vs_alloca_next` by
   (qpat_assum `state_frame s3 = _`
      (mp_tac o AP_TERM ``\state:venom_state. state.vs_alloca_next``) >>
    simp_tac (srw_ss()) [state_frame_def]) >>
 `s2.vs_alloca_next = s.vs_alloca_next` by
   (qpat_assum `r2 = s with vs_vars := _`
      (mp_tac o AP_TERM ``\state:venom_state. state.vs_alloca_next``) >>
    simp_tac (srw_ss()) [Abbr `s2`]) >>
 `s4.vs_alloca_next = s.vs_alloca_next` by asm_simp_tac bool_ss [] >>
 `eval_operand (Var dest_data) s4 = SOME (n2w (d+32))` by simp[eval_operand_def] >>
 `eval_operand (Var source_data) s4 = SOME (n2w (B+p+32))` by
   (qpat_assum `abi_decode_ptr_window G3 tn3 s4 source_data _ _` mp_tac >>
    simp_tac (srw_ss()) [abi_decode_ptr_window_def, eval_operand_def]) >>
 `w2n (n2w (d+32):bytes32) = d+32 /\
  w2n (n2w (B+p+32):bytes32) = B+p+32 /\
  w2n (n2w (n*mem_sz):bytes32) = n*mem_sz` by simp[w2n_n2w] >>
 `run_inst_seq_mem_ok (emitted_insts c4 sb) s4` by
   (mp_tac (Q.SPECL [`Var dest_data`, `Var source_data`, `copy_sz`, `c4`, `sb`, `s4`,
      `n2w (d+32):bytes32`, `n2w (B+p+32):bytes32`, `n2w (n*mem_sz):bytes32`]
      emit_mcopy_mem_ok) >>
    (impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac)) >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
   (`emitted_insts sa sb = emitted_insts sa c4 ++ emitted_insts c4 sb` by
      (irule emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
    qpat_assum `emitted_insts sa sb = emitted_insts sa c4 ++ _`
      (fn th => once_rewrite_tac[th]) >>
    irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >>
    `s' = s4 with vs_inst_idx := s.vs_inst_idx` by gvs[] >>
    qpat_x_assum `s' = _` SUBST_ALL_TAC >> simp[]) >>
 (qexistsl_tac [`G3`, `tn4`] >> rpt conj_tac
 >- first_assum ACCEPT_TAC
 >- first_assum ACCEPT_TAC
 >- first_assum ACCEPT_TAC
 >- first_assum ACCEPT_TAC
 >- (simp[IN_DIFF, GSPECIFICATION])
 >- first_assum ACCEPT_TAC
 >- first_assum ACCEPT_TAC
 >- asm_simp_tac bool_ss []
 >- asm_simp_tac bool_ss []
 >- asm_simp_tac bool_ss []
 >- first_assum ACCEPT_TAC
 >- first_assum ACCEPT_TAC
 >- first_assum ACCEPT_TAC)
QED

Theorem abi_decode_bulk_payload_success_joint:
 abi_decode_bulk_payload (Var output) pos cnt mem_sz MLOAD (Var source) sa = ((),sb) /\
 run_inst_seq (emitted_insts sa sb) s = OK u /\
 fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa output /\ not_fresh_at sa source /\
 (!x. pos = Var x ==> not_fresh_at sa x) /\
 (!x. cnt = Var x ==> not_fresh_at sa x) /\
 lookup_var output s = SOME (n2w d) /\ ptr_covers G tn output s cap /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 eval_operand pos s = SOME (n2w p) /\ eval_operand cnt s = SOME (n2w n) /\
 op_prov G pos = NONE /\ op_taint tn pos = {} /\
 op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
 p+32+n*mem_sz <= L /\ 32+n*mem_sz <= cap /\
 B+L < dimword (:256) /\ d+cap < dimword (:256) /\
 B+L <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
 (B+L <= d \/ d+cap <= B) /\ allocas_from lo s ==>
 ?G' tn'.
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
 ptr_covers G' tn' output u cap /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!i. d+32 <= i /\ i < d+32+n*mem_sz ==> i NOTIN tn'.t_mem) /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_mem = tn.t_mem DIFF {i | d+32 <= i /\ i < d+32+n*mem_sz} /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
 allocas_from lo u
Proof
 strip_tac >>
 drule abi_decode_bulk_payload_joint_code >> strip_tac >>
 `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
 qabbrev_tac `ps = abi_decoder_prune_vars sa.cs_next_var s` >>
 `abi_decoder_operand_live sa.cs_next_var pos /\
  abi_decoder_operand_live sa.cs_next_var cnt /\
  abi_decoder_operand_live sa.cs_next_var (Var source) /\
  abi_decoder_operand_live sa.cs_next_var (Var output)` by
   (Cases_on `pos` >> Cases_on `cnt` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `B < dimword (:256) /\ d < dimword (:256) /\
  B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256)` by decide_tac >>
 `eval_operand (Var source) s = SOME (n2w B) /\
  eval_operand (Var output) s = SOME (n2w d)` by
   fs[abi_decode_ptr_window_def, eval_operand_def] >>
 `eval_operand (Var source) ps = SOME (n2w B) /\
  eval_operand (Var output) ps = SOME (n2w d) /\
  eval_operand pos ps = SOME (n2w p) /\
  eval_operand cnt ps = SOME (n2w n) /\ fresh_vars_wrt sa ps` by
   simp[Abbr `ps`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
 mp_tac (abi_malformed_bulk_payload_exact |> Q.INST
   [`st` |-> `sa`, `en` |-> `sb`, `dst` |-> `Var output`, `src` |-> `pos`,
    `base_op` |-> `Var source`, `s` |-> `ps`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts sa sb) ps = OK clean` >>
 `abi_decode_ptr_window G tn ps source (n2w B) L /\
  ptr_covers G tn output ps cap /\ lookup_var output ps = SOME (n2w d)` by
   (fs[abi_decode_ptr_window_def] >>
    simp[Abbr `ps`, abi_decode_ptr_prune_covers, abi_decoder_prune_vars_def,
      lookup_var_def, FLOOKUP_DRESTRICT] >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def,
      lookup_var_def]) >>
 mp_tac (abi_decode_bulk_payload_fresh_ptr |> Q.INST
   [`s` |-> `ps`, `u` |-> `clean`,
    `D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
 (impl_tac >- (simp[Abbr `ps`, abi_decoder_prune_vars_def, allocas_from_def] >>
    qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >> strip_tac >>
 `abi_decoder_vars_extend s.vs_vars ps s` by
   simp[Abbr `ps`, abi_decoder_prune_extension] >>
 drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
 rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
 `actual = u` by gvs[] >> qpat_x_assum `actual = u` SUBST_ALL_TAC >>
 drule_all abi_decoder_vars_extend_observations >> strip_tac >>
 `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
   (drule_all abi_decode_sequence_mem_reentry >> simp[]) >>
 `inst_seq_ptr
   <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
   0 ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
   (drule_all abi_decode_ptr_sequence_reentry >> simp[]) >>
 `!x. not_fresh_at sa x ==> lookup_var x clean = lookup_var x s` by
   (rpt strip_tac >>
    qpat_assum `not_fresh_at sa x` (assume_tac o REWRITE_RULE [not_fresh_at_def]) >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x clean = _ /\ _`
      (qspec_then `x` mp_tac) >>
    simp[Abbr `ps`, abi_decoder_prune_vars_def, lookup_var_def,
      FLOOKUP_DRESTRICT, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
   (rpt strip_tac >> irule abi_decode_extend_same_lookup >>
    qexists_tac `clean` >> simp[]) >>
 `ptr_covers G' tn' output u cap /\
  abi_decode_ptr_window G' tn' u source (n2w B) L` by
   (conj_tac
    >- (irule ptr_covers_frame >> qexistsl_tac [`G'`, `clean`, `tn'`] >> simp[]) >>
    irule abi_decode_ptr_window_frame >> qexistsl_tac [`G'`, `clean`, `tn'`] >> simp[]) >>
 `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  allocas_from lo u` by
   (fs[Abbr `ps`, abi_decoder_prune_vars_def, allocas_from_def] >> metis_tac[]) >>
 `isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  sb.cs_current_bb = sa.cs_current_bb` by fs[inst_extends_def, same_blocks_def] >>
 drule_all entry_straight_line_code_slice >> strip_tac >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
   fs[EVERY_MEM] >>
 `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
   fs[inst_extends_def] >>
 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
   simp[IS_PREFIX_APPEND] >>
 `!explicit. gas_origin_ptr_path
   (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
    lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
   (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >>
    disch_then (qspec_then `explicit` mp_tac) >> simp[IS_PREFIX_APPEND]) >>
 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
   (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
 qexistsl_tac [`G'`, `tn'`] >> simp[] >> rpt strip_tac >>
 qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` drule >> simp[]
QED
