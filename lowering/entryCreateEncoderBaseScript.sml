(* Nonrecursive ABI encoders: the ghost post and the sequence proof refer
   to one endpoint, not two independently obtained window outcomes. *)
Theory entryCreateEncoderBase
Ancestors
  abiEncoderWindowJointLeaves abiBytestringCode abiEncoderLeaves abiEncoderProps
  abiEncoderReentryLeaves
  entryCreateAdminSequence entryCreateCompletedCut entryCreateFocusSpec
  emitHelperProps exprLoweringProps fragExec venomInst list pred_set arithmetic

Theorem encoder_leaf_ids[local]:
  (ei = AbiPrimWord \/ (?n. ei = AbiCopy n) \/ (?n. ei = AbiBytestring n)) /\
  compile_abi_encode_to_buf dst src ei st = (out,en) ==>
  EVERY (\i. i.inst_id IN frag_ids st en) (emitted_insts st en)
Proof
  strip_tac
  >- (gvs[] >> drule abi_encode_word_trace >> strip_tac >>
      drule emitted_insts_emit_op >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      `emitted_insts st en = emitted_insts st loaded_st ++ emitted_insts loaded_st en` by
        metis_tac[emitted_insts_append, inst_extends_emit_op, inst_extends_emit_void] >>
      simp[frag_ids_def, mk_inst_def])
  >- (gvs[] >> drule abi_encode_copy_code >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[frag_ids_def, mk_inst_def]) >>
  gvs[] >> drule compile_abi_bytestring_code >> strip_tac >>
  simp[bytestring_encoder_insts_def, frag_ids_def, mk_inst_def]
QED

(* Parameterized introduction: the client can carry a prefix in a larger
   encoder interval, or use the trivial payload for an unscoped caller. *)
Theorem encoder_window_base_from_steps:
  (ei = AbiPrimWord \/ (?n. ei = AbiCopy n) \/ (?n. ei = AbiBytestring n)) /\
  encoder_leaf_pre ei dst src st out en ctx func s at av sb cap d G tn lo /\
  (!raw. fn_has_code st en func /\ en.cs_current_bb = st.cs_current_bb /\
    en.cs_current_insts = st.cs_current_insts ++ emitted_insts st en /\
    EVERY (\i. i.inst_id IN frag_ids st en /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en) /\
    create_operand_at st s /\ ~s.vs_halted /\
    run_inst_seq (emitted_insts st en) s = OK raw ==>
    P s (raw with vs_inst_idx := LENGTH en.cs_current_insts)) ==>
  ?t G' tn'. P s t /\
    encoder_leaf_post ctx func st en out at av d s t G tn G' tn' lo explicit PG
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `EVERY (\i. i.inst_id IN frag_ids st en) (emitted_insts st en)` by
    (irule encoder_leaf_ids >>
     qhdtm_assum `encoder_leaf_pre`
       (strip_assume_tac o PURE_REWRITE_RULE[encoder_leaf_pre_def]) >>
     metis_tac[]) >>
  `?t G' tn'. encoder_leaf_trace st en s t /\
     encoder_leaf_post ctx func st en out at av d s t G tn G' tn' lo explicit PG` by
    (qpat_x_assum `ei = AbiPrimWord \/ _` strip_assume_tac >> gvs[] >>
     FIRST [drule compile_abi_encode_to_buf_word_window_joint_trace,
            drule compile_abi_encode_to_buf_copy_window_joint_trace,
            drule compile_abi_encode_to_buf_bytes_window_joint_trace] >>
     disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qhdtm_assum `encoder_leaf_trace`
    (strip_assume_tac o PURE_REWRITE_RULE[encoder_leaf_trace_def]) >>
  qhdtm_assum `encoder_leaf_pre`
    (strip_assume_tac o PURE_REWRITE_RULE[encoder_leaf_pre_def]) >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  first_x_assum irule >>
  simp[create_operand_at_def, inst_extends_def, FILTER_EQ_NIL, EVERY_MEM] >>
  conj_tac >- fs[inst_extends_def] >>
  rpt strip_tac >>
  qpat_assum `FILTER _ _ = []` mp_tac >>
  qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
  qpat_assum `EVERY (\i. i.inst_id IN _) _` mp_tac >>
  simp_tac bool_ss [FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

Theorem encoder_window_base_scoped_from_steps:
  (ei = AbiPrimWord \/ (?n. ei = AbiCopy n) \/ (?n. ei = AbiBytestring n)) /\
  encoder_leaf_pre ei dst src st out en ctx func s at av sb cap d G tn lo ==>
  ?t G' tn'. create_operand_full_scope st en explicit ctx func s [] (OK t) /\
    encoder_leaf_post ctx func st en out at av d s t G tn G' tn' lo explicit PG
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`P` |->
    `\u v. create_operand_full_scope st en explicit ctx func u [] (OK v)`]
    encoder_window_base_from_steps)) >>
  rpt strip_tac >>
  metis_tac[create_admin_sequence_scope]
QED
