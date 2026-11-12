Theory exprSimAbiEncodeNoBlockBoundary
Ancestors
  exprSimAbiEncodeObliviousFacts compileEnv emitHelperProps
  exprLoweringProps abiEncoderSequence list rich_list

Theorem lower_abi_encode_no_block_prefix:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
  sa.cs_blocks = sb.cs_blocks ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  strip_tac >> drule lower_abi_encode_structural_facts >> strip_tac >>
  qpat_x_assum `cs_extends _ _` mp_tac >>
  simp[cs_extends_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem lower_abi_encode_no_block_inst_extends:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
  sa.cs_blocks = sb.cs_blocks ==> inst_extends sa sb
Proof
  strip_tac >> drule_all lower_abi_encode_no_block_prefix >>
  simp[inst_extends_def]
QED

Theorem lower_abi_encode_no_block_run_reach:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
  sa.cs_blocks = sb.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) initial = OK encoded /\
  fn_has_code sa sb observer /\ ~initial.vs_halted /\
  initial.vs_current_bb = sa.cs_current_bb /\
  initial.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. t = encoded with vs_inst_idx := LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    abi_decode_sim ctx observer initial t
Proof
  strip_tac >>
  drule_all lower_abi_encode_no_block_prefix >> strip_tac >>
  drule_all lower_abi_encode_no_block_inst_extends >> strip_tac >>
  irule abi_encoder_run_sequence_reach >> simp[] >> qexists_tac `sa` >> simp[]
QED
