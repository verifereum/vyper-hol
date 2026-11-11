(* Shared #551 encoder adapter for the final two actions of nonempty Log.
   Uses the canonical source-fragment effect API, with no native encoder
   contract or encoder recursion in this adapter.
   Topics are already evaluated words (including typed fixed-bytes topics).
   Resources are the canonical enc_pre reservation, NOT an actual-ALLOCA ledger. *)
Theory logAbiEncoder
Ancestors
  abiEncoderFragment abiEncoderProps abiLogCode abiEncoderStructure
  eventEmitProps emitHelperProps emitHelper compileEnv fragExec
  venomState venomExecSemantics venomInst venomMemDefs
  valueEncoding vyperABI vyperTyping contractABI list rich_list words

(* enc_frame preserves old variables, not arbitrary label-table lookups. *)
Definition log_abi_old_operand_def:
  log_abi_old_operand st op <=>
    case op of
      Lit w => T
    | Var x => not_fresh_at st x
    | Label l => F
End

Theorem log_enc_frame_operand:
  enc_frame st mid lo top outs s0 s /\
  log_abi_old_operand st op /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[log_abi_old_operand_def, eval_operand_def] >>
  strip_tac >> fs[enc_frame_def]
QED

Theorem log_enc_frame_topics:
  !ops ws st mid lo top outs s0 s.
    enc_frame st mid lo top outs s0 s /\
    EVERY (log_abi_old_operand st) ops /\
    eval_operands ops s0 = SOME ws ==>
    eval_operands ops s = SOME ws
Proof
  Induct_on `ops` >> simp[eval_operands_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `eval_operand h s0 = SOME w` >>
  `eval_operand h s = SOME w` by
    (drule_all log_enc_frame_operand >> simp[]) >>
  simp[] >> first_x_assum drule_all >> simp[]
QED

(* Exact single-instruction suffix, requiring no undefined fresh SSA names. *)
Theorem log_abi_emit_suffix:
  emit_inst LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [size_op;dst]) [] mid =
      ((),final) /\
  LENGTH ops < dimword(:256) /\ eval_operands ops s = SOME ws /\
  eval_operand dst s = SOME dw /\ eval_operand size_op s = SOME len /\
  ~s.vs_call_ctx.cc_static ==>
  frag_exec ctx mid final (\t. t = s)
    (\t. t = (s with <|
      vs_logs := s.vs_logs ++
        [<|logger := w2w s.vs_call_ctx.cc_address; topics := ws;
           data := read_memory (w2n dw) (w2n len) s|>];
      vs_inst_idx := LENGTH final.cs_current_insts |>)) (\r. F)
Proof
  rpt strip_tac >> drule emitted_insts_emit_inst >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  simp[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  qexists_tac `s with vs_logs := s.vs_logs ++
    [<|logger := w2w s.vs_call_ctx.cc_address; topics := ws;
       data := read_memory (w2n dw) (w2n len) s|>]` >>
  simp[] >> irule run_inst_seq_sing_ok >>
  mp_tac (Q.SPECL [`mid.cs_next_id`,`ops`,`ws`,`dst`,`size_op`,
    `dw`,`len`,`s`] step_LOG) >> simp[mk_inst_def]
QED

(* The canonical frame is insensitive to the suffix's instruction index.
   Resetting logs exposes precisely the encoder frame to later composition. *)
Theorem log_enc_frame_suffix:
  enc_frame st mid lo top outs s0 s ==>
  enc_frame st mid lo top outs s0
    (s with <|vs_logs := s0.vs_logs; vs_inst_idx := index|>)
Proof
  simp_tac (srw_ss()) [enc_frame_def, lookup_var_def] >> strip_tac >>
  asm_rewrite_tac[] >> qpat_x_assum `enc_scratch _ _ _ s` mp_tac >>
  simp_tac (srw_ss()) [enc_scratch_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

(* TOP-LEVEL: the split is explicit so retained argument packing can supply
   enc_pre at its own endpoint. The final frame resets ONLY logs; thus the
   source/output/scratch and old-variable guarantees remain available.
   The source-fragment effect additionally preserves call context and data
   section, so the emitted logger is the initial call-context address. *)
Theorem compile_log_abi_emit_frag:
  compile_log_abi_emit dst src ei ops st = ((),final) /\
  compile_abi_encode_to_buf dst src ei st = (size_op,encode_end) /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  eval_operand dst s0 = SOME dw /\ eval_operand src s0 = SOME sw /\
  enc_pre st encode_end [dst;src] lo top tv v (w2n sw)
    [(w2n dw,LENGTH (enc (vyper_to_abi_type env ty) av))] s0 /\
  EVERY (log_abi_old_operand st) (dst::ops) /\
  LENGTH ops < dimword(:256) /\ eval_operands ops s0 = SOME ws /\
  ~s0.vs_call_ctx.cc_static ==>
  frag_exec ctx st final (\s. s = s0)
    (\s. mem_bytes_at (w2n dw)
            (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
          enc (vyper_to_abi_type env ty) av /\
      s.vs_logs = s0.vs_logs ++
        [<|logger := w2w s0.vs_call_ctx.cc_address; topics := ws;
           data := enc (vyper_to_abi_type env ty) av|>] /\
      enc_frame st encode_end lo top
        [(w2n dw,LENGTH (enc (vyper_to_abi_type env ty) av))] s0
        (s with vs_logs := s0.vs_logs) /\
      s.vs_call_ctx = s0.vs_call_ctx /\
      s.vs_data_section = s0.vs_data_section /\
      s.vs_tx_ctx = s0.vs_tx_ctx /\ s.vs_block_ctx = s0.vs_block_ctx /\
      s.vs_immutables = s0.vs_immutables /\ s.vs_outcomes = s0.vs_outcomes) (\r. F)
Proof
  rpt strip_tac >>
  `emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [size_op;dst])
     [] encode_end = ((),final)` by
    (qpat_x_assum `compile_log_abi_emit _ _ _ _ _ = _` mp_tac >>
     simp[compile_log_abi_emit_def, comp_bind_def]) >>
  `cs_extends st encode_end` by
    (drule compile_abi_encode_extends >> simp[]) >>
  `cs_extends encode_end final` by
    (irule cs_extends_same_block >> drule emit_inst_extends >>
     simp[IS_PREFIX_APPEND]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) < dimword(:256)` by
    (fs[enc_pre_def, enc_scratch_def] >> decide_tac) >>
  drule_all compile_abi_encode_to_buf_frag_effect >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `frag_exec ctx st encode_end _ post _` >>
  irule frag_exec_seq >> qexistsl_tac [`post`,`encode_end`] >>
  simp[] >> irule frag_exec_pointwise >>
  qx_gen_tac `encoded` >> simp[Abbr`post`] >> strip_tac >>
  `eval_operand dst encoded = SOME dw` by
    (fs[] >> drule_all log_enc_frame_operand >> simp[]) >>
  `eval_operands ops encoded = SOME ws` by
    (fs[] >> drule_all log_enc_frame_topics >> simp[]) >>
  `~encoded.vs_call_ctx.cc_static` by fs[] >>
  drule_all log_abi_emit_suffix >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  fs[read_memory_def, GSYM mem_bytes_at_def] >>
  conj_tac >- fs[enc_frame_def] >>
  irule (SRULE [] log_enc_frame_suffix) >> simp[]
QED
