(* Finite straight-line decoder prefixes, independent of the containing suffix. *)
Theory entryWordPrefix
Ancestors
  entryDecoderObserver abiEncoderPrefixSafety abiDecoderContract entrySinkExtraction
  calldataWordLive calldataWordLeaf fragExecMem fragExec venomInstProofs venomExecSemantics venomExecProps
  exprLoweringProps abiEncoderObserver emitHelperProps venomInst venomState instIdxIndep list rich_list arithmetic

Theorem decoder_sequence_local_prefix:
  !insts s t ctx fn bb.
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!k. k < LENGTH insts ==>
    get_instruction bb (s.vs_inst_idx + k) = SOME (EL k insts)) /\ ~s.vs_halted ==>
  local_prefix ctx fn (s.vs_current_bb,s.vs_inst_idx + LENGTH insts) s
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac
  >- (gvs[] >> irule (cj 1 local_prefix_rules) >> simp[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK middle` >>
  `middle.vs_current_bb = s.vs_current_bb /\
   middle.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >> conj_tac
  >- (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) insts` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`, `ctx`, `fn`, `bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD1] >>
  disch_then irule >> rpt strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `SUC k` mp_tac) >>
  `SUC k + s.vs_inst_idx = k + (s.vs_inst_idx + 1)` by decide_tac >>
  simp_tac std_ss [LESS_MONO_EQ, EL, HD, TL] >> simp[]
QED

Theorem decoder_word_local_prefix:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecPrimWord NoClamp) st = ((),last) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ fresh_vars_wrt st s /\
  d + 32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var src /\
  fn_has_code st last fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (BaseTV (UintT 256))
      (IntV (&w2n (abi_decode_load CALLDATALOAD p s))) d t.vs_memory /\
    t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    local_prefix ctx fn (last.cs_current_bb,LENGTH last.cs_current_insts) s t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st last) s = OK actual` >>
  `last.cs_blocks = st.cs_blocks /\ last.cs_current_bb = st.cs_current_bb` by
    fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `LENGTH st.cs_current_insts + LENGTH (emitted_insts st last) =
    LENGTH last.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  `local_prefix ctx fn (s.vs_current_bb,s.vs_inst_idx + LENGTH (emitted_insts st last)) s
    (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st last))` by
    (irule decoder_sequence_local_prefix >> asm_rewrite_tac[] >>
     qexists_tac `bb` >> asm_rewrite_tac[]) >>
  `actual.vs_current_bb = s.vs_current_bb` by
    metis_tac[run_inst_seq_preserves_entry_control] >>
  `?codebb. lookup_block s.vs_current_bb fn.fn_blocks = SOME codebb /\
    isPREFIX (emitted_insts st last) (DROP s.vs_inst_idx codebb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st last) s` by
    (drule calldata_word_opcodes >> strip_tac >>
     irule run_inst_seq_mem_ok_of_prefix_safe >> conj_tac
     >- (drule calldata_word_prefix_live >> simp[] >>
         disch_then (qspecl_then [`s`,`p`,`d`] mp_tac) >> simp[]) >>
     qpat_x_assum `EVERY (\i. _ /\ _ /\ _ /\ _) _` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `last.cs_current_insts = _` kall_tac >>
  qexists_tac `actual with vs_inst_idx := LENGTH last.cs_current_insts` >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  drule_all mem_safe_run_inst_seq >> strip_tac >>
  qpat_x_assum `!fuel ctx. _ /\ _` (qspecl_then [`fuel`,`ctx`] strip_assume_tac) >>
  qpat_x_assum `!s'. _ = OK s' /\ _ ==> _` irule >>
  qexists_tac `actual` >> simp[] >> metis_tac[]
QED
