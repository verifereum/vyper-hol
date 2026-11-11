(* The real DLOAD decoder header: concrete edge and synchronized ghost. *)
Theory ctorDeployMemoryRunPtrPrefixHeader
Ancestors
  ctorDeployMemoryRunPtrPrefixBlocks ctorDeployMemoryRunPtrPrefixSequence
  abiDecoderExecution abiDecoderContract emitHelperProps ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic list rich_list

Theorem prefix_decode_dload_header_pair:
  let H = abi_decode_header_insts id ip src DLOAD iv cv cmp done body_lbl exit_lbl;
      bb = <|bb_label := hdr; bb_instructions := H|>;
      h = abi_decode_header_state iv cv cmp done i ncount s;
      t = jump_to (if i < ncount then body_lbl else exit_lbl) h
  in
    ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = hdr /\
    src <> Var iv /\ iv <> cv /\
    eval_operand ip s = SOME p /\ eval_operand src s = SOME a /\
    mload (w2n p) s = n2w i /\ abi_decode_load DLOAD a s = n2w ncount /\
    i <= ncount /\ ncount < dimword(:256) /\
    u 0 = s /\ u 4 = h /\ g 0 = G /\ q 0 = tn /\
    (!j. j < 4 ==>
      step_inst_base (EL j (TAKE 4 H)) (u j) = OK (u (SUC j)) /\
      step_inst f ctx (EL j (TAKE 4 H)) ((u j) with vs_inst_idx := j) =
        OK ((u (SUC j)) with vs_inst_idx := j) /\
      ptr_safe_step D lo f ctx fn PG (g j) (q j) (EL j (TAKE 4 H))
        ((u j) with vs_inst_idx := j) /\
      ghost_step f ctx PG (g j) (q j) (EL j (TAKE 4 H))
        ((u j) with vs_inst_idx := j) = (g (SUC j),q (SUC j))) /\
    ptr_safe_step D lo f ctx fn PG (g 4) (q 4) (EL 4 H)
      (h with vs_inst_idx := 4) ==>
    exec_block f ctx bb s = OK t /\
    (ptr_safe_blocks D lo f ctx fn PG
       (entry_prov fn t (g 4)) (entry_taint_vars fn t (q 4)) t ==>
     ptr_safe_block D lo f ctx fn PG G tn bb s)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  conj_tac >-
    (irule abi_decode_header_control >>
     simp[abi_decode_source_opcode_def] >> metis_tac[]) >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `ptr_safe_block _ _ _ _ _ _ _ _ bb s` >>
  `ptr_safe_block D lo f ctx fn PG (g 4) (q 4) bb
     ((u 4) with vs_inst_idx := 4)` suffices_by
    (qspecl_then [`TAKE 4 (abi_decode_header_insts id ip src DLOAD iv cv cmp done body_lbl exit_lbl)`,
       `bb`, `s`, `G`, `tn`, `u`, `g`, `q`, `D`, `lo`, `f`, `ctx`, `fn`, `PG`]
       mp_tac prefix_trace_ptr_safe_block >>
     impl_tac >-
       (simp[Abbr `bb`, abi_decode_header_insts_def, mk_inst_def,
             is_terminator_def] >>
        qpat_x_assum `!j. j < 4 ==> _` mp_tac >>
        simp[abi_decode_header_insts_def, mk_inst_def]) >>
     simp[abi_decode_header_insts_def]) >>
  simp[Once ptr_safe_block_def, Abbr `bb`, get_instruction_def,
       abi_decode_header_insts_def] >>
  qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[abi_decode_header_insts_def] >> strip_tac >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       abi_decode_header_state_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `i < ncount` >>
  gvs[abi_decode_header_state_def, bool_to_word_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, jump_to_def, is_terminator_def]
QED

Theorem prefix_decode_dload_header_entry_pair:
  let H = abi_decode_header_insts id ip src DLOAD iv cv cmp done body_lbl exit_lbl;
      bb = <|bb_label := hdr; bb_instructions := H|>;
      h = abi_decode_header_state iv cv cmp done i ncount s;
      t = jump_to (if i < ncount then body_lbl else exit_lbl) h
  in
    ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = hdr /\
    lookup_block hdr fn.fn_blocks = SOME bb /\
    src <> Var iv /\ iv <> cv /\
    eval_operand ip s = SOME p /\ eval_operand src s = SOME a /\
    mload (w2n p) s = n2w i /\ abi_decode_load DLOAD a s = n2w ncount /\
    i <= ncount /\ ncount < dimword(:256) /\
    u 0 = s /\ u 4 = h /\ g 0 = G /\ q 0 = tn /\
    (!j. j < 4 ==>
      step_inst_base (EL j (TAKE 4 H)) (u j) = OK (u (SUC j)) /\
      step_inst f ctx (EL j (TAKE 4 H)) ((u j) with vs_inst_idx := j) =
        OK ((u (SUC j)) with vs_inst_idx := j) /\
      ptr_safe_step D lo f ctx fn PG (g j) (q j) (EL j (TAKE 4 H))
        ((u j) with vs_inst_idx := j) /\
      ghost_step f ctx PG (g j) (q j) (EL j (TAKE 4 H))
        ((u j) with vs_inst_idx := j) = (g (SUC j),q (SUC j))) /\
    ptr_safe_step D lo f ctx fn PG (g 4) (q 4) (EL 4 H)
      (h with vs_inst_idx := 4) ==>
    exec_block f ctx bb s = OK t /\
    (ptr_safe_blocks D lo f ctx fn PG
       (entry_prov fn t (g 4)) (entry_taint_vars fn t (q 4)) t ==>
     ptr_safe_blocks D lo (SUC f) ctx fn PG G tn s)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  mp_tac prefix_decode_dload_header_pair >> simp[] >> strip_tac >>
  strip_tac >>
  simp[Once ptr_safe_blocks_def, eval_phis_def, phi_prefix_length_def,
       abi_decode_header_insts_def, mk_inst_def] >>
  `s with vs_inst_idx := 0 = s` by
    (Cases_on `s` >> gvs[]) >>
  qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ _ ==> _` mp_tac >>
  simp[abi_decode_header_insts_def, mk_inst_def]
QED

val _ = export_theory();
