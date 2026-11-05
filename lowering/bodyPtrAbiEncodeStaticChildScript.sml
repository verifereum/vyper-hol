(* Static child address preparation followed by the checked word encoder. *)
Theory bodyPtrAbiEncodeStaticChild
Ancestors
  bodyPtrAbiEncodeOffset bodyPtrAbiEncodeWordChecks abiEncoderChildCode ghostPcTransportPtr
  abiEncoderReentryLeaves abiEncoder abiDecoderContract abiDecoderReentry emitHelperProps
  exprLoweringProps compileEnv emitHelper fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  finite_map words list rich_list arithmetic

Theorem abi_encode_static_word_child_code:
  compile_abi_encode_child dst src AbiPrimWord F off cursor st = (out,en) ==>
  ?head mid.
    emit_op ADD [dst; Lit (n2w off)] st = (head,mid) /\
    compile_abi_encode_to_buf head src AbiPrimWord mid = (out,en) /\
    emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en /\
    LENGTH (emitted_insts st mid) = 1 /\
    LENGTH (emitted_insts mid en) = 2 /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts mid en) = [] /\
    mid.cs_next_var = st.cs_next_var+1 /\
    en.cs_next_var = mid.cs_next_var+1
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encode_word_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

(* The offset boundary's run equation also fixes the control-site fields. *)
Theorem abi_encode_static_child_address_control[local]:
  emit_op ADD [Var dst; Lit (n2w off)] st = (head,mid) /\
  lookup_var dst s = SOME a /\
  run_inst_seq (emitted_insts st mid) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def, update_var_def]
QED

Theorem abi_encode_static_child_sites[local]:
  isPREFIX (xs ++ ys) (DROP k code) ==>
  isPREFIX xs (DROP k code) /\
  isPREFIX ys (DROP (k + LENGTH xs) code)
Proof
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  conj_tac >- (qexists_tac `ys ++ l` >> simp[APPEND_ASSOC]) >>
  qexists_tac `l` >>
  once_rewrite_tac[ADD_COMM] >> rewrite_tac[GSYM DROP_DROP_T] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  `LENGTH xs - (LENGTH xs + LENGTH ys) = 0` by decide_tac >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem abi_encode_static_word_child_checked_ptr_path:
  !total.
  compile_abi_encode_child (Var dst) (Var src) AbiPrimWord F off cursor st = (out,en) /\
  not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w db) /\
  sb < dimword(:256) /\ db+off < dimword(:256) /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s total /\
  off < total /\ off+32 <= total /\
  (!i. sb <= i /\ i < sb+32 ==> i NOTIN tn.t_mem) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st en))) /\
    eval_operand out t = SOME 32w /\
    mem_bytes_at (db+off) 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory /\
    fresh_vars_wrt limit_st t /\
    tnf.t_mem = tn.t_mem DIFF {i | db+off <= i /\ i < db+off+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at st p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  gen_tac >> strip_tac >> drule abi_encode_static_word_child_code >> strip_tac >>
  `isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+1) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >> drule abi_encode_static_child_sites >> simp[]) >>
  `w2n (n2w db:bytes32)+off < dimword(:256)` by
    (simp[w2n_n2w] >> `db < dimword(:256)` by decide_tac >> simp[]) >>
  drule_all abi_encode_offset_checked_ptr_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  suspend "after_offset"
QED

Resume abi_encode_static_word_child_checked_ptr_path[after_offset]:
  gvs[] >>
  drule_all abi_encode_static_child_address_control >> strip_tac >>
  `fresh_vars_wrt limit_st t` by
    (irule abi_encode_offset_fresh_vars >> goal_assum $ drule_at Any >>
     simp[] >> goal_assum $ drule_at Any >> simp[]) >>
  `lookup_var src t = SOME (n2w sb) /\
   ptr_covers Gf tnf src t 32` by
    (first_assum (qspec_then `src` mp_tac) >>
     simp[] >> fs[ptr_covers_def]) >>
  `abi_decoder_operand_live mid.cs_next_var (Var p)` by
    fs[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  `eval_operand (Var src) (t with vs_inst_idx := s.vs_inst_idx+1) = SOME (n2w sb) /\
   eval_operand (Var p) (t with vs_inst_idx := s.vs_inst_idx+1) = SOME (n2w (db+off))` by
    fs[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `ptr_covers G tn dst _ _` kall_tac >>
  qpat_x_assum `ptr_covers G tn src _ _` kall_tac >>
  qpat_x_assum `lookup_var src s = _` kall_tac >>
  qpat_x_assum `lookup_var dst s = _` kall_tac >>
  `fresh_vars_wrt limit_st (t with vs_inst_idx := s.vs_inst_idx+1) /\
   lookup_block (t with vs_inst_idx := s.vs_inst_idx+1).vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts mid en)
     (DROP (t with vs_inst_idx := s.vs_inst_idx+1).vs_inst_idx bb.bb_instructions) /\
   ptr_covers Gf tnf src (t with vs_inst_idx := s.vs_inst_idx+1) 32 /\
   ptr_covers Gf tnf p (t with vs_inst_idx := s.vs_inst_idx+1) 32 /\
   ~(t with vs_inst_idx := s.vs_inst_idx+1).vs_halted` by
    fs[fresh_vars_wrt_def] >>
  `en.cs_next_var <= limit_st.cs_next_var /\
   (!i. sb <= i /\ i < sb+32 ==> i NOTIN tnf.t_mem)` by simp[] >>
  drule_all abi_encode_word_checked_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED
Resume abi_encode_static_word_child_checked_ptr_path[compose]:
  gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`Gf'`, `tnf'`, `t'`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at mid p'` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  metis_tac[]
QED
Finalise abi_encode_static_word_child_checked_ptr_path
