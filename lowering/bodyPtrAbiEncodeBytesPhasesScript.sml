(* Full ten-instruction bytes path from the checked phase interfaces. *)
Theory bodyPtrAbiEncodeBytesPhases
Ancestors
  bodyPtrAbiEncodeBytesPath bodyPtrAbiEncodeBytesPrefix bodyPtrAbiEncodeBytesSuffix
  bodyPtrAbiEncodeBytesCopy bodyPtrAbiEncodeCursorFrame bodyPtrDefs
  abiEncoderBytesCode abiEncoderBytesPrefix exprLoweringProps emitHelperProps
  compileEnv emitHelper fragGasPathPtr ptrDiscipline venomState
  venomExecSemantics words arithmetic list rich_list

Theorem abi_encode_bytes_phases_path:
  !total.
  abi_encode_bytes_prefix (Var dst) (Var src) st = (ops,ready) /\
  abi_encode_bytes_copy (Var dst) (Var src) (FST ops) (SND ops) ready = ((),copied) /\
  abi_encode_bytes_suffix (FST ops) copied = (out,en) /\
  not_fresh_at st dst /\ not_fresh_at st src /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  ptr_covers G tn dst s total /\ ptr_covers G tn src s (32+cnt) /\
  (!i. w2n a <= i /\ i < w2n a+(32+cnt) ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w cnt /\ cnt+31 < dimword(:256) /\ 32+cnt < dimword(:256) /\
  32+cnt <= total /\ contractABI$ceil32 cnt+32 <= total /\
  w2n b+contractABI$ceil32 cnt < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st ready) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts ready copied) (DROP (s.vs_inst_idx+4) bb.bb_instructions) /\
  isPREFIX (emitted_insts copied en) (DROP (s.vs_inst_idx+7) bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    lookup_var p t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    ptr_covers H un dst t total /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+10
Proof
  gen_tac >> strip_tac >>
  drule abi_encode_bytes_prefix_shape >> strip_tac >>
  drule abi_encode_bytes_copy_shape >> strip_tac >>
  drule abi_encode_bytes_suffix_shape >> strip_tac >>
  `ready.cs_next_var <= limit_st.cs_next_var /\
   op_taint tn (Var dst) = {} /\ ptr_covers G tn src s 32 /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)` by
    (fs[ptr_covers_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all abi_encode_bytes_prefix_framed_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  `not_fresh_at ready dst /\ not_fresh_at ready src` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  `lookup_var dst t = SOME b /\ lookup_var src t = SOME a /\
   ptr_covers H un dst t (32+cnt) /\ ptr_covers H un src t (32+cnt)` by
    (drule_all abi_encode_read_frame_covers >> strip_tac >>
     `ptr_covers G tn dst s (32+cnt)` by (fs[ptr_covers_def] >> decide_tac) >>
     fs[AC ADD_ASSOC ADD_COMM] >> rpt conj_tac >>
     metis_tac[abi_encode_read_frame_covers, abi_encode_read_frame_lookup]) >>
  `(!i. w2n a <= i /\ i < w2n a+(32+cnt) ==> i NOTIN un.t_mem)` by
    (qpat_assum `abi_encode_read_frame _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encode_read_frame_def] >> strip_tac >>
     fs[AC ADD_ASSOC ADD_COMM]) >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `isPREFIX (emitted_insts ready copied) (DROP t.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts copied en) (DROP (t.vs_inst_idx+3) bb.bb_instructions)` by simp[] >>
  `cnt+31 < dimword(:256) /\ 32+cnt < dimword(:256) /\
   en.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_bytes_copy_suffix_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ptr_covers H un dst t total'` by metis_tac[abi_encode_read_frame_covers] >>
  qmatch_asmsub_abbrev_tac `abi_encode_read_frame ready written H clean t' H' un'` >>
  `ptr_covers H clean dst written total'` by
    (qpat_assum `ptr_covers H un dst t total'` mp_tac >>
     simp_tac (srw_ss()) [Abbr `written`, Abbr `clean`, ptr_covers_def,
       mcopy_def, mstore_def, write_memory_with_expansion_def, LET_THM,
       lookup_var_def, op_taint_def]) >>
  `ptr_covers H' un' dst t' total'` by metis_tac[abi_encode_read_frame_covers] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum $ drule_at Any >> fs[]
QED
