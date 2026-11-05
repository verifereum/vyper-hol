(* Counted composition of the actual bytes copy and suffix phases. *)
Theory bodyPtrAbiEncodeBytesPath
Ancestors
  bodyPtrAbiEncodeBytesCopy bodyPtrAbiEncodeBytesSuffix
  bodyPtrAbiEncodeBytesPrefix bodyPtrAbiEncodeCursorFrame
  abiEncoderBytesCode emitHelperProps exprLoweringProps compileEnv emitHelper
  fragGasPathPtr venomExecSemantics venomState venomInst ptrDiscipline
  words arithmetic list rich_list

Theorem abi_encode_bytes_copy_suffix_path:
  abi_encode_bytes_copy (Var dst) (Var src) (Var len) (Var lastptr) st = ((),mid) /\
  abi_encode_bytes_suffix (Var len) mid = (out,en) /\
  not_fresh_at st dst /\ not_fresh_at st src /\ not_fresh_at st len /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\ lookup_var lastptr s = SOME lp /\
  ptr_covers G tn lastptr s 32 /\ ptr_covers G tn dst s (32+cnt) /\
  ptr_covers G tn src s (32+cnt) /\
  lookup_var len s = SOME (n2w cnt) /\ op_taint tn (Var len) = {} /\
  (!i. w2n a <= i /\ i < w2n a+(32+cnt) ==> i NOTIN tn.t_mem) /\
  32+cnt < dimword(:256) /\ cnt+31 < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+3) bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st (mcopy (w2n b) (w2n a) (32+cnt) (mstore (w2n lp) 0w s)) G
      (tn with t_mem := (tn.t_mem DIFF {i | w2n lp <= i /\ i < w2n lp+32})
                           DIFF {i | w2n b <= i /\ i < w2n b+(32+cnt)}) t H un /\
    lookup_var p t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+6
Proof
  strip_tac >>
  drule abi_encode_bytes_copy_shape >> strip_tac >>
  drule abi_encode_bytes_suffix_shape >> strip_tac >>
  `mid.cs_next_var <= limit_st.cs_next_var /\
   eval_operand (Var len) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
  drule_all abi_encode_bytes_copy_framed_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var len) t = SOME (n2w cnt) /\ op_taint un (Var len) = {} /\
   ~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts mid en) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qmatch_asmsub_abbrev_tac `abi_encode_read_frame st written G clean t H un` >>
     `lookup_var len t = lookup_var len written /\
      op_taint un (Var len) = op_taint clean (Var len)` by
       metis_tac[abi_encode_read_frame_lookup, abi_encode_read_frame_taint] >>
     `~written.vs_halted /\ lookup_block written.vs_current_bb fn.fn_blocks = SOME bb` by
       (simp_tac (srw_ss()) [Abbr `written`, mcopy_def, write_memory_with_expansion_def,
          mstore_def, LET_THM] >> simp[]) >>
     drule_all abi_encode_read_frame_control >> strip_tac >>
     `lookup_var len written = lookup_var len s` by
       simp_tac (srw_ss()) [Abbr `written`, mcopy_def, write_memory_with_expansion_def,
          mstore_def, lookup_var_def, LET_THM] >>
     `op_taint clean (Var len) = op_taint tn (Var len)` by
       simp_tac (srw_ss()) [Abbr `clean`, op_taint_def] >>
     simp[eval_operand_def]) >>
  drule_all abi_encode_bytes_suffix_framed_path >>
  disch_then (qspecl_then [`PG`, `H`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st
     (mcopy (w2n b) (w2n a) (32+cnt) (mstore (w2n lp) 0w s)) G
     (tn with t_mem := (tn.t_mem DIFF {i | w2n lp <= i /\ i < w2n lp+32})
                          DIFF {i | w2n b <= i /\ i < w2n b+(32+cnt)}) t' H' un'` by
    metis_tac[abi_encode_read_frame_then] >>
  qexistsl_tac [`t'`, `H'`, `un'`] >>
  fs[AC ADD_ASSOC ADD_COMM]
QED

(* The two cleared windows overlap: copy includes the length word and
   padding starts at ceil32 cnt. This includes cnt=0, which still copies 32. *)
Theorem abi_encode_bytes_written_clean:
  abi_encode_read_frame st written G
    (tn with t_mem := (tn.t_mem DIFF {i | w2n lp <= i /\ i < w2n lp+32})
                       DIFF {i | w2n b <= i /\ i < w2n b+(32+cnt)}) t H un /\
  w2n lp = w2n b+rounded /\ rounded < cnt+32 ==>
  (!i. w2n b <= i /\ i < w2n b+(32+rounded) ==> i NOTIN un.t_mem)
Proof
  simp_tac (srw_ss()) [abi_encode_read_frame_def] >> strip_tac >>
  fs[] >> rpt strip_tac >> simp[] >> decide_tac
QED
