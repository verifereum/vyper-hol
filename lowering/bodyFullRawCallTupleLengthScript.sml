(* The actual capped-length store, including its mask-independent ghosts. *)
Theory bodyFullRawCallTupleLength
Ancestors
  rawCallBufferPtr exprPtrUnwrapCopyEdges augAssignPtrScalarSafety
  decoderGhostFramePtr exprSafeOperand builtinSimple emitHelper compileEnv
  exprLoweringProps loweringStateRelDefs fragGasSeqPtr venomExecSemantics venomState venomInst
  finite_map words rich_list list pred_set

Theorem raw_call_tuple_length_checked:
 emit_op RETURNDATASIZE [] sa = (z,s1) /\
 emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
 compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
 emit_void MSTORE [Var x;cap] s3 = ((),sb) /\
 0 < n /\ n < dimword (:256) /\
 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
 safe_operand sa (Var x) /\
 lookup_var x s = SOME (n2w b) /\
 b + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
 ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
 LENGTH s.vs_returndata < dimword (:256) /\
 mem_bytes_at (b+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
   TAKE n s.vs_returndata /\
 (!i. b+32 <= i /\ i < b+32+LENGTH (TAKE n s.vs_returndata) ==>
      i NOTIN tn.t_mem) /\
 allocas_from lo s /\ ~ctx_has_dalloca ctx /\
 run_inst_seq (emitted_insts sa sb) s = OK t ==>
 ?Gf tnf.
   (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
   ptr_covers Gf tnf x t (32 + ((n+31) DIV 32)*32) /\
   (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) b mem) /\
   tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!v. not_fresh_at sa v ==>
    lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)) /\
   (t with vs_vars := s.vs_vars) =
    mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) s
Proof
  strip_tac >>
  gvs[compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  fs[emitted_insts_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  qabbrev_tac `a0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `a1 = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `a2 = STRING #"%" (toString (sa.cs_next_var+2))` >>
  qabbrev_tac `a3 = STRING #"%" (toString (sa.cs_next_var+3))` >>
  qabbrev_tac `a4 = STRING #"%" (toString (sa.cs_next_var+4))` >>
  `ALL_DISTINCT [x;a0;a1;a2;a3;a4]` by
    (gvs[safe_operand_def, not_fresh_at_def, Abbr `a0`, Abbr `a1`,
         Abbr `a2`, Abbr `a3`, Abbr `a4`, ALL_DISTINCT] >> decide_tac) >>
  fs[ALL_DISTINCT, lookup_var_def] >>
  qabbrev_tac `r = n2w (LENGTH s.vs_returndata):bytes32` >>
  qabbrev_tac `c = if LENGTH s.vs_returndata < n then 1w else 0w:bytes32` >>
  qabbrev_tac `u0 = update_var a0 r s` >>
  qabbrev_tac `u1 = update_var a1 c u0` >>
  qabbrev_tac `u2 = update_var a2 (word_xor r (n2w n)) u1` >>
  qabbrev_tac `u3 = update_var a3 (c * word_xor r (n2w n)) u2` >>
  qabbrev_tac `u4 = update_var a4 (word_xor (n2w n) (c * word_xor r (n2w n))) u3` >>
  `step_inst_base (mk_inst sa.cs_next_id RETURNDATASIZE [] [a0]) s = OK u0` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_read0_def, Abbr `u0`, Abbr `r`]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) LT [Var a0;Lit (n2w n)] [a1]) u0 = OK u1` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u1`, Abbr `u0`, Abbr `c`, Abbr `r`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     Cases_on `LENGTH s.vs_returndata < n` >> simp[bool_to_word_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) XOR [Var a0;Lit (n2w n)] [a2]) u1 = OK u2` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u2`, Abbr `u1`, Abbr `u0`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+3) MUL [Var a1;Var a2] [a3]) u2 = OK u3` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u3`, Abbr `u2`, Abbr `u1`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+4) XOR [Lit (n2w n);Var a3] [a4]) u3 = OK u4` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u4`, Abbr `u3`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `word_xor (n2w n) (c * word_xor r (n2w n)) = n2w (LENGTH (TAKE n s.vs_returndata)):bytes32` by
    (simp[Abbr `c`, Abbr `r`, LENGTH_TAKE_EQ] >>
     Cases_on `LENGTH s.vs_returndata < n` >> simp[arithmeticTheory.MIN_DEF] >>
     wordsLib.WORD_DECIDE_TAC) >>
  `b < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `eval_operand (Var x) u4 = SOME (n2w b) /\
   eval_operand (Var a4) u4 = SOME (n2w (LENGTH (TAKE n s.vs_returndata)))` by
    simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (sa.cs_next_id+5) MSTORE [Var x;Var a4] []) u4 =
     OK (mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) u4)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def]) >>
  gvs[run_inst_seq_def] >>
  FAIL_TAC "runtime"
QED
