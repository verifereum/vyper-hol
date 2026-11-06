Theory exprSimAbiDecodeRealizeCounted
Ancestors
  exprSimAbiDecodeRealizeEntry exprSimAbiDecodeRealizeTarget
  gasExemptCert gasOutcome gasSummary vyperState builtinAbi vyperCompiler emitHelper compileEnv

Theorem abi_decode_realize_no_exempt:
  ~gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr (abi_decode_realize_live_cx k)
      (abi_decode_realize_expr k)) (return ()))
    (es,s0) marks (err,ee) (leaf,sfinal)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  strip_tac >>
  strip_assume_tac abi_decode_realize_live_eval >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, return_def]
QED

Theorem abi_decode_realize_outcome_needs_normal:
  gas_outcome memory tops (ctx,func)
    (eval_expr (abi_decode_realize_live_cx k) (abi_decode_realize_expr k))
    (es,s0) Q (\res ee r. exprSimDefs$expr_exit res r) ==>
  ?n t res ee. gas_path ctx func s0 n (OK t) /\ Q (INL res) ee t
Proof
  simp[gas_outcome_def, abi_decode_realize_no_exempt,
       gas_summary_at_def, gas_marked_exec_def] >>
  rpt strip_tac >>
  strip_assume_tac abi_decode_realize_live_eval >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  gvs[exprSimDefsTheory.expr_exit_INL] >>
  drule fragGasModeTheory.gas_marked_path_exec >>
  metis_tac[]
QED

(* Keep the recursive decoder opaque: only these eight instructions precede
   output allocation and recursive decoding in the non-exact interval arm. *)
Definition abi_decode_realize_guard_prefix_def:
  abi_decode_realize_guard_prefix data lo hi =
    do len <- emit_op MLOAD [data];
       ptr <- emit_op ADD [data; Lit 32w];
       lt <- emit_op LT [len; Lit (n2w lo)];
       ge <- emit_op ISZERO [lt];
       gt <- emit_op GT [len; Lit (n2w hi)];
       le <- emit_op ISZERO [gt];
       valid <- emit_op AND [ge; le];
       emit_void ASSERT [valid];
       comp_return (ptr,len)
    od
End

Theorem abi_decode_realize_lower_prefix:
  lo <> hi ==>
  lower_abi_decode data info lo hi sz =
    do p <- abi_decode_realize_guard_prefix data lo hi;
       buf <- compile_alloc_buffer sz;
       compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD
         (FST p) (SND p) info;
       comp_return buf.buf_operand
    od
Proof
  strip_tac >>
  simp[lower_abi_decode_def, abi_decode_realize_guard_prefix_def,
    comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

Theorem abi_decode_realize_guard_opcodes:
  MAP (\i. i.inst_opcode)
    (SND (abi_decode_realize_guard_prefix data lo hi
      (initial_compile_state entry))).cs_current_insts =
  [MLOAD; ADD; LT; ISZERO; GT; ISZERO; AND; ASSERT]
Proof
  EVAL_TAC
QED
