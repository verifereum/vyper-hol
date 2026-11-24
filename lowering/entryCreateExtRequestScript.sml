(* ExtCall request preparation ends before the optional EXTCODESIZE check. *)
Theory entryCreateExtRequest
Ancestors
  bodyFullExtCallPacking createSizeEncodeCode createSizeCutOpens
  createSizeCutCode exprLowering compileEnv pair venomInst

Theorem extcall_request_pack_code:
  compile_alloc_buffer ((if abi > cap then abi else cap) + 32) se = (ba,s1) /\
  emit_void MSTORE [ba.buf_operand; Lit (n2w mid)] s1 = ((),s2) /\
  (if vals = [] then comp_return (Lit 4w) else
     comp_bind (emit_op ADD [ba.buf_operand; Lit 32w]) (\dst.
       comp_bind (compile_abi_encode_values_to_buf ce dst (ZIP (vals,tys))) (\alen.
         emit_op ADD [alen; Lit 4w]))) s2 = (len,s3) /\
  emit_op ADD [ba.buf_operand; Lit 28w] s3 = (off,sp) ==>
  create_cut_code {} se s1 /\ create_cut_code {} s1 s2 /\
  create_cut_code {} s2 s3 /\ create_cut_code {} s3 sp /\
  create_cut_code {} se sp
Proof
  strip_tac >>
  `create_cut_code {} se s1` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     metis_tac[create_alloc_buffer_cut_code, pairTheory.SND]) >>
  `create_cut_code {} s1 s2` by
    (qpat_assum `emit_void _ _ _ = _`
       (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
        AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     simp[create_cut_code_emit_void, create_cut_targets_def]) >>
  `create_cut_code {} s2 s3` by
    (qpat_x_assum `(if _ then _ else _) _ = _`
       (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
        AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     IF_CASES_TAC >> simp[] >>
     rpt (irule create_cut_code_bind >>
          simp[create_cut_code_emit_op, create_cut_targets_def,
               create_encode_values_cut_code])) >>
  `create_cut_code {} s3 sp` by
    (qpat_assum `emit_op _ _ _ = _`
       (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
        AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     simp[create_cut_code_emit_op, create_cut_targets_def]) >>
  simp[] >> metis_tac[create_cut_code_join]
QED
