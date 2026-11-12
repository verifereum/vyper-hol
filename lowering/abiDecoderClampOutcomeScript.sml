(* Finite outcomes of clamps on arbitrary loaded words. *)
Theory abiDecoderClampOutcome
Ancestors
  abiDecoderClamp abiDecoderUnsignedClamp abiDecoderGuard abiDecoderRange
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Definition abi_decoder_clamp_wf_def:
  abi_decoder_clamp_wf NoClamp = T /\
  abi_decoder_clamp_wf BoolClamp = T /\
  abi_decoder_clamp_wf (IntClamp bits F) = (bits <= 256) /\
  abi_decoder_clamp_wf (IntClamp bits T) =
    (0 < bits /\ bits <= 256 /\ bits MOD 8 = 0) /\
  abi_decoder_clamp_wf (BytesMClamp m) = (0 < m /\ m <= 32)
End

Theorem abi_decoder_unsigned_shift_nonzero:
  bits <= 256 /\ ~(w2n (w:bytes32) < 2 ** bits) ==>
  w >>> w2n (n2w bits : bytes32) <> 0w
Proof
  strip_tac >>
  `bits < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >>
  ONCE_REWRITE_TAC [GSYM w2n_eq_0] >>
  `0 < 2 ** bits` by simp[] >>
  asm_simp_tac bool_ss [w2n_lsr] >>
  Cases_on `bits = 0` >- gvs[] >>
  `1 < 2 ** bits` by simp[] >>
  metis_tac[DIV_EQ_0]
QED

Theorem abi_decoder_unsigned_clamp_revert:
  compile_abi_int_clamp val_op bits F st = ((),st') /\
  eval_operand val_op s = SOME w /\ bits <= 256 /\
  ~(w2n w < 2 ** bits) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHR [Lit (n2w bits); val_op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w bits)) s = SOME (n2w bits)` by simp[eval_operand_def] >>
  drule_all abi_decoder_unsigned_shift_nonzero >> strip_tac >>
  drule_all emit_op_SHR_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[] >> drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  drule_all (Q.SPECL [`c1`, `c2`, `st'`] run_inst_seq_emit_extend) >>
  simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  simp[]
QED

Theorem abi_decoder_signed_clamp_revert:
  compile_abi_int_clamp val_op bits T st = ((),st') /\
  eval_operand val_op s = SOME w /\
  sign_extend (n2w (bits DIV 8 - 1)) w <> w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SIGNEXTEND [Lit (n2w (bits DIV 8 - 1)); val_op] st = (canon,c1)` >>
  rename1 `emit_op EQ [val_op;canon] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w (bits DIV 8 - 1))) s =
    SOME (n2w (bits DIV 8 - 1))` by simp[eval_operand_def] >>
  drule_all abi_clamp_emit_SIGNEXTEND >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[] >> `eval_operand val_op s1 = SOME w` by metis_tac[] >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  drule_all (Q.SPECL [`c1`, `c2`, `st'`] run_inst_seq_emit_extend) >>
  simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  simp[]
QED

Theorem abi_decoder_bytes_clamp_revert:
  compile_abi_bytes_clamp val_op m st = ((),st') /\
  eval_operand val_op s = SOME w /\
  w << w2n (n2w (m * 8) : bytes32) <> 0w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_bytes_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHL [Lit (n2w (8 * m)); val_op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w (8 * m))) s = SOME (n2w (8 * m))`
    by simp[eval_operand_def] >>
  drule_all abi_clamp_emit_SHL >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[] >> drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  drule_all (Q.SPECL [`c1`, `c2`, `st'`] run_inst_seq_emit_extend) >>
  simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  simp[]
QED

Theorem abi_decoder_clamp_revert:
  compile_abi_clamp_basetype val_op clamp st = ((),st') /\
  eval_operand val_op s = SOME w /\ fresh_vars_wrt st s /\
  abi_decoder_clamp_wf clamp /\ ~abi_decoder_clamp_valid clamp w ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  Cases_on `clamp`
  >- simp[abi_decoder_clamp_valid_def]
  >- (rename1 `IntClamp bits signed` >> Cases_on `signed`
      >- (simp[compile_abi_clamp_basetype_def, abi_decoder_clamp_wf_def,
               abi_decoder_clamp_valid_def] >> rpt strip_tac >>
          drule_all abi_decoder_signed_clamp_revert >> simp[]) >>
      simp[compile_abi_clamp_basetype_def, abi_decoder_clamp_wf_def,
           abi_decoder_clamp_valid_def] >> rpt strip_tac >>
      drule_all abi_decoder_unsigned_clamp_revert >> simp[])
  >- (simp_tac bool_ss [compile_abi_clamp_basetype_def,
                       abi_decoder_clamp_valid_def] >>
      rpt strip_tac >> drule_all abi_decoder_bytes_clamp_revert >> simp[]) >>
  simp[abi_decoder_bool_clamp, abi_decoder_clamp_valid_def] >>
  rpt strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`bits` |-> `1`] abi_decoder_unsigned_clamp_revert)) >> simp[]
QED

Theorem abi_decoder_clamp_finite_outcome:
  compile_abi_clamp_basetype val_op clamp st = ((),st') /\
  eval_operand val_op s = SOME w /\ fresh_vars_wrt st s /\
  abi_decoder_clamp_wf clamp ==>
  (?t. run_inst_seq (emitted_insts st st') s = OK t /\
       abi_decoder_clamp_valid clamp w) \/
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
       ~abi_decoder_clamp_valid clamp w)
Proof
  rpt strip_tac >> Cases_on `abi_decoder_clamp_valid clamp w`
  >- (disj1_tac >> drule_all abi_decoder_clamp_sequence >>
      strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
  disj2_tac >> drule_all abi_decoder_clamp_revert >> simp[]
QED
