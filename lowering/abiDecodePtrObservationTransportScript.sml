(* Endpoint transport preserves defined pointers, not arbitrary absent bindings. *)
Theory abiDecodePtrObservationTransport
Ancestors
  abiDecoderVarExtend bodyPtrDefs venomState finite_map

Theorem abi_decode_ptr_extend_covers:
  abi_decoder_vars_extend extras s t /\ ptr_covers G tn p s sz ==>
  ptr_covers G tn p t sz
Proof
  strip_tac >> fs[ptr_covers_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all abi_decoder_vars_extend_eval >>
  simp[eval_operand_def] >> metis_tac[]
QED

Theorem abi_decode_ptr_extend_ghost:
  abi_decoder_vars_extend extras s t /\ ghost_inv ret cenv cx es G tn s ==>
  ghost_inv ret cenv cx es G tn t
Proof
  strip_tac >>
  drule abi_decoder_vars_extend_restore >> strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `(t with vs_vars := s.vs_vars) = s` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  fs[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      conj_tac >- metis_tac[abi_decode_ptr_extend_covers] >>
      fs[ptr_covers_def] >>
      `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
      drule_all abi_decoder_vars_extend_eval >>
      simp[eval_operand_def] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `ret` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >>
      rename1 `lookup_var rp s = SOME bw` >>
      `eval_operand (Var rp) s = SOME bw` by simp[eval_operand_def] >>
      drule_all abi_decoder_vars_extend_eval >>
      simp[eval_operand_def] >> metis_tac[abi_decode_ptr_extend_covers]) >>
  simp[stor_taint_ok_def] >> fs[stor_taint_ok_def]
QED
