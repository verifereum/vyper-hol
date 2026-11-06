(* Address result clamp execution. *)
Theory bodyMemTbExtract32AddressClamp
Ancestors
  convertScalarChecks exprLowering exprLoweringProps emitHelper compileEnv
  venomState venomInst words list rich_list

Theorem extract32_address_clamp_ok:
  compile_clamp_basetype x (BaseT AddressT) sa = (op,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME w /\ w2n w < 2**160 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ eval_operand op t = SOME w
Proof
  strip_tac >>
  gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule scalar_unsigned_upper_ok >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`w`, `s`] mp_tac) >> simp[dimword_def] >>
  strip_tac >> metis_tac[]
QED

Theorem extract32_address_clamp_revert:
  compile_clamp_basetype x (BaseT AddressT) sa = (op,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME w /\ ~(w2n w < 2**160) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule scalar_unsigned_upper_abort >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`w`, `s`] mp_tac) >> simp[dimword_def]
QED
