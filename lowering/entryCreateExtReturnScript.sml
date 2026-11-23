(* First-exit geometry of external-call return handling. *)
Theory entryCreateExtReturn
Ancestors
  entryCreateEffectFocus entryCreateFocusSpec createSizeDecodeCode extcallReturnDecoderCode
  exprSimExtCallCase abiDecoderVarSequence compileEnv exprLowering
  createSizeCutCode list pair venomInst

Theorem extcall_return_decoder_cut:
  compile_abi_decode_to_buf dst pos MLOAD src hi info a = ((),b) /\
  fn_has_code a b func /\ body_inv tops ctx ce cx /\
  MEM func ctx.ctx_functions ==>
  create_operand_cut a b E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >>
  `create_cut_code {} a b` by
    (mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `pos`, `load` |-> `MLOAD`,
                     `bop` |-> `src`, `hi` |-> `hi`, `info` |-> `info`]
       create_decode_to_buf_cut_code) >>
     simp[create_cut_targets_def] >> disch_then (qspec_then `a` mp_tac) >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ a = _`
       (fn th => simp_tac bool_ss [th,pairTheory.SND])) >>
  `EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b)` by
    (drule return_decoder_frag_code >>
     simp[EVERY_MEM] >> disch_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> simp[abi_decoder_reentry_opcode_def] >>
     strip_tac >> simp[]) >>
  irule create_effect_suffix_cut >> metis_tac[]
QED

Theorem extcall_return_void_scope_cut:
  extcall_returned st0 ctx func ce cx NoneT es sa s0 sr addr buf cap
    target has_default default_op default_ty default_opt returnData ee t /\
  comp_return (Lit 0w) sr = (op,sb) ==>
  create_operand_full_scope sr sb E ctx func t [] (OK t) /\
  create_operand_cut sr sb E ctx func tops cx st0 source (ee,t)
Proof
  simp[comp_return_def, extcall_returned_def] >> strip_tac >>
  `create_operand_at sr t` by simp[create_operand_at_def] >>
  fs[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]
QED
