(* Typed normalization at a conditional arm's assignment continuation. *)
Theory bodyIfExpTypedMemory
Ancestors
  typedNormalizeEntryBoundary typedStoreEndpoint exprSimMemUnwrap
  externalNormalizePremises externalReturnNormalizeRun exprSimIfExp
  context compileEnv venomExecSemantics venomInst emitHelper fragExec

Theorem ifexp_typed_store_assignment_entry:
  compile_store_memory_typed ce dst dt src st initial = ((),sa) /\
  emit_inst ASSIGN [op] [rv] sa = ((),sb) /\
  fn_has_code sa sb func ==>
  (emitted_blocks initial sa <> [] ==>
    ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt strip_tac >>
  `phi_prefix_length sa.cs_current_insts = 0` by
    metis_tac[normalize_typed_changed_prefix_zero] >>
  gvs[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def,
      fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  Cases_on `sa.cs_current_insts` >>
  gvs[phi_prefix_length_def, mk_inst_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
QED
