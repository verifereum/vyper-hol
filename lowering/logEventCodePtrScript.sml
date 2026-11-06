(* Compiler interval facts for the post-topic event suffix. *)
Theory logEventCodePtr
Ancestors
  logEncoderEntryPtr stmtSimLogEncodeFields abiEncoderCounters
  abiBuiltinAllocation abiEmptyAllocate abiDecoderIndexInit stmtSimLogDataRun
  emitHelperProps exprLoweringProps contextCodegenRelProps loweringSlice
  compileEnv context list arithmetic rich_list fragExec

Theorem log_tuple_encoder_interval:
  EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) /\
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys)) sa = (out,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  drule_all (ISPEC ``(ce:compile_env).ce_struct_fields``
    (Q.GEN `sf` scalar_tuple_encoder_shape)) >> strip_tac >> gvs[]
  >- (drule log_encode_copy_safe >> strip_tac >>
      drule abi_encoder_counters >> simp[]) >>
  drule_all log_encode_dynamic_safe >> strip_tac >>
  drule abi_encoder_counters >> simp[]
QED

val _ = if null (hyp log_tuple_encoder_interval) then ()
  else raise Fail "log_tuple_encoder_interval is not closed";

Theorem emitted_interval_split:
  inst_extends a b /\ inst_extends b c /\
  same_blocks a b /\ same_blocks b c /\ fn_has_code a c func /\
  isPREFIX (emitted_insts a c) (DROP j code) ==>
  fn_has_code a b func /\ fn_has_code b c func /\
  isPREFIX (emitted_insts a b) (DROP j code) /\
  isPREFIX (emitted_insts b c) (DROP (j + LENGTH (emitted_insts a b)) code)
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `isPREFIX (emitted_insts a c) _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  conj_tac >- metis_tac[APPEND_ASSOC] >>
  once_rewrite_tac[ADD_COMM] >>
  rewrite_tac[GSYM DROP_DROP_T] >> asm_rewrite_tac[] >>
  qexists_tac `l` >> rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED
