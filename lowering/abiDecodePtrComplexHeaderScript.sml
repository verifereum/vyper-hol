(* The scalar prefix of a bounded complex decoder, before member iteration. *)
Theory abiDecodePtrComplexHeader
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrScalarFrame abiDecodePtrPrims
  abiDecoderRange abiEncoder bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  bodyPtrBopScalarOutcome abiEncoderWindowLookup freshWrites
  exprSimPtrProps assignTuplePtrLoadStep emitHelper emitHelperProps
  exprLoweringProps compileEnv bodyPtrDefs ptrDiscipline fragExec
  venomState venomInst venomExecSemantics words arithmetic list rich_list pred_set

Theorem abi_decode_complex_bounded_split:
  hi <> Lit 0w /\
  compile_abi_decode_to_buf dst pos opc src hi (DecComplex dyn infos) sa = ((),last) ==>
  ?e sm sb.
    emit_op ADD [pos;Lit (n2w (FOLDR (\(_,asz:num,_:num) acc. asz+acc) 0 infos))]
      sa = (e,sm) /\
    compile_abi_decode_range_check pos e hi sm = ((),sb) /\
    compile_abi_decode_complex_elems dst pos opc src hi infos 0 0 sb = ((),last)
Proof
  strip_tac >>
  gvs[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ` (\(_:abi_dec_info,asz:num,_:num) acc. acc + asz) =
    (\(_:abi_dec_info,asz:num,_:num) acc. asz + acc)` by
    (simp[FUN_EQ_THM, pairTheory.FORALL_PROD, ADD_COMM]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]
QED

Theorem abi_decode_complex_header_shape:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >>
  strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_complex_header_scalar:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) /\
  pos IN A /\ hi IN A /\ Lit (n2w static_sz) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sa sm) (e INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos;Lit (n2w static_sz)]`] >> simp[]) >>
  `!x. x IN R ==> not_fresh_at sm x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `?B. bop_scalar_seq R (e INSERT A) (emitted_insts sm sb) B` by
    (irule abi_decode_range_scalar >> simp[] >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >>
     drule compile_abi_decode_range_check_shape >>
     drule inst_extends_emit_op >> simp[inst_extends_def]) >>
  qexists_tac `B` >> simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `e INSERT A` >> simp[]
QED
