(* Counted word normalization with a single execution/ghost witness. *)
Theory typedCopyReturnWordPtr
Ancestors
  typedCopyPtr typedMemoryCopy annAssignPtrLength bodyPtrMakeArrayWordStore
  assignTuplePtrLoadStep assignTuplePtrStoreWord fragGasSeqPtr
  typedCopyAgreement emitHelper compileEnv contextCodegenRelProps
  codegenRel contextCodegenRel venomMemProofs venomState venomInstProofs fragExec
  bodyPtrBytestringBuiltinsSource ptrCoverage ptrDiscipline fragGasPathPtr
  stmtLowering context valueEncoding
  venomInst bodyPtrDefs valueEncodingProps arithmetic

Theorem typed_copy_word_emits[local]:
  is_word_type dty /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) ==>
  ?tmp sm. emit_op MLOAD [src] sa = (Var tmp,sm) /\
    emit_void MSTORE [dst;Var tmp] sm = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sb /\
    tmp = STRING #"%" (toString sa.cs_next_var)
Proof
  strip_tac >>
  drule compile_store_memory_typed_word >>
  disch_then (qspecl_then [`sty`,`src`,`dst`,`ce`] assume_tac) >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  simp[emit_void_def, comp_ignore_bind_def, comp_bind_def,
       fresh_id_def, emit_def, comp_return_def, cs_extends_def] >>
  gvs[loweringShapeRulesTheory.emit_void_eq]
QED

Theorem typed_copy_word_counted:
  is_word_type dty /\
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) 32 s t /\
    t.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    tm.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all typed_copy_word_emits >> strip_tac >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all annassign_emit_mload_clean_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `ptr_covers Gf tnf dst sf 32 /\ lookup_var dst sf = SOME b` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Var tmp) sf = SOME (mload (w2n a) s)` by
    simp[eval_operand_def] >>
  drule_all emit_scratch_word_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tn'`,`t`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >> reverse conj_tac >-
    (fs[op_taint_def, mstore_def, write_memory_with_expansion_def]) >>
  simp[typed_copy_state_frame_def] >>
  conj_tac >-
    gvs[mstore_def, write_memory_with_expansion_def, venom_state_component_equality] >>
  conj_tac >- (simp[lookup_var_def, mstore_def] >> fs[lookup_var_def]) >>
  simp[typed_copy_frame_def] >> conj_tac >-
    (rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint]) >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity, MAX_DEF]
QED

Theorem typed_copy_word_robust_counted:
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME tv /\ value_has_type tv v /\
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) 32 s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory tv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b+32 <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> `sty = dty` by metis_tac[typed_copy_word_widening] >> gvs[] >>
  drule_all robust_typed_word_clean >> strip_tac >>
  `mload (w2n a) s = typed_val_to_w256 tv v` by
    metis_tac[mem_word_at_eq_mload, mem_agree_outside_def] >>
  drule_all typed_copy_word_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[] >>
  conj_tac >- metis_tac[typed_word_store_robust_ptr] >>
  rpt strip_tac >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  `mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    gvs[] >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[exprSimBufferStoreTheory.buffer_window_byte]
QED

Theorem typed_copy_none_counted:
  compile_store_memory_typed ce dst NoneT src NoneT sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  typed_copy_state_frame sa off 0 s s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory NoneTV NoneV off m)
Proof
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
       comp_return_def] >> strip_tac >> gvs[comp_return_def] >>
  simp[gas_path_ptr_rules, typed_copy_state_frame_def, typed_copy_frame_def,
       val_in_memory_def]
QED
