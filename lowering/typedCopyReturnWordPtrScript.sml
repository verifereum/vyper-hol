(* Counted word normalization with a single execution/ghost witness. *)
Theory typedCopyReturnWordPtr
Ancestors
  typedCopyPtr typedMemoryCopy annAssignPtrLength bodyPtrMakeArrayWordStore
  assignTuplePtrLoadStep assignTuplePtrStoreWord fragGasSeqPtr
  typedCopyAgreement emitHelper compileEnv contextCodegenRelProps
  codegenRel contextCodegenRel venomMemProofs venomState venomInstProofs fragExec
  bodyPtrBytestringBuiltinsSource ptrCoverage ptrDiscipline fragGasPathPtr
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
