Theory bodyPtrPrecompileBuiltinsRecoveryInput
Ancestors bodyPtrPrecompileBuiltinsPrefixes bodyPtrPrecompileBuiltinsStaging
          bodyPtrPrecompileBuiltinsSeq bodyPtrPrecompileBuiltinsAllocationTransport
          compileEnv context emitHelper exprLoweringProps fragExec
          venomExecSemantics venomState ptrDiscipline bodyPtrDefs
          finite_map list rich_list

Theorem emitted_direct_word_store_checked:
  emit_void MSTORE [Var bufroot; v] sa = ((),sb) /\
  ptr_covers G tn bufroot s 32 /\ lookup_var bufroot s = SOME a /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx ==>
  ?t tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G tn') /\
    t = mstore (w2n a) w s /\ tn'.t_var = tn.t_var /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    (!p. lookup_var p t = lookup_var p s /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MSTORE [Var bufroot; v] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  drule_all clean_word_store_trace_cursors >>
  disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `tnf` strip_assume_tac)) >>
  qexistsl [`t`, `tnf`] >>
  simp[op_taint_def, lookup_var_def, mstore_def,
       write_memory_with_expansion_def, write_memory_def]
QED
