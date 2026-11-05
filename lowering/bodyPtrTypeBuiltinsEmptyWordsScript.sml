Theory bodyPtrTypeBuiltinsEmptyWords
Ancestors
  bodyPtrTypeBuiltinsEmptyZero bodyPtrTypeBuiltinsSeq abiEmptySequence
  builtinSimple emitHelper emitHelperProps compileEnv context exprLoweringProps
  venomInst venomState list rich_list words typedCopyPtr ptrDiscipline

Theorem empty_zero_words_successor_code:
  !n pop sa sm sb.
    compile_zero_words pop n sa = ((),sm) /\
    compile_zero_words pop (SUC n) sa = ((),sb) ==>
    emitted_insts sa sb = emitted_insts sa sm ++
      [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (n*32))]
         [STRING #"%" (toString sm.cs_next_var)];
       mk_inst (sm.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sm.cs_next_var)); Lit 0w] []]
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_zero_words pop n sa = _`
    (mp_tac o MATCH_MP abi_empty_zero_words_shape) >> strip_tac >>
  gvs[Once compile_zero_words_def, comp_bind_def, comp_ignore_bind_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
      emit_def, comp_return_def] >>
  gvs[inst_extends_def, emitted_insts_def, DROP_APPEND1] >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (qpat_x_assum `sm.cs_current_insts = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  simp[DROP_APPEND1]
QED

Theorem empty_zero_pair_storage_frame:
  !PG G tn s id p out w off.
    lookup_var p s = SOME w ==>
    (step_taint (mk_inst (id+1) MSTORE [Var out; Lit 0w] [])
      (update_var out (w+n2w off) s)
      (mstore (w2n (w+n2w off)) 0w (update_var out (w+n2w off) s))
      (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
        (update_var out (w+n2w off) s) tn)).t_stor = tn.t_stor /\
    (step_taint (mk_inst (id+1) MSTORE [Var out; Lit 0w] [])
      (update_var out (w+n2w off) s)
      (mstore (w2n (w+n2w off)) 0w (update_var out (w+n2w off) s))
      (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
        (update_var out (w+n2w off) s) tn)).t_trans = tn.t_trans
Proof
  rpt strip_tac >>
  simp[mstore_ghost_frame, copy_len_binop_ghost_frame,
       lookup_var_update_var, eval_operand_def, op_taint_def]
QED
