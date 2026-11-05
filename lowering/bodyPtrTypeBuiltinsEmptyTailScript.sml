Theory bodyPtrTypeBuiltinsEmptyTail
Ancestors
  bodyPtrTypeBuiltinsEmptyWords bodyPtrTypeBuiltinsEmptyZero
  builtinSimple emitHelper emitHelperProps compileEnv context exprLoweringProps
  venomInst venomState venomExecSemantics fragGasSeqPtr ptrDiscipline
  finite_map words arithmetic rich_list

Theorem empty_buffer_tail_certificate:
  !header sz sa sb s G tn p w D ctx func PG.
    (if header then emit_void MSTORE [Var p; Lit 0w]
     else compile_zero_words (Var p) ((sz+31) DIV 32)) sa = ((),sb) /\
    not_fresh_at sa p /\ lookup_var p s = SOME w /\
    ptr_covers G tn p s sz /\ w2n w+sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\ ~ctx_has_dalloca ctx ==>
    ?t H th. run_inst_seq (emitted_insts sa sb) s = OK t /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
      lookup_var p t = SOME w /\ ptr_covers H th p t sz /\
      th.t_mem = tn.t_mem DIFF
        {i | w2n w <= i /\ i < w2n w+(if header then 32 else sz)} /\
      th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
        FLOOKUP H q = FLOOKUP G q /\ op_taint th (Var q) = op_taint tn (Var q)) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  reverse Cases >> rpt gen_tac >> strip_tac
  >- (gvs[] >>
      `32*((sz+31) DIV 32) = sz` by
        (qspec_then `32` mp_tac DIVISION >> simp[] >>
         disch_then (qspec_then `sz` mp_tac) >> simp[] >> strip_tac >>
         `sz+31 = 32*(sz DIV 32)+31` suffices_by
           (disch_then SUBST1_TAC >> simp[]) >> decide_tac) >>
      `32*((sz+31) DIV 32) <= sz` by simp[] >>
      `w2n w+sz < dimword (:256)` by decide_tac >>
      drule_all empty_zero_words_certificate >>
      disch_then (qspecl_then [`D`, `func`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`t`, `H`, `th`] >> gvs[venom_state_component_equality]) >>
  gvs[] >>
  drule_all empty_zero_store_certificate >>
  disch_then (qspecl_then [`D`, `func`, `PG`, `sa.cs_next_id`] strip_assume_tac) >>
  qexistsl_tac [`mstore (w2n w) 0w s`, `G`, `tn'`] >>
  gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def,
      emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, op_taint_def, mstore_def, lookup_var_def]
QED
