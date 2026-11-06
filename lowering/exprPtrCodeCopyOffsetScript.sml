(* Source offsets preserve old roots; code offsets need no provenance. *)
Theory exprPtrCodeCopyOffset
Ancestors
  exprPtrCodeCopySegments exprSimCopy context compileEnv emitHelper emitHelperProps
  exprLoweringProps fragGasSeqPtr ptrDiscipline venomState finite_map
  typedCopyLoopHeaderPtr bodyPtrDefs venomExecSemantics venomInst

Theorem code_copy_source_offset:
  compile_lit_byte_offset src off sa = (op,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    eval_operand op t = SOME (a + n2w off) /\ op_taint tnf op = {} /\
    copy_old_operand sb op /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all copy_runtime_offset >> strip_tac >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def,
          copy_runtime_frame_def, run_inst_seq_def] >>
      qexistsl [`G`, `tn`] >> simp[inst_seq_ptr_def]) >>
  Cases_on `src`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def,
          copy_runtime_frame_def, run_inst_seq_def, eval_operand_def] >>
      qexistsl [`G`, `tn`] >> simp[inst_seq_ptr_def, op_taint_def])
  >> (gvs[compile_lit_byte_offset_def] >>
      drule emitted_insts_emit_op >> strip_tac >>
      `!p. not_fresh_at sa p ==>
        p <> STRING #"%" (toString sa.cs_next_var)` by
        simp[not_fresh_at_def] >>
      gvs[copy_runtime_frame_def] >>
      irule code_copy_source_add_segment >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[eval_operand_def]
QED

Theorem code_copy_destination_coverage:
  compile_lit_byte_offset (Var root) off sa = (op,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off+n <= capacity /\
  w2n a + off < dimword(:256) /\
  copy_runtime_frame sa s sb t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf ==>
  ?p. op = Var p /\ ptr_covers Gf tnf p t n
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      fs[copy_runtime_frame_def, emitted_insts_def, run_inst_seq_def] >>
      qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [] _ _ _`
        (mp_tac o REWRITE_RULE [inst_seq_ptr_def]) >>
      disch_then (CONJUNCTS_THEN SUBST1_TAC) >>
      qpat_x_assum `s = t` SUBST_ALL_TAC >>
      fs[ptr_covers_def] >> decide_tac) >>
  gvs[compile_lit_byte_offset_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `root <> STRING #"%" (toString sa.cs_next_var)` by
    gvs[not_fresh_at_def] >>
  `step_inst_base
    (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)]
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (a+n2w off) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  gvs[copy_runtime_frame_def, inst_seq_ptr_def, run_inst_seq_def] >>
  irule typed_copy_loop_dynamic_offset_covers >>
  simp[eval_operand_def] >> goal_assum (drule_at Any) >> simp[]
QED
