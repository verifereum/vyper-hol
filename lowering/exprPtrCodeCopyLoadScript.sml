(* Compiled DLOAD stage, at the ordinary deterministic endpoint. *)
Theory exprPtrCodeCopyLoad
Ancestors
  exprPtrCodeCopySegments exprSimCopy context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  exprLoweringProps fragGasSeqPtr ptrDiscipline venomState finite_map bodyPtrDefs

Theorem code_copy_runtime_load:
  compile_imm_load_word F imm arg sa = (op,sb) /\
  copy_old_operand sa arg /\ eval_operand arg s = SOME a /\
  op_taint tn arg = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    eval_operand op t = SOME (immutable_copy_read F a s) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    copy_old_operand sb op /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all copy_runtime_load >> strip_tac >>
  gvs[compile_imm_load_word_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `!p. not_fresh_at sa p ==>
    p <> STRING #"%" (toString sa.cs_next_var)` by
    simp[not_fresh_at_def] >>
  gvs[copy_runtime_frame_def] >>
  irule code_copy_load_segment >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
