(* Compiler-to-fetch boundary; independent of instruction semantics and ghosts. *)
Theory bodyPtrMakeArrayEmission
Ancestors
  emitHelperProps exprLoweringProps fragExec emitHelper compileEnv
  venomInst venomState rich_list list

Theorem emit_op_old_var_separate:
  emit_op opc args sm = (Var tmp,sb) /\
  sa.cs_next_var <= sm.cs_next_var /\ not_fresh_at sa x ==> x <> tmp
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[not_fresh_at_def]
QED

Theorem emit_op_fetch_boundary:
  emit_op opc args sm = (op,sb) /\ fn_has_code sm sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tmp bb.
    op = Var tmp /\
    tmp = STRING #"%" (toString sm.cs_next_var) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id opc args [tmp]) /\
    s.vs_current_bb = sb.cs_current_bb /\
    SUC s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> x <> tmp)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[get_instruction_def, EL_APPEND_EQN, not_fresh_at_def]
QED
