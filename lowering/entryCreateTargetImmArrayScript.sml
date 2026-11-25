(* First-exit scope for constructor immutable array selection. *)
Theory entryCreateTargetImmArray
Ancestors
  bodyFullTargetImmutableArray entryCreateAdminSequence entryCreatePathScope
  exprSimArrayIndex exprLoweringProps abiEncoderProps emitHelper fragExec
  context compileEnv venomInst entryCreateFocusSpec entryCreateCompletedCut
  list arithmetic

Theorem immutable_array_suffix_layout[local]:
  compile_array_subscript arg idx dyn cnt 32 esz sgn
    (compile_ptr_load T imm LocCode) sa = (dst,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb)
Proof
  Cases_on `dyn` >> Cases_on `sgn` >> Cases_on `imm` >>
  simp[compile_array_subscript_split, compile_ptr_load_def,
       compile_imm_load_word_def, array_elem_ptr_def,
       array_bounds_check_def, array_bounds_valid_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, frag_ids_def]
QED

(* The installed slice cannot contain a CREATE or enter a callee.  This
   cut does not require a successful bounds check. *)
Theorem immutable_array_suffix_cut:
  compile_array_subscript arg idx dyn cnt 32 esz sgn
    (compile_ptr_load T imm LocCode) sn = (dst,sb) /\
  fn_has_code sn sb func /\ create_operand_at sn s ==>
  create_operand_cut sn sb E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule immutable_array_suffix_layout >> strip_tac >>
  irule create_admin_sequence_cut >> fs[EVERY_MEM]
QED
