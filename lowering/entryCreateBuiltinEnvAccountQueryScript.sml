(* Concrete Account query layout at the post-argument cursor. *)
Theory entryCreateBuiltinEnvAccountQuery
Ancestors
  exprSimAccounts builtinProps emitHelper emitHelperProps exprLoweringProps compileEnv
  entryCreateAdminSequence
  venomInst venomState venomExecSemantics vyperAST vyperTypeSystem list rich_list

Theorem drop_append_two[local]:
  !xs x y. DROP (LENGTH xs) (xs ++ [x] ++ [y]) = [x;y]
Proof
  rpt gen_tac >>
  `xs ++ [x] ++ [y] = xs ++ ([x] ++ [y])` by simp[APPEND_ASSOC] >>
  pop_assum SUBST1_TAC >> simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem account_one_emit_layout[local]:
  emit_op opc xs m = (op,b) ==>
  b.cs_current_bb = m.cs_current_bb /\
  b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b
Proof
  strip_tac >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emitted_insts_emit_op >>
  fs[same_blocks_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       emitted_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem account_query_suffix_layout:
  !cenv ty ann item e a op b.
    item <> Code /\ ~is_self_codesize (Acc item) [e] /\
    lower_value compile_expr cenv ty (Builtin ann (Acc item) [e]) a = (op,b) ==>
    ?x m.
      lower_value compile_expr cenv (BaseT AddressT) e a = (x,m) /\
      (case item of
         Balance => emit_op BALANCE [x]
       | Codesize => emit_op EXTCODESIZE [x]
       | Codehash => emit_op EXTCODEHASH [x]
       | IsContract => comp_bind (emit_op EXTCODESIZE [x])
                          (\c. emit_op GT [c; Lit 0w])
       | Address => comp_return x
       | Code => comp_return x) m = (op,b) /\
      b.cs_current_bb = m.cs_current_bb /\
      b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts m b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lower_value_acc >> strip_tac >>
  qexistsl_tac [`x`,`s1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `item`
  >- (gvs[comp_return_def, comp_bind_def] >>
      simp[emitted_insts_def])
  >- (gvs[comp_return_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac account_one_emit_layout >>
      imp_res_tac emitted_insts_emit_op >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      simp[is_terminator_def])
  >- (gvs[comp_return_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac account_one_emit_layout >>
      imp_res_tac emitted_insts_emit_op >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      simp[is_terminator_def])
  >- (gvs[comp_return_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac account_one_emit_layout >>
      imp_res_tac emitted_insts_emit_op >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      simp[is_terminator_def])
  >- (gvs[comp_return_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac account_one_emit_layout >>
      imp_res_tac emitted_insts_emit_op >>
      `emitted_insts s1 b = emitted_insts s1 cs' ++ emitted_insts cs' b` by
        metis_tac[emitted_insts_append] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[APPEND_ASSOC] >>
      simp[is_terminator_def])
  >- gvs[]
QED


Theorem account_query_suffix_scope:
  !item e x m op b E C f s u.
    item <> Code /\
    (case item of
       Balance => emit_op BALANCE [x]
     | Codesize => emit_op EXTCODESIZE [x]
     | Codehash => emit_op EXTCODEHASH [x]
     | IsContract => comp_bind (emit_op EXTCODESIZE [x])
                        (\c. emit_op GT [c; Lit 0w])
     | Address => comp_return x | Code => comp_return x) m = (op,b) /\
    fn_has_code m b f /\
    b.cs_current_bb = m.cs_current_bb /\
    b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
    EVERY (\i. i.inst_id IN frag_ids m b /\
               i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts m b) /\
    create_operand_at m s /\ ~s.vs_halted /\
    run_inst_seq (emitted_insts m b) s = OK u ==>
    create_operand_full_scope m b E C f s []
      (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  irule create_admin_sequence_scope >>
  metis_tac[]
QED

Theorem account_query_suffix_cut:
  !item e x m op b E C f tops cx st0 source es s.
    item <> Code /\
    (case item of
       Balance => emit_op BALANCE [x]
     | Codesize => emit_op EXTCODESIZE [x]
     | Codehash => emit_op EXTCODEHASH [x]
     | IsContract => comp_bind (emit_op EXTCODESIZE [x])
                        (\c. emit_op GT [c; Lit 0w])
     | Address => comp_return x | Code => comp_return x) m = (op,b) /\
    fn_has_code m b f /\
    b.cs_current_bb = m.cs_current_bb /\
    b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\
               i.inst_opcode <> CREATE /\
               i.inst_opcode <> CREATE2) (emitted_insts m b) /\
    create_operand_at m s ==>
    create_operand_cut m b E C f tops cx st0 source (es,s)
Proof
  rpt gen_tac >> strip_tac >>
  irule create_admin_sequence_cut >>
  metis_tac[]
QED
