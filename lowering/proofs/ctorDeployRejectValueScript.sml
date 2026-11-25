(* The non-payable constructor value check reads no gas before reverting. *)
Theory ctorDeployRejectValue
Ancestors
  fragGasPathMem memSafeRun venomExecProofs venomExecSemantics venomInst
  venomState venomExecProps gasCount list finite_map
  fragGasSeqAbort fragGasMode unitTransformDefs contextCodegenRel codegenRel

(* One opcode's dispatch equation, keeping the simplification local. *)
fun opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

(* A block that starts with the non-payable check reverts at its ASSERT when
   the call carries value, reading no GAS. *)
Theorem nonpayable_check_zero_path:
  !ctx fn bb rest s j0 j1 j2 v0 v1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      mk_inst j0 CALLVALUE [] [v0] :: mk_inst j1 ISZERO [Var v0] [v1] ::
      mk_inst j2 ASSERT [Var v1] [] :: rest /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    s.vs_call_ctx.cc_callvalue <> 0w ==>
    ?t. gas_path_mem ctx fn s 0 (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i0 = mk_inst j0 CALLVALUE [] [v0]` >>
  qabbrev_tac `i1 = mk_inst j1 ISZERO [Var v0] [v1]` >>
  qabbrev_tac `i2 = mk_inst j2 ASSERT [Var v1] []` >>
  `i0.inst_opcode = CALLVALUE /\ i0.inst_operands = [] /\
   i0.inst_outputs = [v0] /\
   i1.inst_opcode = ISZERO /\ i1.inst_operands = [Var v0] /\
   i1.inst_outputs = [v1] /\
   i2.inst_opcode = ASSERT /\ i2.inst_operands = [Var v1] /\
   i2.inst_outputs = []` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def] >>
  qabbrev_tac `t1 = update_var v0 s.vs_call_ctx.cc_callvalue s` >>
  `step_inst_base i0 s = OK t1` by
    (asm_simp_tac (srw_ss()) [opcode_eq ``CALLVALUE``, exec_read0_def] >>
     simp[Abbr `t1`]) >>
  qabbrev_tac `t1' = t1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var v0 t1' = SOME s.vs_call_ctx.cc_callvalue /\
   t1'.vs_inst_idx = 1 /\ ~t1'.vs_halted /\
   t1'.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `t1'`, Abbr `t1`, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  qabbrev_tac `t2 = update_var v1 0w t1'` >>
  `step_inst_base i1 t1' = OK t2` by
    (asm_simp_tac (srw_ss()) [opcode_eq ``ISZERO``, exec_pure1_def,
                              eval_operand_def, bool_to_word_def] >>
     simp[Abbr `t2`]) >>
  qabbrev_tac `t2' = t2 with vs_inst_idx := SUC t1'.vs_inst_idx` >>
  `lookup_var v1 t2' = SOME 0w /\ t2'.vs_inst_idx = 2 /\ ~t2'.vs_halted /\
   t2'.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `t2'`, Abbr `t2`, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base i2 t2' =
     Abort Revert_abort (revert_state (set_returndata [] t2'))` by
    asm_simp_tac (srw_ss()) [opcode_eq ``ASSERT``, eval_operand_def] >>
  qexists_tac `revert_state (set_returndata [] t2')` >>
  `gas_marked_path T ctx fn t2' (if i2.inst_opcode = GAS then 1 else 0)
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule (Q.SPECL [`T`, `ctx`, `fn`, `t2'`, `bb`, `i2`,
       `Revert_abort`, `revert_state (set_returndata [] t2')`]
       gas_marked_path_abort) >>
     simp[get_instruction_def, is_terminator_def, Abbr `i2`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `gas_marked_path T ctx fn t1'
     ((if i1.inst_opcode = GAS then 1 else 0) +
      (if i2.inst_opcode = GAS then 1 else 0))
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule (Q.SPECL [`T`, `ctx`, `fn`, `t1'`, `bb`, `i1`, `t2`,
       `if i2.inst_opcode = GAS then 1 else 0`,
       `Abort Revert_abort (revert_state (set_returndata [] t2'))`]
       gas_marked_path_step) >>
     gvs[get_instruction_def, is_terminator_def, Abbr `i1`, Abbr `t2'`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `gas_marked_path T ctx fn s
     ((if i0.inst_opcode = GAS then 1 else 0) +
      ((if i1.inst_opcode = GAS then 1 else 0) +
       (if i2.inst_opcode = GAS then 1 else 0)))
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule (Q.SPECL [`T`, `ctx`, `fn`, `s`, `bb`, `i0`, `t1`,
       `(if i1.inst_opcode = GAS then 1 else 0) +
        (if i2.inst_opcode = GAS then 1 else 0)`,
       `Abort Revert_abort (revert_state (set_returndata [] t2'))`]
       gas_marked_path_step) >>
     gvs[get_instruction_def, is_terminator_def, Abbr `i0`, Abbr `t1'`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  gvs[gas_marked_path_def]
QED
