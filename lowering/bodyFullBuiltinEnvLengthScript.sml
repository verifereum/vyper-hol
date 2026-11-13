(* Joint finite-horizon simulation for Len and CalldataLen. *)
Theory bodyFullBuiltinEnvLength
Ancestors
  bodyFullExprGeneric bodyFullPreds bodyFullGhostFrame gasOutcomeFullCompose
  exprSimLen exprSimCalldata exprSimSource exprSimProps
  fragGasSeqPtr fragGasOriginPtr emitHelperProps allocaHistory
  loweringStateRelDefs ptrSafeRun ptrDiscipline instMemFrontier
  contextCodegenRel codegenRel unitTransformDefs memSafeRun
  vyperTypeSystem vyperTypeBuiltins list finite_map emitHelper compileEnv
  fragExec venomInst venomState

Theorem calldatalen_full_path:
  lower_value compile_expr cenv ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE [] [out]) s =
    OK (update_var out w s)) ==>
  ?t G' tn'.
    t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s
          with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) /\
    tn' = step_taint (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> gvs[lower_value_calldata_len] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s
          with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G inst (update_var (STRING #"%" (toString sa.cs_next_var)) w s),
      step_taint inst s (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn)` by
    (mp_tac (Q.INST [`i` |-> `inst`,
        `u` |-> `update_var (STRING #"%" (toString sa.cs_next_var)) w s`]
        straight_line_origin_ptr_edge) >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def,
          ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def] >>
     simp[GSYM mk_inst_def, venomExecSemanticsTheory.step_inst_non_invoke,
          update_var_def]) >>
  `~(update_var (STRING #"%" (toString sa.cs_next_var)) w s
       with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  drule (cj 1 gas_origin_ptr_path_rules) >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[update_var_def]
QED
