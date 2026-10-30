(* TOP-LEVEL: actual non-indexed data packing preserves all saved Log
   arguments, including indexed values, and produces the declared data tuple. *)
Theory typedLogSplitPath
Ancestors
  typedCopyStateFrame
  typedLogSplitComplete typedLogSplitArgs typedLogDataContract typedLogArgs typedLogArgsFrames
  typedSArrayDynInvariant typedCopyContract eventLogSplitProps memoryValueDefs
  abiStaticLoopCode fragBlockPath fragExec context stmtLowering compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue venomState venomInst
  list pair words arithmetic

Definition split_log_data_store_contract_def:
  split_log_data_store_contract ctx func flags args ftvs atvs buf field_offset start after <=>
    !ss vs buf_addr.
      LENGTH flags = LENGTH args /\ fn_has_code start after func /\ cut_continuation_no_phi after func /\
      ss.vs_current_bb = start.cs_current_bb /\ ss.vs_inst_idx = LENGTH start.cs_current_insts /\ ~ss.vs_halted /\
      log_args_rel args atvs vs ss /\
      log_args_safe args atvs ss (w2n buf_addr + field_offset)
        (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
      eval_operand buf ss = SOME buf_addr /\
      w2n buf_addr + field_offset + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) /\
      EVERY (\name. buf <> Var name)
        (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) /\
      log_args_avoid args (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
      ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
        out.vs_current_bb = after.cs_current_bb /\ out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
        values_have_types (select_log_args F flags ftvs) (select_log_args F flags vs) /\
        memory_tuple_rel (select_log_args F flags ftvs) (select_log_args F flags vs)
          (w2n buf_addr + field_offset) out.vs_memory /\
        log_args_rel args atvs vs out /\
        log_args_safe args atvs out (w2n buf_addr + field_offset)
          (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
        array_copy_frame (TupleTV (select_log_args F flags ftvs)) 1
          (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
        (!arg_op. EVERY (\name. arg_op <> Var name)
          (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
          eval_operand arg_op out = eval_operand arg_op ss)
End

Theorem split_log_data_store_contract_from_store:
  !ctx func flags args ftvs atvs buf field_offset start after.
    LENGTH flags = LENGTH args /\
    log_data_store_contract ctx func (SND (split_log_ops args flags))
      (select_log_args F flags ftvs) (select_log_args F flags atvs) buf field_offset start after ==>
    split_log_data_store_contract ctx func flags args ftvs atvs buf field_offset start after
Proof
  rpt gen_tac >> strip_tac >> drule split_log_ops_select >> DISCH_TAC >>
  simp_tac bool_ss [split_log_data_store_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `vs`, `buf_addr`] >> strip_tac >>
  `log_args_rel (SND (split_log_ops args flags)) (select_log_args F flags atvs)
    (select_log_args F flags vs) ss` by
    (asm_simp_tac bool_ss [SND] >> irule log_args_rel_select >> simp[]) >>
  `log_args_safe (SND (split_log_ops args flags)) (select_log_args F flags atvs) ss
    (w2n buf_addr + field_offset) (type_memory_size (TupleTV (select_log_args F flags ftvs)))` by
    (asm_simp_tac bool_ss [SND] >> irule log_args_safe_select >> simp[]) >>
  `log_args_avoid (SND (split_log_ops args flags))
    (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var))` by
    (asm_simp_tac bool_ss [SND] >> irule log_args_avoid_select >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `log_data_store_contract _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [log_data_store_contract_def]) >>
  disch_then (qspecl_then [`ss`, `select_log_args F flags vs`, `buf_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  mp_tac (Q.SPECL [`args`, `atvs`, `vs`, `ss`, `out`, `TupleTV (select_log_args F flags ftvs)`,
    `1`, `w2n (buf_addr:bytes32) + field_offset`,
    `compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)`] log_args_frame) >>
  impl_tac >- (simp_tac bool_ss [MULT_CLAUSES] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [MULT_CLAUSES]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

Theorem checked_compile_split_log_data_store_contract:
  !tops in_deploy layouts addr art ctx func cenv flags fts args ftvs atvs buf field_offset cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    compile_log_store_data cenv (SND (split_log_ops args flags))
      (log_non_indexed_types flags fts) buf field_offset cs = (ret,cs') ==>
    split_log_data_store_contract ctx func flags args ftvs atvs buf field_offset cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `flags`, `fts`, `args`, `ftvs`, `atvs`, `buf`, `field_offset`, `cs`, `ret`, `cs'`]
    checked_compile_split_log_data_complete) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  irule split_log_data_store_contract_from_store >> simp[]
QED
