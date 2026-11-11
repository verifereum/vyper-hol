(* Memory bounds for the stack-tuple internal-return loads. *)
Theory internalReturnTupleMem
Ancestors
  internalReturnUnlockMem internalReturnSequenceMem stmtSimReturn fragExecMem instMemFrontier memSafeRun
  stmtLowering context compileEnv emitHelper exprLoweringProps emitHelperProps abiTupleValueEncoding
  fragExec fragGasPathMem runFromGasPathMem venomExecSemantics venomState venomInst words list arithmetic

Theorem tuple_elem_head_mem_ok[local]:
  emit_op ADD [bop; Lit off] sa = (pv, sm) /\
  emit_op MLOAD [pv] sm = (v, sb) /\
  eval_operand bop s = SOME w /\
  w2n (w + off) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
      fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_def,
       below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def,
       bind_outputs_def] >>
  simp[GSYM mk_inst_def, below_frontier_MLOAD, eval_operand_def,
       lookup_var_update_var, update_var_def] >>
  conj_tac >- simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `step_inst_base inst ss` >>
  Cases_on `step_inst_base inst ss` >> simp[]
QED

Theorem compile_load_tuple_elements_mem_ok:
  !tys cenv bop off sa elems sb s w.
  compile_load_tuple_elements cenv bop tys off sa = (elems,sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w /\ EVERY is_word_type tys /\
  w2n w + off + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + off + 32 * LENGTH tys < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct
  >- (rw[compile_load_tuple_elements_def, comp_return_def] >>
      simp[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_load_tuple_elements _ _ _ _ _ = _` mp_tac >>
  simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `emit_op MLOAD _ sm = (v,sh)` >>
  rename1 `compile_load_tuple_elements _ _ _ _ sh = (rest,sf)` >>
  `w2n (w + n2w off) = w2n w + off` by
    (Cases_on `w` >> gvs[word_add_n2w]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sh) s` by
    (irule tuple_elem_head_mem_ok >> goal_assum (drule_at Any) >>
     qexistsl_tac [`bop`, `n2w off`, `w`] >> simp[] >> decide_tac) >>
  drule_all (SRULE [compile_load_memory_def]
    (Q.SPEC `T` (Q.GEN `load` (SPEC_ALL tuple_elem_load_head_run)))) >>
  strip_tac >> gvs[] >>
  `!z. bop = Var z ==> not_fresh_at sh z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `eval_operand bop (s with vs_vars := vs) = SOME w` by
    (qsuff_tac `eval_operand bop (s with vs_vars := vs) = eval_operand bop s`
     >- simp[] >> irule eval_operand_old_vars >> simp[] >>
     qexists_tac `sa` >> simp[]) >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    (drule_all compile_load_tuple_elements_run >> strip_tac >>
     metis_tac[emitted_insts_append]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`cenv`, `rest`, `off + type_memory_bytes cenv h`] >>
  drule abi_word_metadata >> simp[] >> decide_tac
QED

Theorem compile_load_tuple_elements_frag_mem:
  compile_load_tuple_elements cenv bop tys off sa = (elems,sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w /\ EVERY is_word_type tys /\
  w2n w + off + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + off + 32 * LENGTH tys < dimword (:256) ==>
  frag_exec_mem ctx sa sb (\t. t = s)
    (\t. ?vars. t = s with <|vs_vars := vars;
                             vs_inst_idx := LENGTH sb.cs_current_insts|> /\
       (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
       eval_operands elems t = SOME (tuple_words cenv w tys off s.vs_memory))
    (\r. F)
Proof
  strip_tac >>
  drule_all compile_load_tuple_elements_mem_ok >> strip_tac >>
  drule_all compile_load_tuple_elements_run >> strip_tac >>
  irule frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def] >> simp[rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `vs` >> simp[eval_operands_vars_inst_idx, lookup_var_def] >>
  fs[lookup_var_def]
QED

Theorem emit_ret_values_path_mem[local]:
  emit_inst RET (ops ++ [rpc]) [] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operands ops s = SOME vals /\ eval_operand rpc s = SOME pc ==>
  ?n. gas_path_mem ctx func s n
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id RET (ops ++ [rpc]) []) s =
   IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> s` by
    metis_tac[internalReturnLockPropsTheory.step_RET_values] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id RET (ops ++ [rpc]) []]` by
    gvs[emit_inst_def, fresh_id_def, comp_bind_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` assume_tac) >> fs[] >>
  irule run_from_gas_path_mem >> simp[exit_result_def] >>
  qexists_tac `0` >>
  fs[run_from_def, mem_safe_run_def, Once mem_safe_block_def,
     mem_safe_step_non_invoke, below_frontier_no_ranges,
     inst_dload_in_section_other, mk_inst_def, Once exec_block_def,
     step_inst_non_invoke, is_terminator_def] >>
  simp[Once run_block_non_phis_def, step_inst_non_invoke, mk_inst_def]
QED

Theorem frag_mem_exit_path[local]:
  frag_exec_mem ctx sa sb (\t. t = s) Q (\r. F) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
       ?n r. gas_path_mem ctx func t n r /\ exit_result r /\ R r) ==>
  ?n r. gas_path_mem ctx func s n r /\ exit_result r /\ R r
Proof
  strip_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule gas_path_mem_exec >> strip_tac >> gvs[exit_result_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  irule run_from_gas_path_mem >> simp[exit_result_def] >>
  metis_tac[exit_result_def]
QED

Theorem tuple_load_ret_path_mem[local]:
  compile_load_tuple_elements cenv bop tys off sa = (elems,sb) /\
  emit_inst RET (elems ++ [rpc]) [] sb = ((),sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w /\ eval_operand rpc s = SOME pc /\
  EVERY is_word_type tys /\
  w2n w + off + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + off + 32 * LENGTH tys < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path_mem ctx func s n r /\ exit_result r /\
    ?vars. r = IntRet <|iret_values := tuple_words cenv w tys off s.vs_memory;
                       iret_adopt_fmp := NONE|>
                     (s with <|vs_vars := vars;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
      (!x. not_fresh_at sa x ==>
           lookup_var x (s with vs_vars := vars) = lookup_var x s)
Proof
  strip_tac >>
  drule_all compile_load_tuple_elements_frag_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `frag_exec_mem ctx sa sb _ post _` >>
  ho_match_mp_tac (Q.INST [`Q` |-> `post`] frag_mem_exit_path) >> simp[] >>
  rpt strip_tac >> gvs[Abbr `post`] >>
  `eval_operand rpc (s with <|vs_vars := vars;
      vs_inst_idx := LENGTH sb.cs_current_insts|>) = SOME pc` by
    (qsuff_tac `eval_operand rpc (s with <|vs_vars := vars;
       vs_inst_idx := LENGTH sb.cs_current_insts|>) = eval_operand rpc s`
     >- simp[] >> irule eval_operand_old_vars >> simp[] >>
     qexists_tac `sa` >> simp[]) >>
  `~(s with <|vs_vars := vars; vs_inst_idx := LENGTH sb.cs_current_insts|>).vs_halted /\
   (s with <|vs_vars := vars; vs_inst_idx := LENGTH sb.cs_current_insts|>).vs_current_bb = sb.cs_current_bb /\
   (s with <|vs_vars := vars; vs_inst_idx := LENGTH sb.cs_current_insts|>).vs_inst_idx = LENGTH sb.cs_current_insts` by simp[] >>
  drule_all emit_ret_values_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[exit_result_def] >>
  qexists_tac `vars` >> simp[] >> fs[lookup_var_def]
QED

Theorem compile_internal_tuple_return_parts[local]:
  cenv.ce_return_buf = NONE /\ 0 < cenv.ce_returns_count /\
  (case ty of TupleT ts => ts | StructT nm =>
    MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nm))
    | _ => []) = tys /\ tys <> [] /\
  compile_internal_return_from_env cenv ty src_ty bop rpc sa = ((),sc) ==>
  ?su elems sb.
    compile_return_unlock cenv sa = ((),su) /\
    compile_load_tuple_elements cenv bop tys 0 su = (elems,sb) /\
    emit_inst RET (elems ++ [rpc]) [] sb = ((),sc)
Proof
  strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >> metis_tac[]
QED
