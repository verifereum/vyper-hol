(* Memory bounds for the stack-tuple internal-return loads. *)
Theory internalReturnTupleMem
Ancestors
  internalReturnSequenceMem stmtSimReturn fragExecMem instMemFrontier memSafeRun
  stmtLowering context compileEnv emitHelper exprLoweringProps emitHelperProps abiTupleValueEncoding
  venomExecSemantics venomState venomInst words list arithmetic

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
