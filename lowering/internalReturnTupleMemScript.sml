(* Consecutive stack-return word loads below the allocation frontier. *)
Theory internalReturnTupleMem
Ancestors
  stmtLoweringProps
  bodyMemAssignTupleTargetsLoad bodyLiteralBufferMemory stmtSimReturn stmtSimReturnTuple
  fragExec fragExecMem fragGasSeqMem context stmtLowering emitHelperProps
  exprLoweringProps freshWrites compileEnv venomState list rich_list arithmetic

Theorem internal_return_tuple_load_mem_ok[local]:
  !tys ce bop off sa elems sb s w.
    compile_load_tuple_elements ce bop tys off sa = (elems,sb) /\
    EVERY (\ty. type_memory_bytes ce ty = 32) tys /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    w2n w + off + 32 * LENGTH tys <= s.vs_alloca_next /\
    w2n w + off + 32 * LENGTH tys <= dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct
  >- (simp[compile_load_tuple_elements_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_load_tuple_elements _ _ _ _ _ = _` mp_tac >>
  simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `emit_op MLOAD _ sm = (v,sh)` >>
  rename1 `compile_load_tuple_elements _ _ _ _ sh = (rest,sf)` >>
  `compile_load_memory pv T sm = (v,sh)` by simp[compile_load_memory_def] >>
  drule_all tuple_elem_load_head_run >> strip_tac >> gvs[] >>
  `w2n (w + n2w off) = w2n w + off` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sh) s` by
    (`w2n (w + n2w off) + 32 <= s.vs_alloca_next` by decide_tac >>
     metis_tac[tuple_elem_load_head_mem_ok]) >>
  `(!x. bop = Var x ==> not_fresh_at sh x) /\
   eval_operand bop (s with vs_vars := vs) = SOME w` by
    (conj_tac
     >- metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
     Cases_on `bop` >> gvs[eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sh sf) (s with vs_vars := vs)` by
    (first_x_assum irule >> qexistsl_tac [`bop`, `ce`, `rest`, `off + 32`, `w`] >>
     simp[] >> decide_tac) >>
  drule_all compile_load_tuple_elements_run >> strip_tac >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sf.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `sh.cs_current_insts = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  simp[] >> irule run_inst_seq_mem_ok_append_run >>
  simp[]
QED

Theorem internal_return_tuple_load_path_mem:
  compile_load_tuple_elements ce bop tys off sa = (elems,sb) /\
  EVERY (\ty. type_memory_bytes ce ty = 32) tys /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w /\
  w2n w + off + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + off + 32 * LENGTH tys <= dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?vs. gas_path_mem ctx func s 0
         (OK (s with <|vs_vars := vs; vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
       (!x. not_fresh_at sa x ==>
          lookup_var x (s with vs_vars := vs) = lookup_var x s) /\
       eval_operands elems (s with vs_vars := vs) =
         SOME (tuple_words ce w tys off s.vs_memory)
Proof
  strip_tac >> drule_all internal_return_tuple_load_mem_ok >> strip_tac >>
  drule_all compile_load_tuple_elements_run >> strip_tac >> gvs[] >>
  drule compile_load_tuple_elements_no_gas >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `sb.cs_current_insts = sa.cs_current_insts ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  qexists_tac `vs` >> simp[]
QED
