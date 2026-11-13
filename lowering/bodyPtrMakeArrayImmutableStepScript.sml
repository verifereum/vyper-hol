(* Arbitrary byte offsets for runtime immutable copies.  Unlike storage
   loops, this compiler recursively advances the byte offset by 32. *)
Theory bodyPtrMakeArrayImmutableStep
Ancestors
  bodyPtrMakeArrayAddCoverage bodyPtrMakeArrayCopiedWord
  immutableCopyExecution context words bodyPtrDefs fragGasSeqPtr
  typedCopyPtr emitHelper emitHelperProps compileEnv exprLoweringProps
  ptrDiscipline venomInst venomState

Theorem immutable_offset_step_bounds:
  off + 32 * SUC n <= m ==>
  off < m /\ off + 32 <= m /\ (off + 32) + 32 * n <= m
Proof
  simp[arithmeticTheory.MULT_SUC] >> decide_tac
QED

Theorem immutable_offset_destination_window:
  ptr_covers G tn root s m /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32 * SUC n <= m ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out ((update_var out (a + n2w off) s) with
      vs_inst_idx := SUC s.vs_inst_idx) 32
Proof
  strip_tac >> irule add_destination_coverage >>
  goal_assum (drule_at Any) >> conj_tac
  >- (qexistsl_tac [`blo`, `cap`] >> simp[]) >>
  qexists_tac `m` >> simp[] >> drule immutable_offset_step_bounds >> simp[]
QED

Theorem immutable_offset_zero_window:
  ptr_covers G tn root s m /\ 32 * SUC n <= m ==>
  ptr_covers G tn root s 32
Proof
  simp[ptr_covers_def, arithmeticTheory.MULT_SUC] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

(* This is a per-instruction check, not an erasure of a fixed-run path. *)
Theorem immutable_byte_offset_checked:
  compile_lit_byte_offset op off sa = (result,sb) /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    (emitted_insts sa sb) s Gf tnf
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, inst_seq_ptr_def]) >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def] >> rpt strip_tac
  >- gvs[emitted_insts_def, inst_seq_ptr_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D 0 0 ctx fn G tn i s` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def]) >>
  simp[] >> Cases_on `step_inst_base i s` >> simp[]
QED

Theorem immutable_byte_offset_opcodes:
  compile_lit_byte_offset op off sa = (result,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def]) >>
  Cases_on `op` >> simp[compile_lit_byte_offset_def, comp_return_def] >>
  rpt gen_tac >> strip_tac
  >- gvs[emitted_insts_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem immutable_byte_offset_ptr_path:
  compile_lit_byte_offset op off sa = (result,sb) /\
  eval_operand op s = SOME a /\ fresh_vars_wrt sa s /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf t. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    eval_operand result t = SOME (a + n2w off) /\
    t.vs_memory = s.vs_memory /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all immutable_byte_offset_execution >> strip_tac >>
  `?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    (emitted_insts sa sb) s Gf tnf` by
    metis_tac[immutable_byte_offset_checked] >>
  drule immutable_byte_offset_opcodes >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`,
    `s' with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`] >>
  simp[] >> Cases_on `result` >> gvs[eval_operand_def, lookup_var_def]
QED
