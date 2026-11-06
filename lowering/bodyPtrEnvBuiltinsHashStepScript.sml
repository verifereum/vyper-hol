(* The runtime hash reads only the clean payload range, not padding. *)
Theory bodyPtrEnvBuiltinsHashStep
Ancestors bodyPtrEnvBuiltinsHashInput bodyPtrEnvBuiltinsEdges
  bodyPtrDefs compileEnv fragGasSeqPtr fragGasPathPtr
  ptrSafeRun ptrDiscipline venomInst venomState venomExecSemantics
  memLocDefs codegenRel contextCodegenRel finite_map list pred_set

Theorem ptr_inst_ok_hash:
  eval_operand (Var p) s = SOME off /\ eval_operand len s = SOME n /\
  FLOOKUP G p = SOME (b,sz) /\ b <= w2n off /\
  w2n off + w2n n <= b + sz /\
  op_taint tn (Var p) = {} /\ op_taint tn len = {} /\
  (!i. w2n off <= i /\ i < w2n off + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id SHA3 [Var p; len] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke] >>
  simp[memory_range_of_operands_def, mem_read_ops_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[update_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem hash_output_clean:
  ptr_val_ok cx (BaseT (BytesT (Fixed 32))) v (Var out)
    (step_prov PG G (mk_inst id SHA3 [src; len] [out]) u)
    (step_taint (mk_inst id SHA3 [src; len] [out]) s u tn) u
Proof
  simp[ptr_val_ok_def, is_word_type_def, op_taint_def,
       step_taint_def, out_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE] >>
  conj_tac >- (Cases_on `eval_operand src s` >> simp[]) >>
  irule step_prov_out_none >> simp[mk_inst_def] >>
  irule out_prov_other_none >> simp[mk_inst_def]
QED

Theorem hash_counted_edge:
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SHA3 [src; len] [out]) s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id SHA3 [src; len] [out]) /\
  step_inst_base (mk_inst id SHA3 [src; len] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id SHA3 [src; len] [out]) u)
    (step_taint (mk_inst id SHA3 [src; len] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >> gvs[mk_inst_def]
QED
