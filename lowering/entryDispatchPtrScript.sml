(* Pointer-safe scalar/control-flow transport for entry dispatch. *)
Theory entryDispatchPtr
Ancestors ptrSafeRun ptrDiscipline moduleLoweringProps moduleLowering
  fragExec venomExecSemantics venomInst venomState list finite_map words
  contextCodegenRel codegenRel

Theorem ptr_safe_jump_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!G' tn'. ptr_safe_blocks D lo fuel ctx fn PG G' tn' (jump_to lbl s)) ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, step_inst_non_invoke,
           step_inst_base_def, jump_to_def, op_taint_def]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       is_terminator_def]
QED

Theorem ptr_safe_cond_jump_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label yes; Label no] []) /\
  eval_operand op s = SOME v /\ op_taint tn op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!G' tn'. ptr_safe_blocks D lo fuel ctx fn PG G' tn'
     (jump_to (if v <> 0w then yes else no) s)) ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, step_inst_non_invoke,
           step_inst_base_def, jump_to_def, op_taint_def] >>
      Cases_on `v = 0w` >> simp[jump_to_def] >>
      rpt strip_tac >> Cases_on `op'` >> gvs[op_taint_def] >>
      strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       is_terminator_def] >>
  Cases_on `v = 0w` >> gvs[]
QED

Theorem ptr_safe_dispatch_scalar_step:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  EVERY (\op. op_taint tn op = {}) ops /\
  (!u v. ops <> [Var u; Var v]) /\
  step_inst fuel ctx (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst id opc ops outs) s
Proof
  strip_tac >>
  fs[MEM] >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_write_ranges_def,
      source_memory_read_ranges_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem dispatch_scalar_out_taint:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  out_taint tn (mk_inst id opc ops outs) s = {}
Proof
  strip_tac >> fs[MEM] >>
  (namedCases_on `ops` ["", "a rest"]
  >- simp[out_taint_def, mk_inst_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def, mk_inst_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >>
      gvs[out_taint_def, mk_inst_def, shift_taint_def,
          pred_setTheory.EXTENSION]) >>
  Cases_on `tail` >> simp[out_taint_def, mk_inst_def])
QED

Theorem dispatch_scalar_output_clean:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) (Var out) = {}
Proof
  strip_tac >> drule_all dispatch_scalar_out_taint >> strip_tac >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE]
QED

Theorem step_taint_single_output_preserves_other_operand:
  op <> Var out ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) op = op_taint tn op
Proof
  Cases_on `op` >> simp[op_taint_def, step_taint_def, mk_inst_def,
                        set_var_taint_def, FLOOKUP_UPDATE]
QED
