Theory exprSimAbiEncodeArgsTupleTarget
Ancestors
  exprSimAbiEncodeArgsTupleSource exprSimAbiEncodeArgsTupleProbe
  exprLowering compileEnv fragGasMode intCallStep
  venomExecSemantics venomInst venomState finite_map gasCount fragGasPath
  placeMemoryStaging emitHelperProps loweringHalt emitHelper fragExec
  abiDecodeStaticProps

val _ = temp_delsimps ["exec_block_non_phis"];

Theorem tuple_return_metadata:
  compute_func_info sft tuple_narrow
    (type_memory_bytes ce tuple_narrow) [] = (0,128,[])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

Theorem tuple_actual_call_compile:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  compile_expr ce ty tuple_call sa =
    (let (buf,sm) = compile_alloc_buffer 128 sa in
     let (_,sb) = emit_void INVOKE
       [Label (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
          (nsid_to_string (NONE,"f"))
          (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor);
        buf.buf_operand] sm in
     (LocatedValue tuple_narrow (base_ptr buf),sb))
Proof
  simp[tuple_call_def, Once compile_expr_def, compile_call_def,
       compile_multi_vvs_def, compile_stage_intcall_args_def, comp_return_def] >>
  strip_tac >> Cases_on `compile_alloc_buffer 128 sa` >>
  simp[compile_stage_intcall_args_def, comp_return_def]
QED

Theorem tuple_actual_unwrap:
  lower_value compile_expr ce ty tuple_call sa =
    (case compile_expr ce ty tuple_call sa of (vv,sb) => unwrap_value ce vv sb)
Proof
  Cases_on `compile_expr ce ty tuple_call sa` >>
  simp[lower_value_def, comp_bind_def]
QED

Theorem tuple_actual_singleton_operand:
  compile_expr ce tuple_wide tuple_call sa =
    (LocatedValue tuple_narrow (base_ptr buf),sb) ==>
  compile_abi_encode_args compile_expr ce [tuple_call] sa = ([buf.buf_operand],sb)
Proof
  simp[compile_abi_encode_args_def, tuple_call_def,
       vyperASTTheory.expr_type_def, expr_can_mutate_def,
       unwrap_value_def, tuple_narrow_def, is_word_type_def,
       contextTheory.base_ptr_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* A constant-return callee.  Its sole parameter is the caller-owned buffer. *)
Definition tuple_target_block_def:
  tuple_target_block = <| bb_label := "tuple_entry"; bb_instructions :=
    [mk_inst 0 PARAM [Lit 0w] ["p"];
     mk_inst 1 MSTORE [Var "p"; Lit 1w] [];
     mk_inst 2 ADD [Var "p"; Lit 32w] ["q"];
     mk_inst 3 MSTORE [Var "q"; Lit (n2w (170 * 2 ** 248))] [];
     mk_inst 4 ADD [Var "p"; Lit 64w] ["r"];
     mk_inst 5 MSTORE [Var "r"; Lit 1w] [];
     mk_inst 6 ADD [Var "p"; Lit 96w] ["z"];
     mk_inst 7 MSTORE [Var "z"; Lit (n2w (187 * 2 ** 248))] [];
     mk_inst 8 RET [Lit 0w] []] |>
End

Definition tuple_target_function_def:
  tuple_target_function name = mk_raw_function name [tuple_target_block]
End

Definition tuple_target_writes_def:
  tuple_target_writes p s =
    mstore (w2n (p + 96w)) (n2w (187 * 2 ** 248))
      (mstore (w2n (p + 64w)) 1w
        (mstore (w2n (p + 32w)) (n2w (170 * 2 ** 248))
          (mstore (w2n p) 1w s)))
End

Theorem tuple_target_run:
  setup_callee (tuple_target_function name) [p] s = SOME cs ==>
  ?t. run_blocks 1 ctx (tuple_target_function name) cs =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |> t /\
      t.vs_memory = (tuple_target_writes p s).vs_memory /\
      t.vs_gas_readings = s.vs_gas_readings /\
      merge_callee_state s t =
        s with vs_memory := (tuple_target_writes p s).vs_memory
Proof
  simp[setup_callee_def, tuple_target_function_def, mk_raw_function_def] >>
  strip_tac >> gvs[] >>
  simp[Once run_blocks_def, tuple_target_block_def, lookup_block_def,
       listTheory.FIND_thm, eval_phis_def, phi_prefix_length_def, mk_inst_def,
       Excl "exec_block_non_phis"] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_write2_def, exec_pure2_def,
       eval_operand_def, eval_operands_def, update_var_def, lookup_var_def,
       is_terminator_def, FLOOKUP_UPDATE] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_write2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, mstore_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, update_var_def, is_terminator_def] >>
  qpat_abbrev_tac `mem1 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_write2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, mstore_def, is_terminator_def] >>
  qpat_abbrev_tac `mem2 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, update_var_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_write2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, mstore_def, is_terminator_def] >>
  qpat_abbrev_tac `mem3 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, update_var_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_write2_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, mstore_def, is_terminator_def] >>
  qpat_abbrev_tac `mem4 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, eval_operand_def, eval_operands_def,
       merge_callee_state_def] >>
  ` (mstore (w2n p) 1w s).vs_memory = mem1` by
    simp[mstore_def, Abbr `mem1`] >>
  ` (mstore (w2n (p + 32w)) (n2w (170 * 2 ** 248))
       (mstore (w2n p) 1w s)).vs_memory = mem2` by
    simp[Once mstore_def, Abbr `mem2`] >>
  ` (mstore (w2n (p + 64w)) 1w
       (mstore (w2n (p + 32w)) (n2w (170 * 2 ** 248))
         (mstore (w2n p) 1w s))).vs_memory = mem3` by
    simp[Once mstore_def, Abbr `mem3`] >>
  simp[tuple_target_writes_def, Once mstore_def, Abbr `mem4`] >>
  fs[] >> simp[Once mstore_def]
QED

Theorem tuple_target_count:
  setup_callee (tuple_target_function name) [p] s = SOME cs ==>
  gas_count_blocks 1 ctx (tuple_target_function name) cs = 0
Proof
  simp[setup_callee_def, tuple_target_function_def, mk_raw_function_def] >>
  strip_tac >> gvs[] >>
  simp[Once gas_count_blocks_def, tuple_target_block_def, lookup_block_def,
       listTheory.FIND_thm, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once gas_count_blocks_def] >>
  reverse conj_tac >- (CASE_TAC >> simp[]) >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, eval_operand_def,
       eval_operands_def, update_var_def, is_terminator_def] >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_write2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, mstore_def,
       is_terminator_def] >>
  qpat_abbrev_tac `mem1 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def,
       is_terminator_def] >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_write2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, mstore_def,
       is_terminator_def] >>
  qpat_abbrev_tac `mem2 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def,
       is_terminator_def] >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_write2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, mstore_def,
       is_terminator_def] >>
  qpat_abbrev_tac `mem3 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def,
       is_terminator_def] >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, exec_write2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, mstore_def,
       is_terminator_def] >>
  qpat_abbrev_tac `mem4 = (TAKE _ _ ++ _) ++ _` >>
  simp[Once gas_count_block_def, gas_count_step_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def, eval_operand_def,
       eval_operands_def]
QED

Definition tuple_target_context_def:
  tuple_target_context name ctx =
    ctx with ctx_functions := [tuple_target_function name]
End

Theorem tuple_target_invoke:
  eval_operand op s = SOME p ==>
  step_inst 1 (tuple_target_context name ctx)
    (mk_inst id INVOKE [Label name; op] []) s =
    OK (s with vs_memory := (tuple_target_writes p s).vs_memory) /\
  gas_count_step 1 (tuple_target_context name ctx)
    (mk_inst id INVOKE [Label name; op] []) s = 0
Proof
  strip_tac >>
  `?cs. setup_callee (tuple_target_function name) [p] s = SOME cs` by
    simp[setup_callee_def, tuple_target_function_def, mk_raw_function_def] >>
  drule tuple_target_run >>
  disch_then (qspec_then `tuple_target_context name ctx` strip_assume_tac) >>
  drule tuple_target_count >> strip_tac >>
  fs[Once step_inst_def, gas_count_step_def, mk_inst_def, decode_invoke_def,
       tuple_target_context_def, lookup_function_def, listTheory.FIND_thm,
       tuple_target_function_def, mk_raw_function_def,
       eval_operands_def, bind_outputs_def, adopt_return_fmp_def]
QED

Theorem tuple_target_invoke_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id INVOKE [Label name; op] []) /\
  eval_operand op s = SOME p ==>
  gas_marked_path F (tuple_target_context name ctx) fn s 0
    (OK (s with <| vs_memory := (tuple_target_writes p s).vs_memory;
                   vs_inst_idx := SUC s.vs_inst_idx |>))
Proof
  strip_tac >>
  `step_inst 1 (tuple_target_context name ctx)
      (mk_inst id INVOKE [Label name; op] []) s =
    OK (s with vs_memory := (tuple_target_writes p s).vs_memory) /\
   gas_count_step 1 (tuple_target_context name ctx)
      (mk_inst id INVOKE [Label name; op] []) s = 0` by
    (irule tuple_target_invoke >> simp[]) >>
  `gas_path_edge (tuple_target_context name ctx) fn s 0
    (OK (s with <| vs_memory := (tuple_target_writes p s).vs_memory;
                   vs_inst_idx := SUC s.vs_inst_idx |>))` by
    (simp[gas_path_edge_def] >>
     qexists_tac `1` >>
     simp[cj 1 tuple_target_invoke, cj 2 tuple_target_invoke] >>
     simp[is_terminator_def]) >>
  simp[gas_marked_path_def] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[cj 1 gas_path_rules]
QED

Theorem tuple_target_allocated_path:
  compile_alloc_buffer 128 sa = (buf,sm) /\
  emit_void INVOKE [Label name; buf.buf_operand] sm = ((),sb) /\
  stmt_state_rel (tuple_target_context name ctx) fn ce cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r p. gas_marked_path F (tuple_target_context name ctx) fn s 0
    (OK (r with <| vs_memory := (tuple_target_writes p r).vs_memory;
                   vs_inst_idx := LENGTH sb.cs_current_insts |>)) /\
    stmt_state_rel (tuple_target_context name ctx) fn ce cx es r /\
    sa.cs_next_id < sm.cs_next_id /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand buf.buf_operand r = SOME p /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n p,128) /\
    w2n p + 128 < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (!local b len. local_region ce es.scopes r local b len ==>
       regions_disjoint (w2n p) 128 b len)
Proof
  rpt strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
        comp_return_def, emit_def, fresh_id_def, cs_extends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `128 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all compile_alloc_buffer_forward >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
        comp_return_def, emit_def, fresh_id_def] >>
  drule_all fn_has_code_same_block >>
  simp[] >> strip_tac >>
  `gas_marked_path F (tuple_target_context name ctx) fn r 0
     (OK (r with <|vs_memory := (tuple_target_writes tw r).vs_memory;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>))` by
    (`gas_marked_path F (tuple_target_context name ctx) fn r 0
        (OK (r with <|vs_memory := (tuple_target_writes tw r).vs_memory;
                      vs_inst_idx := SUC r.vs_inst_idx|>))` by
       (irule tuple_target_invoke_path >> metis_tac[]) >>
     fs[arithmeticTheory.ADD1] >> metis_tac[]) >>
  qexistsl_tac [`r`, `tw`] >> simp[] >>
  drule_all gas_marked_path_then >> simp[] >> metis_tac[]
QED

Theorem tuple_target_writes_frame:
  w2n (p:bytes32) + 128 < dimword (:256) /\
  (i < w2n p \/ w2n p + 128 <= i) ==>
  mem_bytes_at i 1 (tuple_target_writes p s).vs_memory =
  mem_bytes_at i 1 s.vs_memory
Proof
  strip_tac >>
  `w2n (p + 32w) = w2n p + 32 /\
   w2n (p + 64w) = w2n p + 64 /\
   w2n (p + 96w) = w2n p + 96` by
    (rpt conj_tac >> irule w2n_add_n2w_lt >> decide_tac) >>
  simp[tuple_target_writes_def] >>
  rpt (irule EQ_TRANS >>
       irule_at Any mem_bytes_at_mstore_outside >> conj_tac >- decide_tac) >>
  simp[]
QED


Theorem tuple_target_invoke_in_context:
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) /\
  eval_operand op s = SOME p ==>
  step_inst 1 ctx (mk_inst id INVOKE [Label name; op] []) s =
    OK (s with vs_memory := (tuple_target_writes p s).vs_memory) /\
  gas_count_step 1 ctx (mk_inst id INVOKE [Label name; op] []) s = 0
Proof
  strip_tac >>
  `?cs. setup_callee (tuple_target_function name) [p] s = SOME cs` by
    simp[setup_callee_def, tuple_target_function_def, mk_raw_function_def] >>
  drule tuple_target_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule tuple_target_count >> strip_tac >>
  fs[Once step_inst_def, gas_count_step_def, mk_inst_def, decode_invoke_def,
     eval_operands_def, bind_outputs_def, adopt_return_fmp_def]
QED

Theorem tuple_target_invoke_path_in_context:
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id INVOKE [Label name; op] []) /\
  eval_operand op s = SOME p ==>
  gas_marked_path F ctx fn s 0
    (OK (s with <|vs_memory := (tuple_target_writes p s).vs_memory;
                  vs_inst_idx := SUC s.vs_inst_idx|>))
Proof
  strip_tac >>
  drule_all tuple_target_invoke_in_context >> strip_tac >>
  `gas_path_edge ctx fn s 0
    (OK (s with <|vs_memory := (tuple_target_writes p s).vs_memory;
                  vs_inst_idx := SUC s.vs_inst_idx|>))` by
    (simp[gas_path_edge_def] >> qexists_tac `1` >>
     simp[is_terminator_def]) >>
  simp[gas_marked_path_def] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[cj 1 gas_path_rules]
QED

Theorem tuple_target_allocated_path_in_context:
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) /\
  compile_alloc_buffer 128 sa = (buf,sm) /\
  emit_void INVOKE [Label name; buf.buf_operand] sm = ((),sb) /\
  stmt_state_rel ctx fn ce cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r p. gas_marked_path F ctx fn s 0
    (OK (r with <|vs_memory := (tuple_target_writes p r).vs_memory;
                  vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
    stmt_state_rel ctx fn ce cx es r /\
    sa.cs_next_id < sm.cs_next_id /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand buf.buf_operand r = SOME p /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n p,128) /\
    w2n p + 128 < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (!local b len. local_region ce es.scopes r local b len ==>
       regions_disjoint (w2n p) 128 b len)
Proof
  rpt strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
        comp_return_def, emit_def, fresh_id_def, cs_extends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `128 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all compile_alloc_buffer_forward >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
        comp_return_def, emit_def, fresh_id_def] >>
  drule_all fn_has_code_same_block >> simp[] >> strip_tac >>
  `gas_marked_path F ctx fn r 0
     (OK (r with <|vs_memory := (tuple_target_writes tw r).vs_memory;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>))` by
    (`gas_marked_path F ctx fn r 0
        (OK (r with <|vs_memory := (tuple_target_writes tw r).vs_memory;
                      vs_inst_idx := SUC r.vs_inst_idx|>))` by
       (irule tuple_target_invoke_path_in_context >> metis_tac[]) >>
     fs[arithmeticTheory.ADD1] >> metis_tac[]) >>
  qexistsl_tac [`r`, `tw`] >> simp[] >>
  drule_all gas_marked_path_then >> simp[] >> metis_tac[]
QED
