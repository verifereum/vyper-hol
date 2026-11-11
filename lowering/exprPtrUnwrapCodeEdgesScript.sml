(* Runtime immutable access uses DLOAD and unrolled copy instructions. *)
Theory exprPtrUnwrapCodeEdges
Ancestors
  exprLowering context compileEnv exprPtrUnwrapCopyEdges fragGasSeqPtr
  ptrSafeRun ptrDiscipline venomExecProps bodyPtrDefs codegenRel contextCodegenRel
  venomExecSemantics venomInstProofs venomInst venomState finite_map

Theorem unwrap_runtime_code_route:
  ~is_word_type ty /\ p.ptr_location = LocCode ==>
  unwrap_value cenv (LocatedValue ty p) =
    compile_ensure_in_memory p.ptr_operand LocCode (type_memory_bytes cenv ty)
      ((type_memory_bytes cenv ty + 31) DIV 32)
      cenv.ce_is_ctor cenv.ce_imm_alloca
Proof
  simp[unwrap_value_def]
QED

Theorem runtime_code_copy_step:
  compile_imm_copy_to_memory F imm src dst (SUC n) off =
    do src_op <- compile_lit_byte_offset src off;
       value <- emit_op DLOAD [src_op];
       dst_op <- compile_lit_byte_offset dst off;
       emit_void MSTORE [dst_op; value];
       compile_imm_copy_to_memory F imm src dst n (off + 32)
    od
Proof
  simp[compile_imm_copy_to_memory_def, compile_imm_load_word_def]
QED

Theorem runtime_code_load_clean:
  op_taint (step_taint (mk_inst id DLOAD [a] [out]) s u tn) (Var out) = {}
Proof
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem ptr_inst_ok_code_load:
  eval_operand a s = SOME off /\ op_taint tn a = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id DLOAD [a] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, update_var_def]
QED

Theorem code_load_counted_edge:
  eval_operand a s = SOME off /\ op_taint tn a = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id DLOAD [a] [out]) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id DLOAD [a] [out])
      (update_var out (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))) s))
    (step_taint (mk_inst id DLOAD [a] [out]) s
      (update_var out (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))) s) tn)
    (OK ((update_var out (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id DLOAD [a] [out]) s` by
    (irule ptr_inst_ok_code_load >> simp[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_ptr_edge >>
  gvs[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs, exec_read1_def]
QED

Theorem runtime_code_copy_singleton:
  compile_imm_copy_to_memory F imm src dst (SUC 0) 0 =
    do value <- emit_op DLOAD [src]; emit_void MSTORE [dst; value] od
Proof
  simp[compile_imm_copy_to_memory_def, compile_lit_byte_offset_def,
       compile_imm_load_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem runtime_code_store_after_load:
  eval_operand src s = SOME off /\ op_taint tn src = {} /\
  root <> out /\ ptr_covers G tn root s 32 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var out value s /\
  G1 = step_prov PG G (mk_inst id DLOAD [src] [out]) u /\
  tn1 = step_taint (mk_inst id DLOAD [src] [out]) s u tn /\
  eval_operand (Var root) u = SOME addr ==>
  ptr_inst_ok D lo fuel ctx fn G1 tn1
    (mk_inst sid MSTORE [Var root; Var out] []) u /\
  (step_taint (mk_inst sid MSTORE [Var root; Var out] []) u
    (mstore (w2n addr) value u) tn1).t_mem =
    tn1.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32}
Proof
  strip_tac >>
  `ptr_covers G1 tn1 root u 32` by
    (fs[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
        step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
        FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, lookup_var_def, update_var_def] >> metis_tac[]) >>
  conj_tac >-
    (irule ptr_inst_ok_mstore_tainted >>
     fs[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  `eval_operand (Var out) u = SOME value` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint tn1 (Var out) = {}` by simp[runtime_code_load_clean] >>
  asm_simp_tac bool_ss [mstore_transferred_taint] >> simp[]
QED

Theorem ensure_code_copy_route:
  compile_ensure_in_memory src LocCode bytes words is_ctor imm =
    do buf <- compile_alloc_buffer bytes;
       compile_imm_copy_to_memory is_ctor imm src buf.buf_operand
         ((bytes + 31) DIV 32) 0;
       return buf.buf_operand
    od
Proof
  simp[compile_ensure_in_memory_def]
QED
