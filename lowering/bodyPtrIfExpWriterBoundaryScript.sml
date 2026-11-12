Theory bodyPtrIfExpWriterBoundary
Ancestors context fragExec venomWf emitHelper compileEnv venomInst

(* Structural obstruction only: no execution or full body frame is asserted. *)
Theorem ifexp_containment_allows_phi_writer:
  ?sa sb rb fn p u bb i.
    compile_alloc_buffer 32 sa = (rb,sb) /\
    rb.buf_operand = Var p /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    lookup_block u fn.fn_blocks = SOME bb /\
    MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
    MEM p i.inst_outputs
Proof
  qexists_tac `<| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
    cs_current_bb := "entry"; cs_current_insts := []; cs_blocks := [];
    cs_data_sections := [] |>` >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >>
  qexists_tac `mk_raw_function "probe"
    [<| bb_label := "entry";
        bb_instructions := [mk_inst 0 ALLOCA [Lit 32w] ["%0"]] |>;
     <| bb_label := "other";
        bb_instructions := [mk_inst 1 PHI [] ["%0"]] |>]` >>
  qexistsl_tac [`"other"`,
    `<| bb_label := "other"; bb_instructions := [mk_inst 1 PHI [] ["%0"]] |>`,
    `mk_inst 1 PHI [] ["%0"]`] >>
  simp[fn_has_code_def, emitted_blocks_def, fn_inst_ids_distinct_def,
       mk_raw_function_def, lookup_block_def, mk_inst_def] >> EVAL_TAC >> simp[]
QED
