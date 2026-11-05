(* Actual empty-runtime instruction inventory for the bounded fixture probe. *)
Theory bodyMemTbConvertZeroEntry
Ancestors
  bodyMemTbConvertZeroFixture compileVyper venomCompilerTypes venomPolicyTypes
  venomInst fragExec list rich_list

Theorem convert_zero_empty_runtime_no_alloca:
  EVERY (\f. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f))
    (THE (lower_vyper_runtime_unit []
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>)).cu_context.ctx_functions
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, fn_insts_blocks_def]
QED

Theorem convert_zero_slice_has_alloca:
  !cenv. cenv.ce_target = all_capabilities ==>
  EXISTS (\i. i.inst_opcode = ALLOCA)
    (SND (compile_expr cenv (BaseT BoolT)
      (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
        [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])])
      (initial_compile_state "__entry"))).cs_current_insts
Proof
  rpt strip_tac >> EVAL_TAC
QED

Theorem convert_zero_empty_runtime_slice_excluded:
  !cenv fn.
    cenv.ce_target = all_capabilities /\
    MEM fn (THE (lower_vyper_runtime_unit []
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>)).cu_context.ctx_functions ==>
    ~fn_has_code (initial_compile_state "__entry")
      (SND (compile_expr cenv (BaseT BoolT)
        (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
          [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])])
        (initial_compile_state "__entry"))) fn
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  drule convert_zero_slice_has_alloca >>
  disch_then (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
  assume_tac (REWRITE_RULE [EVERY_MEM] convert_zero_empty_runtime_no_alloca) >>
  fs[] >> rename1 `i.inst_opcode = ALLOCA` >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `MEM i (fn_insts fn)` by
    (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED
