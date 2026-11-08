(* Exact variable allocation in selector dispatch. *)
Theory entryDispatchCounters
Ancestors entryDispatchPtr moduleLowering moduleLoweringProps emitHelperProps
  compileEnv list exprLoweringProps codegenRel

Theorem compile_selector_checks_next_var_exact:
  !sels mid st x st'.
    compile_selector_checks mid sels st = (x,st') ==>
    st'.cs_next_var = st.cs_next_var + LENGTH sels
Proof
  Induct
  >- simp[compile_selector_checks_def, comp_return_def] >>
  Cases >> rpt gen_tac >>
  simp[Once compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_inst_extends >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  fs[same_blocks_def]
QED

Theorem compile_selector_dispatch_linear_next_var_exact:
  compile_selector_dispatch_linear sels fallback st = (x,st') ==>
  st'.cs_next_var = st.cs_next_var + 5 + LENGTH sels
Proof
  simp[compile_selector_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  drule compile_selector_checks_next_var_exact >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_inst_extends >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  fs[same_blocks_def]
QED
