(* Memory safety transported along a total, synchronized register extension. *)
Theory bodyMemTbExtract32MemoryTransfer
Ancestors
  varsExt exprLoweringProps fragExec fragExecMem instMemFrontier memSafeRun venomExecSemantics venomState venomInst list

Theorem run_inst_seq_mem_ok_total_vars_ext:
  !code s big.
    vars_ext s big /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) code /\
    ((?t. run_inst_seq code s = OK t) \/
     (?a t. run_inst_seq code s = Abort a t)) /\
    run_inst_seq_mem_ok code s /\
    (!i u v. MEM i code /\ vars_ext u v /\
      ((?t. step_inst_base i u = OK t) \/
       (?a t. step_inst_base i u = Abort a t)) /\
      inst_mem_below_frontier i u /\ inst_dload_in_section i u ==>
      inst_mem_below_frontier i v /\ inst_dload_in_section i v) ==>
    run_inst_seq_mem_ok code big
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `vars_ext_result (step_inst_base h s) (step_inst_base h big)` by
    (irule step_inst_base_vars_ext_state >>
     qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_DEF]) >>
  Cases_on `step_inst_base h s` >>
  qpat_x_assum `run_inst_seq (h::code) s = _` mp_tac >>
  simp[Once run_inst_seq_def] >> strip_tac >>
  qpat_x_assum `run_inst_seq_mem_ok (h::code) s` mp_tac >>
  qpat_assum `step_inst_base h s = _`
    (fn th => pure_rewrite_tac[run_inst_seq_mem_ok_def, th]) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  pure_rewrite_tac[vars_ext_result_def] >> strip_tac >>
  `inst_mem_below_frontier h big /\ inst_dload_in_section h big` by
    (qpat_x_assum `!i u v. _` irule >>
     simp[NoAsms, MEM] >> qexists_tac `s` >> metis_tac[]) >>
  qpat_assum `step_inst_base h big = _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `inst_mem_below_frontier h big`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `inst_dload_in_section h big`
    (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms] >>
  (first_x_assum irule >> conj_tac
  >- (qpat_x_assum `!i u v. _` mp_tac >>
      metis_tac[MEM]) >>
  conj_tac
  >- (qpat_x_assum `EVERY _ (h::code)` mp_tac >>
      simp[NoAsms, EVERY_DEF]) >>
  qexists_tac `v` >> metis_tac[])
QED

Theorem mload_total_vars_ext_frontier:
  vars_ext s big /\
  ((?t. step_inst_base (mk_inst id MLOAD [addr] [out]) s = OK t) \/
   (?a t. step_inst_base (mk_inst id MLOAD [addr] [out]) s = Abort a t)) /\
  inst_mem_below_frontier (mk_inst id MLOAD [addr] [out]) s ==>
  inst_mem_below_frontier (mk_inst id MLOAD [addr] [out]) big /\
  inst_dload_in_section (mk_inst id MLOAD [addr] [out]) big
Proof
  strip_tac >>
  qpat_x_assum `vars_ext s big` (strip_assume_tac o REWRITE_RULE [vars_ext_def]) >>
  qpat_x_assum `big = _` SUBST1_TAC >>
  Cases_on `eval_operand addr s` >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
      below_frontier_MLOAD, eval_operand_vars_ext, inst_dload_in_section_def]
QED
