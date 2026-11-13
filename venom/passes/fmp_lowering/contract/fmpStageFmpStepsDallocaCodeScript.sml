Theory fmpStageFmpStepsDallocaCode
Ancestors
  fmpStageControlWalk fmpLowerSequenceExec fmpLowerDefs irSupply
  venomFnScheduleRunner finite_map list rich_list

Theorem fmp_dalloca_head_fresh[local]:
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\
  MEM runner sp.irs_used_vars /\ list_subset vars sp.irs_used_vars /\
  MEM out vars /\ runner <> out /\
  fmp_lower_inst infos ctx runner sp inst = SOME (head,sp') ==>
  ?plus31 mask aligned ai ni mi bi.
    head = [mk_inst ai ADD [Lit 31w;size_op] [plus31];
      mk_inst ni NOT [Lit 31w] [mask];
      mk_inst mi AND [Var plus31;Var mask] [aligned];
      mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] /\
    ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
    ~MEM plus31 vars /\ ~MEM mask vars /\ ~MEM aligned vars
Proof
  strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs()] >>
  imp_res_tac (cj 1 fresh_ir_var_contract) >>
  imp_res_tac (cj 2 fresh_ir_var_contract) >>
  gvs[list_subset_def, EVERY_MEM] >>
  simp[] >> metis_tac[]
QED

Theorem fmp_dalloca_indexed_suffix:
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\ MEM runner sp.irs_used_vars /\
  list_subset vars sp.irs_used_vars /\ MEM out vars /\ runner <> out /\
  ALL_DISTINCT (MAP FST restores) /\
  (!j b. MEM ((lbl,j),b) restores <=>
    idx <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  fmp_lower_indexed infos ctx runner lbl idx sp restores (inst::insts) =
    SOME (code,leftover,sp') ==>
  ?plus31 mask aligned ai ni mi bi tail.
    DROP (if (lbl,idx) IN FDOM plan then 1 else 0) code =
      [mk_inst ai ADD [Lit 31w;size_op] [plus31];
       mk_inst ni NOT [Lit 31w] [mask];
       mk_inst mi AND [Var plus31;Var mask] [aligned];
       mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] ++ tail /\
    ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
    ~MEM plus31 vars /\ ~MEM mask vars /\ ~MEM aligned vars
Proof
  strip_tac >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once fmp_lower_indexed_def] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  drule_all fmp_control_select_plan >> strip_tac >>
  `LENGTH prefix = LENGTH bases` by metis_tac[fmp_control_emit_length] >>
  `MEM runner s0.irs_used_vars /\ list_subset vars s0.irs_used_vars` by
    (gvs[list_subset_def, EVERY_MEM] >>
     metis_tac[fmp_control_emit_vars_mono]) >>
  gvs[] >> drule_all fmp_dalloca_head_fresh >> strip_tac >>
  gvs[] >>
  qexistsl_tac [`plus31`,`mask`,`aligned`,`ai`,`ni`,`mi`,`bi`,`tail`] >>
  qpat_x_assum `LENGTH prefix = _` (SUBST1_TAC o GSYM) >>
  simp[APPEND_ASSOC, DROP_APPEND] >>
  `LENGTH prefix - (LENGTH prefix + 4) = 0` by decide_tac >> simp[]
QED
