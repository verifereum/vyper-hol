(* Shared effects at a related FMP instruction, without whole-run safety. *)
Theory gasFocusFmpCutSharedEffect
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadJointStorageWrite
  o1LowerDloadShared o1LowerDloadRangeTransport ptrDiscipline ptrStaticDiscipline
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomWf
  venomState venomInst vfmState memLocDefs pointerConfinedDefs words byte finite_map pred_set list

Theorem cut_storage_store[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ inst.inst_outputs = [] /\
  step_inst_base inst s = OK s1 /\
  t.vs_call_ctx = s.vs_call_ctx /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  (!kop vop key v. inst.inst_operands = [kop;vop] /\
    eval_operand kop s = SOME key /\ eval_operand vop s = SOME v ==>
    ?w. eval_operand kop t = SOME key /\ eval_operand vop t = SOME w /\
        word_agree_except (op_taint tn vop) v w) ==>
  ?t1. step_inst_base inst t = OK t1 /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    (step_taint inst s s1 tn).t_mem = tn.t_mem /\
    s1.vs_memory = s.vs_memory /\ t1.vs_memory = t.vs_memory /\
    s1.vs_vars = s.vs_vars /\ t1.vs_vars = t.vs_vars /\
    s1.vs_returndata = s.vs_returndata /\ t1.vs_returndata = t.vs_returndata
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  gvs[eval_operands_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def] >>
  rename1 `inst.inst_operands = [kop;vop]` >>
  rename [`eval_operand kop s = SOME key`, `eval_operand vop s = SOME v`]
  >- (`step_taint inst s (sstore key v s) tn =
        tn with t_stor := key_update tn.t_stor key (op_taint tn vop)` by
        simp[step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
             adopt_reset_def, mem_taint_def, new_site_bytes_def, written_taint_def,
             step_writes_def, source_memory_write_ranges_def, range_bytes_def,
             sstore_def, FLOOKUP_DEF, taint_component_equality,
             EXTENSION, SF CONJ_ss, DRESTRICT_UNIV] >>
      simp[] >> reverse conj_tac >- simp[sstore_def] >> irule ld_shared_sstore >> simp[]) >>
  `step_taint inst s (tstore key v s) tn =
     tn with t_trans := key_update tn.t_trans key (op_taint tn vop)` by
    simp[step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
         adopt_reset_def, mem_taint_def, new_site_bytes_def, written_taint_def,
         step_writes_def, source_memory_write_ranges_def, range_bytes_def,
         tstore_def, FLOOKUP_DEF, taint_component_equality,
         EXTENSION, SF CONJ_ss, DRESTRICT_UNIV] >>
  simp[] >> reverse conj_tac >- simp[tstore_def] >> irule ld_shared_tstore >> simp[]
QED
