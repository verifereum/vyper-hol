(* Provenance-backed scratch-word reads. *)
Theory ctorDeployMemoryRunPtrPrefixWordRead
Ancestors
  ctorDeployMemoryRunPtrPrefixSteps ptrSafeRun ptrDiscipline
  venomExecSemantics venomState venomInst memLocDefs codegenRel contextCodegenRel finite_map words

Theorem prefix_mload_dispatch[local]:
  step_inst_base (mk_inst iid MLOAD [addr] [x]) s =
  exec_read1 (\a s. mload (w2n a) s) (mk_inst iid MLOAD [addr] [x]) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_mload_step:
  eval_operand addr s = SOME w ==>
  step_inst_base (mk_inst iid MLOAD [addr] [x]) s =
    OK (update_var x (mload (w2n w) s) s)
Proof
  simp[prefix_mload_dispatch, exec_read1_def, mk_inst_def]
QED

Theorem prefix_mload_ghost_step:
  eval_operand addr s = SOME w ==>
  let inst = mk_inst iid MLOAD [addr] [x];
      t = update_var x (mload (w2n w) s) s
  in ghost_step fuel ctx PG G tn inst s =
    (DRESTRICT G (COMPL {x}), step_taint inst s t tn)
Proof
  rpt strip_tac >> simp[] >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_mload_step,
       mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       prefix_mload_dispatch, exec_read1_def]
QED

Theorem prefix_mload_ptr_step:
  eval_operand (Var p) s = SOME w /\
  FLOOKUP G p = SOME (b,sz) /\ b <= w2n w /\ w2n w+32 <= b+sz /\
  op_taint tn (Var p) = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid MLOAD [Var p] [x]) s
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, step_inst_non_invoke,
       prefix_mload_step] >>
  simp[access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mem_read_ops_def, mk_inst_def,
       taint_ok_def, REWRITE_RULE[mk_inst_def] prefix_mload_dispatch,
       exec_read1_def, update_var_def, allocas_from_def] >> metis_tac[]
QED

Theorem prefix_mload_output_clean:
  eval_operand addr s = SOME w /\
  (!k. k < 32 ==> w2n w+k NOTIN tn.t_mem) ==>
  op_taint (step_taint (mk_inst iid MLOAD [addr] [x]) s t tn) (Var x) = {}
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, FLOOKUP_UPDATE, mem_word_taint_def,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem prefix_mload_taint_frame:
  let t = update_var x w s;
      tn' = step_taint (mk_inst iid MLOAD [addr] [x]) s t tn in
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. y <> x ==> FLOOKUP tn'.t_var y = FLOOKUP tn.t_var y)
Proof
  simp[step_taint_def, mk_inst_def, set_var_taint_def, mem_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       FLOOKUP_UPDATE, DRESTRICT_UNIV, new_site_bytes_def,
       update_var_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, FLOOKUP_DEF] >>
  simp[pred_setTheory.EXTENSION, SF CONJ_ss, FAPPLY_FUPDATE_THM]
QED

Theorem prefix_mload_prov_frame:
  FLOOKUP (DRESTRICT G (COMPL {x})) x = NONE /\
  (!y. y <> x ==> FLOOKUP (DRESTRICT G (COMPL {x})) y = FLOOKUP G y)
Proof
  simp[FLOOKUP_DRESTRICT]
QED

Theorem prefix_mload_endpoint_frame:
  eval_operand addr s = SOME w ==>
  let t = update_var x (mload (w2n w) s) s in
    eval_operand (Var x) t = SOME (mload (w2n w) s) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (allocas_from lo t <=> allocas_from lo s) /\
    (allocas_below_fmp t <=> allocas_below_fmp s)
Proof
  simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       allocas_from_def, allocas_below_fmp_def]
QED

val _ = export_theory();
