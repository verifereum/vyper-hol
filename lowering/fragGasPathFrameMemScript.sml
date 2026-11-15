(* State frames for counted paths and checked memory paths, including raw jumps. *)
Theory fragGasPathFrameMem
Ancestors fragGasPath venomInstProofs
  execMemoryLength fragGasPathMem allocaHistory venomExecProofs venomExecSemantics
  venomState fragExec arithmetic

Theorem path_mem_edge_history[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  gas_path_mem_edge ctx fn s n (OK t) ==> alloca_history fn t
Proof
  rw[gas_path_mem_edge_def] >> gvs[exit_result_def]
  >- (drule_all alloca_history_step >> simp[])
  >- (irule history_phi_entry >> goal_assum (drule_at Any) >>
      simp[] >> drule_all alloca_history_step >> simp[])
  >- metis_tac[alloca_history_step]
  >- metis_tac[exit_result_def]
  >- (drule_all alloca_history_step >> simp[])
  >- (irule history_phi_entry >> goal_assum (drule_at Any) >>
      simp[] >> drule_all alloca_history_step >> simp[])
  >- metis_tac[alloca_history_step]
  >> metis_tac[exit_result_def]
QED

Theorem gas_path_mem_zero_history:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  gas_path_mem ctx fn s 0 (OK t) /\
  (!u. gas_path_mem ctx fn s 0 (OK u) ==> alloca_inv u) ==>
  alloca_history fn t
Proof
  qsuff_tac `!ctx fn s n r. gas_path_mem ctx fn s n r ==>
    n = 0 ==> !t. r = OK t ==>
    fn_inst_ids_distinct fn /\ alloca_history fn s /\
    (!u. gas_path_mem ctx fn s 0 (OK u) ==> alloca_inv u) ==>
    alloca_history fn t`
  >- metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
      gvs[] >>
      `~s.vs_halted` by fs[gas_path_mem_edge_def] >>
      `alloca_inv s` by metis_tac[gas_path_mem_rules] >>
      `alloca_history fn s''` by metis_tac[path_mem_edge_history] >>
      first_x_assum irule >> simp[] >>
      metis_tac[gas_path_mem_rules, ADD_CLAUSES])
  >> simp[exit_result_def] >> metis_tac[exit_result_def]
QED

Theorem path_mem_edge_memory_length[local]:
  gas_path_mem_edge ctx fn s n (OK t) ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rw[gas_path_mem_edge_def] >> gvs[exit_result_def] >>
  imp_res_tac step_inst_memory_length >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  gvs[jump_to_def]
  >>~- ([`entered = _ with vs_vars := _`],
     qpat_x_assum `entered = _`
        (mp_tac o Q.AP_TERM `\u. u.vs_memory`) >> simp[]) >>
  metis_tac[step_inst_memory_length, exit_result_def]
QED

Theorem gas_path_mem_memory_length:
  gas_path_mem ctx fn s n (OK t) ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  qsuff_tac `!ctx fn s n r. gas_path_mem ctx fn s n r ==>
    !t. r = OK t ==> LENGTH s.vs_memory <= LENGTH t.vs_memory`
  >- metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      imp_res_tac path_mem_edge_memory_length >>
      metis_tac[LESS_EQ_TRANS]) >>
  simp[exit_result_def] >> metis_tac[exit_result_def]
QED

(* Code bytes and labels are immutable along the successful checked
   execution itself. *)
Theorem path_edge_code[local]:
  fragGasPath$gas_path_edge ctx fn s n (OK t) ==> t.vs_code = s.vs_code
Proof
  rw[fragGasPathTheory.gas_path_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >- metis_tac[venomInstProofsTheory.step_preserves_code]
  >- (drule_all venomExecProofsTheory.step_inst_ok_terminator_jump >> strip_tac >>
      gvs[step_inst_non_invoke,step_inst_base_opcode_eqs,jump_to_def,AllCaseEqs()] >>
      drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o Q.AP_TERM `\u. u.vs_code`) >> simp[])
  >- simp[jump_to_def] >>
  qpat_x_assum `OK _ = step_inst _ _ _ _`
    (fn th => fs[GSYM th, fragExecTheory.exit_result_def])
QED

Theorem path_edge_labels[local]:
  fragGasPath$gas_path_edge ctx fn s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  rw[fragGasPathTheory.gas_path_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >- metis_tac[venomInstProofsTheory.step_preserves_labels]
  >- (drule_all venomExecProofsTheory.step_inst_ok_terminator_jump >> strip_tac >>
      gvs[step_inst_non_invoke,step_inst_base_opcode_eqs,jump_to_def,AllCaseEqs()] >>
      drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o Q.AP_TERM `\u. u.vs_labels`) >> simp[])
  >- simp[jump_to_def] >>
  qpat_x_assum `OK _ = step_inst _ _ _ _`
    (fn th => fs[GSYM th, fragExecTheory.exit_result_def])
QED

Theorem gas_path_code_labels:
  !ctx fn s n r. fragGasPath$gas_path ctx fn s n r ==>
    !t. r = OK t ==> t.vs_code = s.vs_code /\ t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >> rpt conj_tac >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def] >>
  metis_tac[path_edge_code, path_edge_labels]
QED
