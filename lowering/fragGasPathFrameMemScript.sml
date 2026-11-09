(* Allocation-history transport for counted memory paths, including raw jumps. *)
Theory fragGasPathFrameMem
Ancestors
  fragGasPathMem allocaHistory venomExecProofs venomExecSemantics
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
