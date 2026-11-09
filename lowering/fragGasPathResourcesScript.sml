(* Allocation history at the actual endpoint of counted memory paths. *)
Theory fragGasPathResources
Ancestors
  bodyMemAggregatePath allocaHistory fragGasPathMem venomMemDefs
  venomExecProofs venomState fragExec

Theorem gas_path_mem_edge_history[local]:
  gas_path_mem_edge ctx fn s g (OK t) /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s ==> alloca_history fn t
Proof
  rw[gas_path_mem_edge_def] >> gvs[exit_result_def]
  >>~- ([`~is_terminator inst.inst_opcode`], metis_tac[alloca_history_step])
  >>~- ([`eval_phis _ _ = OK _`],
    drule_all alloca_history_step >> simp[] >> strip_tac >>
    drule_all history_phi_entry >> simp[])
  >>~- ([`jump_to lbl s`],
    irule alloca_history_jump >> simp[jump_to_def] >> qexists `s` >> simp[]) >>
  metis_tac[exit_result_def]
QED

Theorem gas_path_mem_history:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  gas_path_mem ctx fn s g (OK t) ==> alloca_history fn t /\ alloca_inv t
Proof
  `!ctx fn s g result. gas_path_mem ctx fn s g result ==>
     !t. result = OK t ==> fn_inst_ids_distinct fn /\
       alloca_history fn s /\ alloca_inv s ==>
       alloca_history fn t /\ alloca_inv t`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[gas_path_mem_edge_history, aggregate_mem_edge_alloca_inv,
    exit_result_def]
QED
