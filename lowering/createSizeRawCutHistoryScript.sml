(* Allocation history follows the actual caller edges, independently of marks. *)
Theory createSizeRawCutHistory
Ancestors
  fragGasOrigin fragExec allocaHistory venomExecProofs venomMemDefs
  venomMemProofs venomState relation

Theorem create_raw_ok_edge_alloca_history[local]:
  gas_origin_edge F explicit ctx func s ms (OK t) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  alloca_history func t /\ alloca_inv t
Proof
  strip_tac >> qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  simp[gas_origin_edge_def] >> strip_tac >> gvs[exit_result_def]
  >~ [`OK _ = step_inst _ _ _ _`]
  >- (qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
      gvs[exit_result_def]) >>
  drule_all alloca_history_step >> simp[] >> strip_tac >>
  drule_all alloca_inv_step_inst_proof >> strip_tac
  >>~- ([`alloca_history func (_ with vs_inst_idx := phi_prefix_length _)`],
    drule_all history_phi_entry >> strip_tac >>
    drule eval_phis_preserves_alloca_fields >> strip_tac >>
    gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
    metis_tac[]) >>
  metis_tac[alloca_inv_set_inst_idx]
QED

Theorem create_raw_ok_rtc_alloca_history:
  fn_inst_ids_distinct func /\ alloca_history func u /\ alloca_inv u /\
  RTC (\x y. ?ms. gas_origin_edge F explicit ctx func x ms (OK y)) u r ==>
  alloca_history func r
Proof
  `!x y. RTC (\x y. ?ms. gas_origin_edge F explicit ctx func x ms (OK y)) x y ==>
         fn_inst_ids_distinct func /\ alloca_history func x /\ alloca_inv x ==>
         alloca_history func y /\ alloca_inv y` suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  rpt strip_tac >> metis_tac[create_raw_ok_edge_alloca_history]
QED
