(* Source-side boundaries for counted memory forcing. *)
Theory exprSimMemorySource
Ancestors
  exprSimDefs gasContext vyperInterpreter vyperState

Theorem forced_expr_admissible_raw:
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >>
  strip_tac >> first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def] >> Cases_on `res`
  >- (rename1 `eval_expr _ _ _ = (INL tv,ee)` >>
      Cases_on `tv` >> simp[expr_vv_res_ok_def] >>
      simp[read_result_def, raise_def, expr_res_ok_def]) >>
  simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem read_result_gas_obs:
  read_result cx tv ee = (INL v,ee) ==>
  !tail. read_result cx tv (ee with gas_obs := tail) =
    (INL v,ee with gas_obs := tail)
Proof
  Cases_on `tv`
  >- simp[read_result_def, return_def]
  >- (Cases_on `p`
      >- (Cases_on `b` >>
          simp[read_result_def, read_place_def, read_storage_slot_def,
               get_storage_backend_def, get_transient_storage_def,
               get_accounts_def, bind_def, lift_option_def, return_def, raise_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
      >- (simp[read_result_def, read_place_def, get_scopes_def, bind_def,
               lift_option_type_def, lift_sum_def, return_def, raise_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
      simp[read_result_def, read_place_def, get_immutables_def,
           get_address_immutables_def, bind_def, lift_option_type_def,
           lift_sum_def, return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def])) >>
  simp[read_result_def, raise_def]
QED
