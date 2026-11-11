(* The projections consulted by a captured source read, not whole-state equality. *)
Theory exprExtRequestReadProbe
Ancestors
  vyperState vyperMisc

Definition extrequest_read_frame_def:
  extrequest_read_frame cx es ee <=>
    es.scopes = ee.scopes /\
    (lookup_account cx.txn.target es.accounts).storage =
      (lookup_account cx.txn.target ee.accounts).storage /\
    vfmExecution$lookup_transient_storage cx.txn.target es.tStorage =
      vfmExecution$lookup_transient_storage cx.txn.target ee.tStorage /\
    ALOOKUP es.immutables cx.txn.target = ALOOKUP ee.immutables cx.txn.target
End

Theorem extrequest_read_result_frame:
  extrequest_read_frame cx es ee ==>
  read_result cx result ee = (FST (read_result cx result es), ee)
Proof
  strip_tac >> Cases_on `result`
  >- simp[read_result_def, return_def]
  >- (Cases_on `p`
      >- (Cases_on `b` >>
          gvs[extrequest_read_frame_def, read_result_def, read_place_def,
              read_storage_slot_def, get_storage_backend_def,
              get_transient_storage_def, get_accounts_def, bind_def,
              lift_option_def, return_def, raise_def, option_CASE_rator, sum_CASE_rator] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
      >- (gvs[extrequest_read_frame_def, read_result_def, read_place_def,
              get_scopes_def, bind_def, lift_option_type_def, lift_sum_def,
              return_def, raise_def, option_CASE_rator, sum_CASE_rator] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
      gvs[extrequest_read_frame_def, read_result_def, read_place_def,
          get_immutables_def, get_address_immutables_def, bind_def,
          lift_option_type_def, lift_sum_def, return_def, raise_def, option_CASE_rator, sum_CASE_rator] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def])) >>
  simp[read_result_def, raise_def]
QED
