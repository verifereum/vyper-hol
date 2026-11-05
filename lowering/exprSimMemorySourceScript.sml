(* Source-side boundaries for counted memory forcing. *)
Theory exprSimMemorySource
Ancestors
  loweringPosts
  exprSimDefs gasContext vyperInterpreter vyperState gasExemptCert
  gasSummaryCompose exprSimUnwrapProps

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

Theorem force_ignore_bind_action:
  ignore_bind (bind a (read_result cx)) (return ()) =
  bind a (\tv. ignore_bind (read_result cx tv) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >>
  gen_tac >> Cases_on `a x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem force_exempt_cert:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind a (return ())) (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind a (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  rewrite_tac[force_ignore_bind_action] >> strip_tac >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem buffer_memory_marked_read:
  gas_marked_exec memory (ctx,func) a (es,s0) marks (INL tv) ee (OK s) /\
  vv_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) tv
    (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ ~is_word_type t ==>
  ?v. gas_marked_exec memory (ctx,func) (bind a (read_result cx))
        (es,s0) marks (INL v) (ee with gas_obs := []) (OK s) /\
      expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := [])
        v p.ptr_operand s
Proof
  rpt strip_tac >>
  `?v. read_result cx tv (ee with gas_obs := []) =
       (INL v,ee with gas_obs := [])` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def] >>
     metis_tac[]) >>
  qexists_tac `v` >> conj_tac
  >- (drule read_result_gas_obs >> strip_tac >>
      gvs[gasSummaryTheory.gas_marked_exec_def, bind_def]) >>
  irule expr_post_of_vv_post_memory >> simp[] >>
  drule vv_post_read_result >> metis_tac[]
QED
