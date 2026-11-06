(* Source boundaries for counted pointer-safe storage append composition. *)
Theory appendStorageSourcePtr
Ancestors
  stmtSimAppendStorageCompose appendStorageRel vyperInterpreter vyperState
  vyperStorage vyperStorageBackend vyperValue
Libs
  monadsyntax

Theorem get_storage_gas_obs:
  get_storage cx (st with gas_obs := g) b = get_storage cx st b
Proof
  Cases_on `b` >> simp[get_storage_def]
QED

Theorem set_storage_gas_obs:
  set_storage cx (st with gas_obs := g) b x =
  set_storage cx st b x with gas_obs := g
Proof
  Cases_on `b` >> simp[set_storage_def]
QED

Theorem append_storage_place_gas_obs:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v st =
    (res, st') ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
    (st with gas_obs := g) = (res, st' with gas_obs := g)
Proof
  strip_tac >>
  qpat_x_assum `append_place _ _ _ _ = _` mp_tac >>
  simp[append_place_def, get_storage_backend_eq, bind_def, LET_THM,
       ignore_bind_def, check_def, assert_def, return_def, raise_def,
       write_storage_slot_eq, get_storage_gas_obs] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[get_storage_gas_obs, set_storage_gas_obs, raise_def, return_def])
QED

Theorem append_toplevel_place_any:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot tv), es) ==>
  !st. eval_target_place cx (TopLevelNameTarget nid) st =
         (INL (StoragePlace tr slot tv), st)
Proof
  PairCases_on `nid` >>
  `!st. eval_target_place cx (TopLevelNameTarget (nid0,nid1)) st =
        bind (lookup_global cx nid0 nid1) get_place st` by
    (gen_tac >> simp[Once evaluate_def] >>
     simp[Once evaluate_def, bind_def]) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  simp[bind_def, lookup_global_def, lift_option_type_def, return_def,
       raise_def, get_immutables_def, get_address_immutables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[get_place_def, return_def, raise_def, bind_def, LET_THM,
           get_immutables_def, get_address_immutables_def,
           lift_option_type_def])
QED

Theorem eval_append_storage_bind:
  (!st. eval_target_place cx (TopLevelNameTarget nid) st = (INL p, st)) ==>
  eval_stmt cx (Append (TopLevelNameTarget nid) e) =
    bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p)
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw, st1)` >>
  Cases_on `raw` >> simp[] >>
  Cases_on `read_result cx x' st1` >> rename1 `_ = (r2, st2)` >>
  Cases_on `r2` >> simp[]
QED
