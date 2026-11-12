(* Counted source certificates for any pure storage-place prefix. *)
Theory augAssignPtrStoragePlaceCertificates
Ancestors
  augAssignPtrStoragePlaceSource augAssignPtrStorageCommon
  gasExemptCert fragGasMode fragGasPath vyperLookup
  bodyPtrDefs gasSummaryComposePtr gasSummary gasCount gasContext
  fragGasPathPtr vyperInterpreter vyperState

Theorem augassign_storage_place_exception_exec_ptr:
  (!gs. eval_target_place cx tgt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tv),es with gas_obs := gs)) /\
  read_storage_slot cx tr slot tv es = (INL cur,es) /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INR ex) ee J un r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty tgt bop e))
    (es,s0,G,tn) marks (INR ex) ee J un r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >>
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_storage_place_exception_ptr >> simp[] >>
  qexists_tac `cur` >> metis_tac[read_storage_slot_gas_obs_ptr]
QED

Theorem augassign_storage_place_normal_exec_ptr:
  (!gs. eval_target_place cx tgt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tv),es with gas_obs := gs)) /\
  read_storage_slot cx tr slot tv es = (INL cur,es) /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INL v) ee J un (OK u) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (write_storage_slot cx tr slot tv))
    (ee with gas_obs := [],u,J,un) [] res fin Hfin uk r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty tgt bop e))
    (es,s0,G,tn) marks res fin Hfin uk r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_ptr_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `read_storage_slot cx tr slot tv
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL cur,es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` by
        metis_tac[read_storage_slot_gas_obs_ptr] >>
      `eval_target_place cx tgt
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL (StoragePlace tr slot tv),
          es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` by simp[] >>
      drule_all augassign_storage_place_normal_ptr >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem augassign_storage_place_exempt_ptr:
  read_storage_slot cx tr slot tvt es = (INL v0,es) /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_target_place cx tgt)
    (es,s0,G,tn) [] (INL (StoragePlace tr slot tvt)) es H tm (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  `ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()) =
   bind (eval_target_place cx tgt) (\p.
     bind (read_place cx p) (\cur.
     bind (place_type_value cx p) (\ptv.
     bind (bind (eval_expr cx e) (read_result cx)) (\v.
     bind (lift_sum (evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ptv bop cur v)) (\r. ignore_bind (write_place cx p r) (return ()))))))` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  `gas_marked_exec F (ctx,func) (read_place cx (StoragePlace tr slot tvt))
     (es with gas_obs := [],t) [] (INL v0)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> simp[read_place_def] >>
         metis_tac[read_storage_slot_gas_obs_ptr]) >>
     simp[gas_marked_path_def, gas_path_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED
