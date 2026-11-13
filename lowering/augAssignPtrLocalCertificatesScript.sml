(* Source certificate transport, independent of local store pointer safety. *)
Theory augAssignPtrLocalCertificates
Ancestors augAssignPtrStorageCommon
  augAssignPtrLocalSource augAssignPtrStorageSource stmtSimAugAssign stmtSimAssignSource
  bodyPtrDefs gasSummaryComposePtr gasSummaryCompose gasOutcome
  gasSummary gasCount gasContext gasExemptCert fragGasMode fragGasPath fragGasPathPtr
  vyperInterpreter vyperLookup vyperState
Libs monadsyntax

Theorem augassign_rhs_exception_exec_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INR ex) ee J un r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (es,s0,G,tn) marks (INR ex) ee J un r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >>
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_rhs_exception_ptr >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem augassign_rhs_normal_exec_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INL v) ee J un (OK u) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      entry.type bop entry.value v)) (write_place cx (MemoryPlace id [])))
    (ee with gas_obs := [],u,J,un) [] res fin Hfin uk r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (es,s0,G,tn) marks res fin Hfin uk r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_ptr_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `lookup_scopes id (es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail).scopes = SOME entry` by simp[] >>
      drule_all augassign_rhs_normal_ptr >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem augassign_rhs_exempt_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_target_place cx (NameTarget id))
    (es,s0,G,tn) [] (INL (MemoryPlace id [])) es H tm (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  `ignore_bind (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) (return ()) =
   do p <- eval_target_place cx (NameTarget id);
      cur <- read_place cx p;
      ptv <- place_type_value cx p;
      v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur v);
      ignore_bind (write_place cx p r) (return ()) od` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  `gas_marked_exec F (ctx,func) (read_place cx (MemoryPlace id []))
     (es with gas_obs := [],t) [] (INL entry.value)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> irule (cj 2 eval_target_place_local) >> simp[]) >>
     simp[gas_marked_path_def, gas_path_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[lift_option_type_def, subscripts_type_def, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem augassign_store_continuation_exec_ptr:
  br = INL w /\
  write_place cx (MemoryPlace id []) w ee = (INL (),fin) /\
  gas_path_ptr D 0 ctx func PG G tn u 0 H tm r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum br) (write_place cx (MemoryPlace id [])))
    (ee,u,G,tn) [] (INL ()) fin H tm r
Proof
  strip_tac >> drule stmtSimAssignSourceTheory.write_place_local_success_gas_obs >>
  strip_tac >> simp[gas_marked_exec_ptr_def, lift_sum_def, bind_def, return_def]
QED

Theorem augassign_error_continuation_exec_ptr:
  br = INR err /\ gas_path_ptr D 0 ctx func PG G tn u 0 H tm r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum br) (write_place cx (MemoryPlace id [])))
    (ee,u,G,tn) [] (INR (Error err)) ee H tm r
Proof
  simp[gas_marked_exec_ptr_def, lift_sum_def, bind_def, raise_def]
QED
