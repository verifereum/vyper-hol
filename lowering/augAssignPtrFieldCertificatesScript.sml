(* Counted source certificate transport for local field updates. *)
Theory augAssignPtrFieldCertificates
Ancestors
  augAssignPtrFieldSource augAssignPtrLocalCertificates augAssignPtrStorageSource
  bodyPtrDefs gasSummaryComposePtr gasSummaryCompose gasOutcome
  gasSummary gasCount gasContext gasExemptCert fragGasMode fragGasPath fragGasPathPtr
  vyperInterpreter vyperLookup vyperState
Libs monadsyntax

Theorem augassign_attr_rhs_exception_exec_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INR ex) ee J un r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (es,s0,G,tn) marks (INR ex) ee J un r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >>
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_attr_rhs_exception_ptr >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem augassign_attr_rhs_normal_exec_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INL v) ee J un (OK u) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v)) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u,J,un) [] res fin Hfin uk r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (es,s0,G,tn) marks res fin Hfin uk r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_ptr_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `lookup_scopes id (es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail).scopes = SOME entry` by simp[] >>
      drule_all augassign_attr_rhs_normal_ptr >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem augassign_attr_rhs_exempt_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_target_place cx (AttributeTarget (NameTarget id) fld))
    (es,s0,G,tn) [] (INL (MemoryPlace id [AttrSubscript fld])) es H tm (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (eval_stmt cx
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  rewrite_tac[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  simp[bind_assoc] >>
  rewrite_tac[read_place_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[bind_return, lift_option_type_def, read_memory_path_def,
       evaluate_subscripts_def, lift_sum_def] >>
  rewrite_tac[place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[bind_return, lift_option_type_def, subscripts_type_def,
       subscript_type_def, lift_sum_def] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Theorem augassign_attr_store_continuation_exec_ptr:
  br = INL w /\
  gas_marked_exec_ptr D (ctx,func) PG
    (write_place cx (MemoryPlace id [AttrSubscript fld]) w)
    (ee with gas_obs := [],u,G,tn) [] res fin H tm r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum br) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u,G,tn) [] res fin H tm r
Proof
  strip_tac >> gvs[gas_marked_exec_ptr_def, bind_def, lift_sum_def, return_def]
QED

Theorem augassign_attr_error_continuation_exec_ptr:
  br = INR err /\ gas_path_ptr D 0 ctx func PG G tn u 0 H tm r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum br) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee,u,G,tn) [] (INR (Error err)) ee H tm r
Proof
  simp[gas_marked_exec_ptr_def, bind_def, lift_sum_def, raise_def]
QED
