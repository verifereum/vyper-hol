(* Resolve any pure AugAssign target, then share its compiled prefix with
   the RHS/operator/write outcome. Storage observations may be appended. *)
Theory augAssignFullSourcePrefix
Ancestors
  gasOutcomeFullSourcePrefix gasOutcomeFull gasExemptPurePrefix
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathMem fragExec
  gasExemptCert gasSummary gasStorage
  vyperStorageFootprint vyperStorageTrace vyperInterpreter vyperState
  venomState list
Libs
  monadsyntax

Theorem augassign_pure_prefix_full:
  (!gs.
     eval_target_place cx tgt (es with gas_obs := gs) =
       (INL p,mid with gas_obs := gs) /\
     read_place cx p (mid with gas_obs := gs) =
       (INL cur,mid with gas_obs := gs) /\
     place_type_value cx p (mid with gas_obs := gs) =
       (INL ptv,mid with gas_obs := gs)) /\
  mid.storage_trace = es.storage_trace ++ obs /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (s0,G0,tn0) [] (OK s1,G1,tn1)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p)))
    (mid,s1,G1,tn1) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (AugAssign ty tgt bop e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ m _ _ _` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `~s1.vs_halted` by
    (drule gas_path_mem_exec >> simp[exit_result_def]) >>
  `!gs. eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
        m (mid with gas_obs := gs)` by
    (gen_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def, Abbr `m`] >>
     Cases_on `eval_expr cx e (mid with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[bind_def]) >>
  irule gas_outcome_full_source_prefix >>
  qpat_assum `gas_outcome_full _ _ _ _ m _ _ _` (irule_at Any) >>
  qpat_assum `mid.storage_trace = _` (irule_at Any) >> rpt conj_tac
  >~ [`storage_trace_frame m`]
  >- (qunabbrev_tac `m` >> irule storage_trace_frame_bind_all >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_lifts, storage_trace_frame_write_place]) >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >>
      `gas_exempt_cert T tops (ctx,func) (ignore_bind m (return ()))
        (mid with gas_obs := [],s1) marks (err,ee) (leaf,fin)` by
        (drule gas_exempt_cert_start_gas_obs >>
         disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
      `ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()) =
       do p <- eval_target_place cx tgt;
          cur <- read_place cx p;
          ptv <- place_type_value cx p;
          rhs <- bind (eval_expr cx e) (read_result cx);
          r <- lift_sum (evaluate_binop
            (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
            ptv bop cur rhs);
          ignore_bind (write_place cx p r) (return ()) od` by
        simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
      pop_assum SUBST1_TAC >>
      `gas_marked_exec T (ctx,func) (eval_target_place cx tgt)
        (es,s0) [] (INL p) (mid with gas_obs := []) (OK s1)` by
        simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
      BETA_TAC >>
      irule (Q.INST [`v` |-> `cur`] gas_exempt_cert_pure_prefix) >> simp[] >>
      BETA_TAC >>
      irule (Q.INST [`v` |-> `ptv`] gas_exempt_cert_pure_prefix) >>
      fs[Abbr `m`, ignore_bind_def, bind_assoc]) >>
  first_assum ACCEPT_TAC
QED
