(* Pointwise linked outcome at a reached bytestring Convert operand. *)
Theory bodyConvertBytesSuffixMods
Ancestors
  gasOutcomeFullPostMods exprSimDefs haltExitProj vyperStorageFootprint
  fragExec fragGasOriginPtr compileEnv vyperInterpreter vyperState venomState

Theorem bytes_convert_suffix_continuation_mods:
  ~t.vs_halted /\ mid.gas_obs = [] /\
  (valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace ==>
   ((?vout q Gf tnf. convert_result cx (expr_type e) dst v = INL vout /\
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
              (t,G,tn) [] (OK q,Gf,tnf)) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
            V H (INL (Value vout)) mid Gf tnf q)) \/
    (?msg q Gf tnf. convert_result cx (expr_type e) dst v = INR (Error (RuntimeError msg)) /\
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
              (t,G,tn) [] (Abort Revert_abort q,Gf,tnf))))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (\ee. (sum_CASE (convert_result cx (expr_type e) dst v) (\w. INL (Value w)) INR,ee))
    (mid,t,G,tn) V
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 mid.storage_trace`
  >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[storage_trace_domain_def] >>
      `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
      qpat_x_assum `valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac)
      >- (irule gas_outcome_full_mods_pure >> simp[] >>
          qexistsl_tac [`Gf`,`mid`,`INL (Value vout)`,`q`,`tnf`] >> simp[]) >>
      irule gas_outcome_full_mods_exit_revert >> simp[] >>
      qexistsl_tac [`Gf`,`mid`,`INR (Error (RuntimeError msg))`,`tnf`,`q`] >>
      simp[exit_result_def,expr_exit_def,halt_exit_not_halt]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[]
QED
