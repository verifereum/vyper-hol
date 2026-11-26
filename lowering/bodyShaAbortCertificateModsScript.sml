(* The source failure and counted abort of the reached SHA256 suffix. *)
Theory bodyShaAbortCertificateMods
Ancestors
  bodyFullHashShaAbortOrigin bodyPtrHashBuiltinsShaSource
  exprSimDefs exprSimWordArgs fragExec vyperStorageFootprint

Theorem sha_abort_certificate_mods:
  storage_trace_domain cx st0 mid.storage_trace /\
  stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s /\
  builtin_result cx mid.accounts ann Sha256 tys [v] = INL w /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  insts = prefix ++ mk_inst id GAS [] [gv]::code /\
  isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) code /\
  (func.fn_name,id) NOTIN explicit /\
  run_inst_seq_mem_ok insts s /\
  (ctx_has_dalloca ctx ==>
    !pre i post u. insts = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
                   dalloca_no_wrap i u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn insts s Gf tf) /\
  run_inst_seq insts s = Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort) z ==>
  ?ef j.
    (!tail.
      (case builtin_result cx (mid with gas_obs := tail).accounts ann Sha256 tys [v] of
         INR exc => (INR exc,mid with gas_obs := tail)
       | INL w => (do precompile_call_success Sha256 [v]; return (Value w) od)
                    (mid with gas_obs := tail)) =
      (INR (Error (RuntimeError "precompile failed")),ef with gas_obs := tail)) /\
    storage_trace_domain cx st0 ef.storage_trace /\
    !H. valid_horizon cx st0 H ef.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F]
        (Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
           (z with vs_inst_idx := j),Gf,tf) /\
      exit_result (Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
        (z with vs_inst_idx := j)) /\
      expr_exit (INR (Error (RuntimeError "precompile failed")))
        (Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
           (z with vs_inst_idx := j)) /\
      halt_exit H cx (ef with gas_obs := []) (INR (Error (RuntimeError "precompile failed")))
        (Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
           (z with vs_inst_idx := j)) /\
      (ctx_has_dalloca ctx ==>
        !t. Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
              (z with vs_inst_idx := j) = Halt t ==> allocas_below_fmp t)
Proof
  strip_tac >>
  qpat_x_assum `insts = _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac sha_setup_gas_origin_abort_uniform >>
  qabbrev_tac `start = mid with gas_obs := []` >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx start s /\
   start.gas_obs = [] /\ builtin_result cx start.accounts ann Sha256 tys [v] = INL w` by
    simp[Abbr `start`] >>
  drule_all_then strip_assume_tac hash_sha256_source_failure >>
  qexistsl_tac [`ef`,`j`] >>
  conj_tac
  >- (`!tail. (start with gas_obs := tail) = mid with gas_obs := tail` by
        simp[Abbr `start`, vyperStateTheory.evaluation_state_component_equality] >>
      qpat_x_assum `!tail. _ = (INR _,ef with gas_obs := tail)` mp_tac >>
      asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ef.storage_trace <=>
       valid_horizon cx st0 H mid.storage_trace` by
    (Cases_on `s.vs_outcomes` >> gvs[Abbr `start`]) >>
  conj_tac
  >- (Cases_on `s.vs_outcomes` >> gvs[storage_trace_domain_def, Abbr `start`]) >>
  simp[expr_exit_def, halt_exit_def, exit_result_def]
QED
