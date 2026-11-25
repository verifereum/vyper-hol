(* Identify the external code at the reached address landing. *)
Theory bodySliceExternalLaunchMods
Ancestors
  exprSimSliceExtcode exprSimSliceExtcodeContinue exprSimHypsDefs
  bodyFullHashKeccakFixed stateRelProj accountsRelProps exprLoweringProps
  vyperStorageFootprint vyperState words
Libs monadsyntax

Theorem slice_external_launch_mods:
  LENGTH bs = 20 /\
  eval_operand aop z = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  expr_sim_inv_mods mods cenv cx env ae /\
  storage_trace_domain cx st0 ae.storage_trace /\
  (!H. valid_horizon cx st0 H ae.storage_trace ==> stmt_state_rel H ctx func cenv cx ae z) /\
  i < dimword (:256) /\ k < dimword (:256) ==>
  let code = (lookup_account (word_of_bytes_be bs) ae.accounts).code in
    LENGTH code < dimword (:256) /\
    step_inst_base (mk_inst s3.cs_next_id EXTCODESIZE [aop]
      [STRING #"%" (toString s3.cs_next_var)]) z =
    OK (update_var (STRING #"%" (toString s3.cs_next_var)) (n2w (LENGTH code)) z) /\
    (!v wd. i+k <= LENGTH code /\
      v.vs_accounts = z.vs_accounts /\ v.vs_call_ctx = z.vs_call_ctx /\
      v.vs_code = z.vs_code /\ eval_operand dst v = SOME wd /\
      eval_operand x v = SOME (n2w i) /\ eval_operand y v = SOME (n2w k) /\
      (EXTCODECOPY = EXTCODECOPY ==> eval_operand aop v = eval_operand aop z) ==>
      step_inst_base (mk_inst se.cs_next_id EXTCODECOPY [aop;dst;x;y] []) v =
      OK (write_memory_with_expansion (w2n wd) (TAKE k (DROP i code)) v)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z /\
      z.vs_alloca_next + pending_alloca_size func z <= w2n z.vs_initial_fmp) /\
    (!tail.
      (do code_acc <- get_accounts;
          code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type addr] [BytesV bs]);
          slice_acc <- get_accounts;
          v <- lift_sum (evaluate_builtin cx slice_acc ann (Slice n)
            (MAP expr_type [Builtin ct (Acc Code) [addr];start;len]) [code_v;IntV (&i);IntV (&k)]);
          return (Value v) od) (ae with gas_obs := tail) =
      ((case evaluate_slice (BytesV code) (IntV (&i)) (IntV (&k)) n of
          INL v => INL (Value v) | INR err => INR (Error err)),
       ae with gas_obs := tail))
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `valid_horizon cx st0 (storage_trace_horizon ae.storage_trace) ae.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_then assume_tac stmt_state_rel_state_rel >>
  drule_then strip_assume_tac state_rel_accounts >>
  `accounts_well_typed ae.accounts` by fs[expr_sim_inv_mods_def] >>
  drule_all_then strip_assume_tac slice_extcode_account >>
  conj_tac
  >- (simp[dimword_def] >> decide_tac) >>
  conj_tac
  >- (drule slice_extcodesize_step >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `eval_operand aop v = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))` by fs[] >>
      `w2n (n2w i : bytes32) + w2n (n2w k : bytes32) <=
         LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
           v.vs_accounts).code` by simp[w2n_n2w] >>
      qpat_assum `eval_operand dst v = SOME wd`
        (mp_then (Pos (el 2)) mp_tac slice_extcodecopy_step) >>
      disch_then (drule_all_then (qspec_then `se.cs_next_id` mp_tac)) >>
      simp[w2n_n2w]) >>
  conj_tac
  >- (strip_tac >>
      drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
      drule stmt_state_rel_fmp_room >>
      simp[fmp_room_def] >> decide_tac) >>
  gen_tac >>
  rewrite_tac[slice_extcode_source_tail] >>
  Cases_on `evaluate_slice (BytesV (lookup_account (word_of_bytes_be bs) ae.accounts).code)
    (IntV (&i)) (IntV (&k)) n` >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, raise_def]
QED
