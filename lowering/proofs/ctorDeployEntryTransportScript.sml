(* Reconstruct a creation frame for the unoptimized deployment program. *)
Theory ctorDeployEntryTransport
Ancestors
  ctorDeployDefs e2eDeployDefs e2eDefs e2eEntry vfmExecutionProp vfmTotalBalance
  vfmReturndataBound list rich_list

Theorem deploy_reconstructed_entry:
  !tops prog prog' cplan am tx es.
    deploy_state_rel tops (assemble prog') am tx es ==>
    ?es0.
      deploy_state_rel tops (assemble prog) am
        (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)
        es0 /\
      deploy_entry_state prog cplan tops es0 =
        (opt_deploy_entry_state prog prog' cplan tops es with
           <|vs_gas_readings := gas_readings es0;
             vs_outcomes := MAP SND (call_trace es0)|>)
Proof
  rpt gen_tac >> simp[deploy_state_rel_def] >> strip_tac >>
  qabbrev_tac `code0 = assemble prog ++ args_bytes` >>
  qabbrev_tac `ctxt0 = ctxt with msgParams :=
    (ctxt.msgParams with <|code := code0;
                          parsed := parse_code 0 FEMPTY code0|>)` >>
  qabbrev_tac `es0 = es with contexts := [(ctxt0,rb)]` >>
  qexists_tac `es0` >>
  `wf_state es0` by
    (qpat_x_assum `wf_state es` mp_tac >>
     simp[wf_state_def, wf_context_def, all_accounts_def,
          stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def,
          outputTo_consistent_ctx_def, Abbr `es0`, Abbr `ctxt0`]) >>
  `(opt_deploy_entry_state prog prog' cplan tops es).vs_code = code0` by
    simp[opt_deploy_entry_state_def, opt_entry_state_def,
         DROP_LENGTH_APPEND, Abbr `code0`] >>
  conj_tac
  >- (qexistsl [`ctxt0`, `rb`, `args_bytes`] >>
      simp[Abbr `es0`, Abbr `ctxt0`, Abbr `code0`] >>
      rpt conj_tac
      >- (qpat_x_assum `balance_bounded _ es` mp_tac >>
          simp[balance_bounded_def, all_accounts_def])
      >- (qpat_x_assum `constructor_args_encode tops tx args_bytes` mp_tac >>
          simp[constructor_args_encode_def])
      >- (qpat_x_assum `value_transfer_ok tx am.accounts` mp_tac >>
          simp[value_transfer_ok_def])
      >- (qpat_x_assum `es.rollback.accounts = accounts_after_transfer tx _`
            mp_tac >> simp[accounts_after_transfer_def])
      >- (qpat_x_assum `tx_block_fields_rel tx es.txParams` mp_tac >>
          simp[tx_block_fields_rel_def, loweringStateRelDefsTheory.tx_env_ok_def] >>
          strip_tac >>
          qpat_x_assum `tx.block_hashes = TAKE 256 es.txParams.prevHashes`
            (fn th => simp[GSYM th]))
      >- (qpat_x_assum `layouts_agree tops am tx` mp_tac >>
          simp[layouts_agree_def])) >>
  simp[deploy_entry_state_def, opt_deploy_entry_state_def, opt_entry_state_def,
       entry_venom_state_def, DROP_LENGTH_APPEND,
       Abbr `es0`, Abbr `ctxt0`, Abbr `code0`]
QED
