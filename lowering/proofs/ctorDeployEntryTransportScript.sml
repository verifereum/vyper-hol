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
  conj_tac
  >- (qexistsl [`ctxt0`, `rb`, `args_bytes`] >>
      fs[Abbr `es0`, Abbr `ctxt0`, Abbr `code0`,
         balance_bounded_def, all_accounts_def, returndata_bounded_def,
         opt_deploy_entry_state_def, opt_entry_state_def, DROP_LENGTH_APPEND,
         constructor_args_encode_def, value_transfer_ok_def,
         accounts_after_transfer_def, tx_block_fields_rel_def,
         loweringStateRelDefsTheory.tx_env_ok_def, layouts_agree_def] >>
      gvs[]) >>
  simp[deploy_entry_state_def, opt_deploy_entry_state_def, opt_entry_state_def,
       entry_venom_state_def, DROP_LENGTH_APPEND,
       Abbr `es0`, Abbr `ctxt0`, Abbr `code0`]
QED
