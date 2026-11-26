(* The linked nonstatic, nonoverflowing SELFDESTRUCT terminal branch. *)
Theory bodySelfDestructHaltMods
Ancestors
  gasOutcomeFullMods gasSummary selfdestructHalt fragGasOriginPtr fragExec
  exprSimDefs loweringStateRelDefs venomExecSemantics venomInst venomState
  vyperInterpreter vyperState vyperStorageFootprint bodyPtrDefs ptrDiscipline words

Theorem selfdestruct_halt_outcome_mods:
  !DF lo explicit ctx func PG cenv cx st0 source es s0 G0 tn0 marks
    v ee t G tn op id aw r Q.
    (!tail. source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      state_rel H func cenv cx (ee with gas_obs := []) t /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G,tn) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G,tn) [] (r,G,tn)) /\
    dest_AddressV v = SOME (w2w aw) /\
    ~cx.txn.is_static /\
    ~selfdestruct_overflows cx (w2w aw) ee.accounts /\
    t.vs_call_ctx.cc_address = cx.txn.target /\
    t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
    ~t.vs_call_ctx.cc_static /\
    eval_operand op t = SOME aw /\
    step_inst_base (mk_inst id SELFDESTRUCT [op] []) t = r /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
      (bind (bind source (selfdestruct_tail cx)) (read_result cx))
      (es,s0,G0,tn0) Q
      (\H res ee' gt r'. expr_exit res r' /\ halt_exit H cx ee' res r' /\
        (ctx_has_dalloca ctx ==> !s. r' = Halt s ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ?u. r = Halt u /\ u.vs_returndata = [] /\
         halt_rel H cx (selfdestruct_final cx (w2w aw) (ee with gas_obs := [])) u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` drule >> strip_tac >>
     qpat_x_assum `step_inst_base _ _ = r` (SUBST1_TAC o SYM) >>
     irule step_selfdestruct_halt_rel >> simp[] >>
     irule halt_rel_from_state_rel >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?u. _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (disch_tac >>
     `allocas_below_fmp t` by simp[] >>
     qpat_x_assum `step_inst_base _ t = Halt u` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def, LET_THM] >>
     disch_then (SUBST1_TAC o SYM) >>
     fs[allocas_below_fmp_def, halt_state_def, set_returndata_def] >>
     first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists `marks` >> disj2_tac >> disj1_tac >>
  qexistsl [`INR HaltException`, `selfdestruct_final cx (w2w aw) ee`,
            `Halt u`, `G`, `tn`] >>
  conj_tac
  >- (gen_tac >> once_rewrite_tac[bind_assoc] >>
      pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >>
      `selfdestruct_tail cx v (ee with gas_obs := tail) =
       (INR HaltException : eval_result + exception,
        selfdestruct_final cx (w2w aw) (ee with gas_obs := tail))` by
        (irule selfdestruct_tail_halt >> simp[]) >>
      simp[bind_def, selfdestruct_final_fields]) >>
  conj_tac >- simp[selfdestruct_final_def] >>
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by fs[selfdestruct_final_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _` drule >>
  strip_tac >> reverse conj_tac
  >- (simp[exit_result_def, expr_exit_def, halt_exit_def] >>
      first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `gas_origin_ptr_path _ _ marks (OK t,G,tn)`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED
