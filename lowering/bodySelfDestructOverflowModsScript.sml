(* The exempt error is witnessed at the reached address operand, before
   executing the target's selfdestruct instruction. *)
Theory bodySelfDestructOverflowMods
Ancestors
  gasOutcomeFullMods gasExemptCertMods gasExemptOriginMods gasNormalPrefix
  fragGasOriginPtr selfdestructHalt exprLowering vyperStorageFootprint
  vyperInterpreter vyperState

Theorem selfdestruct_overflow_outcome_mods:
  !DF lo explicit ctx func PG cenv cx st0 es s0 G0 tn0
    H ann e dflt ty sa sb sc vv op marks v ee t G tn a Q R.
    compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) /\
    fn_has_code sa sb func /\
    gas_value_prefix H T (ctx,func,cenv,cx) (expr_type e,e)
      (sa,sc,op) (es,s0) marks (v,ee,t) /\
    (storage_trace_domain cx st0 es.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G,tn) /\
    dest_AddressV v = SOME a /\ ~cx.txn.is_static /\
    selfdestruct_overflows cx a ee.accounts ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG)
      cenv.ce_modules cx st0
      (bind (eval_expr cx (Call ann SelfDestructTarget [e] dflt))
        (read_result cx)) (es,s0,G0,tn0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists `marks` >> disj2_tac >> disj2_tac >>
  qexistsl [`RuntimeError "transfer_value recipient overflow"`,
            `ee`, `func`, `PG`, `G`, `tn`, `t`] >>
  conj_tac
  >- (rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_mods_error_result >>
      irule gas_exempt_cert_mods_origin >>
      rewrite_tac[gas_exempt_origin_mods_def] >> disj2_tac >>
      qexistsl [`H`, `cenv`, `cx`, `ty`, `ann`, `e`, `dflt`,
                `sa`, `sb`, `sc`, `vv`, `op`, `v`, `a`] >> simp[]) >>
  qexists `H` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (cj 1 gas_origin_ptr_focus_rules) >> first_assum ACCEPT_TAC
QED
