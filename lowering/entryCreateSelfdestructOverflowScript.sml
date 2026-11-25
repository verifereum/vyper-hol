(* A recipient overflow stops at the selected operand exit.  The
   exemption is for the enclosing Call, with no SELFDESTRUCT step. *)
Theory entryCreateSelfdestructOverflow
Ancestors
  gasExemptCert gasExemptOrigin gasNormalPrefix fragGasOriginPtr
  exprLoweringProps vyperStorageFootprint vyperInterpreter vyperState

Theorem selfdestruct_boundary_exemption:
  compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) /\
  fn_has_code sa sb func /\
  gas_value_prefix H T (ctx,func,cenv,cx) (expr_type e,e)
    (sa,sm,op) (es,s) marks (v,ee,t) /\
  dest_AddressV v = SOME address /\ ~cx.txn.is_static /\
  selfdestruct_overflows cx address ee.accounts /\
  (storage_trace_domain cx st0 es.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace) /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,G1,tn1) ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_expr cx (Call ann SelfDestructTarget [e] dflt)) (return ()))
    (es,s) marks (RuntimeError "transfer_value recipient overflow",ee) (func,t) /\
  ?H'. (storage_trace_domain cx st0 es.storage_trace ==>
         valid_horizon cx st0 H' es.storage_trace) /\
       gas_origin_ptr_focus (DF H',lo,explicit,ctx,func,PG)
         (s,G,tn) marks (func,PG,G1,tn1,t)
Proof
  strip_tac >> conj_tac
  >- (irule gas_exempt_cert_origin >>
      rewrite_tac[gas_exempt_origin_def] >> disj2_tac >>
      qexistsl [`H`,`cenv`,`cx`,`ty`,`ann`,`e`,`dflt`,
                `sa`,`sb`,`sm`,`vv`,`op`,`v`,`address`] >> simp[]) >>
  qexists `H` >> simp[] >>
  irule (cj 1 gas_origin_ptr_focus_rules) >> first_assum ACCEPT_TAC
QED
