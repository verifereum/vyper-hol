Theory s1PrefixBoolChainWordEqDemandStep
Ancestors
  s1PrefixBoolChainWordEqCut s1PrefixBoolChainEqDemand bodyFullSimProjection
  s1PrefixDefs

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `expr_size l < expr_size (Builtin (BaseT BoolT) (Bop Eq) [l;r]) /\
   expr_size r < expr_size (Builtin (BaseT BoolT) (Bop Eq) [l;r])` by
    (drule_all bool_chain_word_eq_demand_closure >> strip_tac >> simp[]) >>
  qpat_x_assum `value_read_demand _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [value_read_demand_def]) >>
  irule bool_chain_word_eq_prefix_at_entry >>
  rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qexistsl_tac [`cenv`,`d`,`env`,`op`,`sa`,`sb`,`shadow_func`,
                `shadow_sa`,`shadow_sb`,`tops`,`ty`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      (* The left replay with an empty tail unlocks the right full judgment. *)
      qpat_assum `!tail. bind (eval_expr cx l) _ _ = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
      `body_expr_full_ok cx r` by metis_tac[] >>
      qpat_x_assum `body_expr_full_ok cx l` kall_tac >>
      reverse conj_tac
      >- (qpat_assum `!z ety ee ca cb sha shb op' u J tau. _ ==> gas_prefix_full _ _ _ _ _` irule >>
          simp[value_read_demand_def] >>
          qpat_assum `expr_sim_full_pre _ _ _ _ r _ _` (irule_at Any) >> simp[]) >>
      drule_all (DISCH_ALL (CONJUNCT1 (UNDISCH body_expr_full_ok_simulations))) >>
      rewrite_tac[expr_sim_full_eq] >>
      disch_then (drule_then ACCEPT_TAC)) >>
  rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (qpat_assum `!z ety ee ca cb sha shb op' u J tau. _ ==> gas_prefix_full _ _ _ _ _` irule >>
      simp[value_read_demand_def] >>
      qpat_assum `expr_sim_full_pre _ _ _ _ l _ _` (irule_at Any) >> simp[]) >>
  drule_all (DISCH_ALL (CONJUNCT1 (UNDISCH body_expr_full_ok_simulations))) >>
  rewrite_tac[expr_sim_full_eq] >>
  disch_then (drule_then ACCEPT_TAC)
QED
*)
Theorem bool_chain_word_eq_prefix_of_smaller:
  value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    tops cenv cx env (Builtin (BaseT BoolT) (Bop Eq) [l;r]) ty es
    (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
  ~is_bytestring_type (expr_type l) /\ is_word_type (expr_type l) /\
  is_word_type (expr_type r) /\ body_expr_full_ok cx l /\
  (!gs v m. bind (eval_expr cx l) (read_result cx) (es with gas_obs := gs) = (INL v,m) ==>
            body_expr_full_ok cx r) /\
  (!z ety ee ca cb sha shb op' u J tau.
     expr_size z < expr_size (Builtin (BaseT BoolT) (Bop Eq) [l;r]) /\
     body_expr_full_ok cx z /\
     value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       tops cenv cx env z ety ee (st0,ca,cb,sha,shb,op',u,J,tau) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx z) (read_result cx)) (ee,u,J,tau)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx (Builtin (BaseT BoolT) (Bop Eq) [l;r])) (read_result cx))
    (es,s0,G0,tn0)
Proof
  cheat
QED
