(* Lift the checked step at a selected STATICCALL through its native focus. *)
Theory s1PrefixBoolChainIndexedCut
Ancestors
  s1PrefixBoolChainReachedSource s1PrefixDefs fragGasOriginPtr list pair

Triviality native_focus_append:
  !c st left out. gas_origin_ptr_focus c st left out ==>
    !D lo explicit ctx func PG s G tn mid midPG midG midTn t
     right leaf leafPG leafG leafTn u.
    c = (D,lo,explicit,ctx,func,PG) /\ st = (s,G,tn) /\
    out = (mid,midPG,midG,midTn,t) /\
    gas_origin_ptr_focus (D,lo,explicit,ctx,mid,midPG) (t,midG,midTn)
      right (leaf,leafPG,leafG,leafTn,u) ==>
    gas_origin_ptr_focus (D,lo,explicit,ctx,func,PG) (s,G,tn)
      (left ++ right) (leaf,leafPG,leafG,leafTn,u)
Proof
  ho_match_mp_tac gas_origin_ptr_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  >- (rewrite_tac[GSYM APPEND_ASSOC] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  >> irule (cj 3 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

Triviality indexed_site_prepend_focus:
  gas_origin_ptr_focus (D,lo,explicit,ctx,root,rootPG) (s,J,tm)
    marks (func,PG,G,tn,t) /\
  request_site (D,lo,explicit,ctx,func,PG) cx H (t,G,tn) k rq oc ==>
  request_site (D,lo,explicit,ctx,root,rootPG) cx H (s,J,tm) k rq oc
Proof
  rewrite_tac[request_site_def] >> strip_tac >>
  qexistsl_tac [`marks ++ left`,`leaf`,`leaf_pg`,`G'`,`tn'`,`t'`,
    `inst`,`fuel`,`t''`] >> simp[] >>
  qpat_assum `gas_origin_ptr_focus _ _ marks _`
    (mp_then Any mp_tac native_focus_append) >> simp[]
QED

Theorem bool_chain_indexed_staticcall_site:
  seen = cut.storage_trace /\
  LENGTH cut.requests = recorded_outcomes_count seen /\
  take_request_outcome rq0 cut = (INL (rq,oc),consumed) /\
  ~computed_precompile rq /\
  gas_origin_ptr_focus (DF H,lo,explicit,ctx,root,rootPG) (s,J,tm)
    marks (func,PG,G,tn,t) /\
  emit_op STATICCALL [gas;addr;dp;dl;buf;rz] sc = (Var out,sd) /\
  fn_has_code sc sd func /\
  ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  step_inst_base (mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]) t = OK post /\
  inst_mem_below_frontier (mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]) t /\
  eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
  eval_operand buf t = SOME ro /\ eval_operand rz t = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p t (w2n az)) /\
  (rn <> 0w ==> ?p. buf = Var p /\ ptr_covers G tn p t (w2n rn)) /\
  EVERY (\p. op_taint tn p = {}) [gas;addr;dp;dl;buf;rz] /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  ghost_inv_at (DF H) lo d cenv cx cut G tn t /\
  stmt_state_rel H ctx func cenv cx cut t /\
  stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) post ==>
  request_site (DF H,lo,explicit,ctx,root,rootPG) cx H (s,J,tm)
    (recorded_outcomes_count seen) rq oc
Proof
  strip_tac >> drule indexed_site_prepend_focus >> disch_then irule >>
  drule_all_then MATCH_ACCEPT_TAC reached_staticcall_request_site
QED
