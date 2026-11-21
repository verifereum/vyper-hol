Theory forCapturedStorageCons
Ancestors
  forCapturedStorageLive gasOutcomeFullCompose gasOutcomeFull gasContext
  gasExemptCert bodyFullIfExpReach exprSimMemorySource stmtSimForParts
  stmtSimDefs fragExec fragGasOriginPtr vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState finite_map

(* The admission check for the whole remaining loop implies the corresponding
   check for the first loop body, at the scope produced by the selected read. *)
Theorem captured_storage_body_admissible[local]:
  gas_admissible (eval_for cx tyv id stmts (a::rs)) ok es /\
  (!res. ok res ==> stmt_res_ok lctx res) /\
  lookup_scopes id es.scopes = NONE /\ read_result cx a es = (INL v,es) ==>
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
    (es with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)) :: es.scopes;
      gas_obs := [] |>)
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts _ = (raw,ef)` >>
  `read_result cx a (es with gas_obs := gs) = (INL v,es with gas_obs := gs)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `eval_for cx tyv id stmts (a::rs) (es with gas_obs := gs) =
   eval_for cx tyv id stmts (Value v::rs) (es with gas_obs := gs)` by
    (qpat_assum `read_result cx a (es with gas_obs := gs) = _`
       (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read) >>
     `read_result cx (Value v) (es with gas_obs := gs) = (INL v,es with gas_obs := gs)` by
       simp[read_result_def,return_def] >>
     qpat_assum `read_result cx (Value v) _ = _`
       (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read)) >>
  Cases_on `eval_for cx tyv id stmts (Value v::rs) (es with gas_obs := gs)` >>
  rename1 `eval_for cx tyv id stmts (Value v::rs) _ = (lr,le)` >>
  `stmt_res_ok lctx lr` by
    (first_x_assum irule >>
     qpat_assum `gas_admissible _ _ _`
       (qspecl_then [`gs`,`lr`,`le`] mp_tac o REWRITE_RULE[gas_admissible_def]) >> simp[]) >>
  qpat_assum `eval_for cx tyv id stmts (Value v::rs) _ = (lr,le)`
    (mp_then Any mp_tac stmtSimForPartsTheory.eval_for_cons_cases) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `stmt_res_ok lctx _` mp_tac >> simp[stmt_res_ok_def]
QED

(* The head and cleanup run on the same endpoint. Only a continuing cleanup
   executes the (zero-GAS-mark) increment, with its original index. *)
Theorem for_captured_storage_cons_from_stages:
  let Live = \lab H j xs ee G' tn' t.
    for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
      (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
      (lvo,idx,lab) (p,dst,nb,sd) (H,j,xs,ee,G',tn',t) in
  let head = bind (read_result cx a) (push_scope_with_var id tyv) in
  let clean = finally (try (ignore_bind (eval_stmts cx stmts) (return F))
                      handle_loop_exception) pop_scope in
  let Scoped = \v. es with <| scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)) :: es.scopes;
    gas_obs := [] |> in
  let Qhead = \H (res:unit + exception) eb G1 tn1 z.
    res = INL () /\ eb.gas_obs = [] /\
    ?v. eb = Scoped v /\ read_result cx a es = (INL v,es) /\
        Entry H (es with gas_obs := []) v k z G1 tn1 /\
        eval_operand bop z = SOME slot /\ op_taint tn1 bop = {} in
  let Qclean = \H (res:bool + exception) ee G1 tn1 t.
    ee.gas_obs = [] /\ ~t.vs_halted /\
    ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
        (~b ==> Live incr H k (a::rs) ee G1 tn1 t /\ k < len /\
                body_stmts_full_ok cx stmts) in
  ~s.vs_halted /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!f inst u. frag_reachable ctx func s f inst u ==> dalloca_no_wrap inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> Live cond H k (a::rs) es G tn s) /\
  gas_admissible (eval_for cx tyv id stmts (a::rs)) ok es /\
  (!res. ok res ==> stmt_res_ok lctx res) /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 head (es,s,G,tn)
     Qhead (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) /\
  (!v eb G1 tn1 z.
     eb = Scoped v /\ read_result cx a es = (INL v,es) /\ k < len /\
     eval_operand bop z = SOME slot /\ op_taint tn1 bop = {} /\
     (!H. valid_horizon cx st0 H eb.storage_trace ==>
          Entry H (es with gas_obs := []) v k z G1 tn1) /\
     gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) eb /\
     (!f inst u. frag_reachable ctx func z f inst u ==> dalloca_no_wrap inst u) ==>
     gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 clean (eb,z,G1,tn1)
       Qclean (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) /\
  (!ee G1 tn1 t.
     k < len /\ body_stmts_full_ok cx stmts /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> Live incr H k (a::rs) ee G1 tn1 t) ==>
     ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2) /\
       Live cond H (SUC k) rs ee G2 tn2 u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (read_result cx a) (\v. ignore_bind (push_scope_with_var id tyv v) clean))
    (es,s,G,tn)
    (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
      ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
          (~b ==> ?j. Live cond H j rs ee G1 tn1 t))
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  BasicProvers.LET_ELIM_TAC >>
  `storage_trace_frame head` by
    (simp[Abbr `head`] >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result,storage_trace_frame_state_updates]) >>
  `storage_trace_frame clean` by
    (simp[Abbr `clean`] >> irule storage_trace_frame_finally >>
     simp[storage_trace_frame_pop_scope] >> irule storage_trace_frame_try >>
     simp[storage_trace_frame_loop_handler] >> irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_return, evaluate_storage_trace_frame]) >>
  `bind head (\u:unit. clean) =
    bind (read_result cx a) (\v. ignore_bind (push_scope_with_var id tyv v) clean)` by
    simp[Abbr `head`,bind_assoc,ignore_bind_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- (irule storage_trace_frame_bind_all >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  irule gas_outcome_full_zero_suffix >> qexists `Qclean` >>
  reverse conj_tac >- suspend "bind_head" >> suspend "increment"
QED

Resume for_captured_storage_cons_from_stages[bind_head]:
  irule gas_outcome_full_bind_all_path >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_unit >>
               qexistsl [`mid`,`t`] >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_unit >> simp[]) >>
  qexists `Qhead` >> reverse conj_tac >- simp[] >>
  suspend "body_entry"
QED

Resume for_captured_storage_cons_from_stages[body_entry]:
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `Hm = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 Hm mid.storage_trace` by
    simp[Abbr `Hm`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Qhead H _ _ _ _ _`
    (qspec_then `Hm` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms,Abbr `Qhead`] >> strip_tac >>
  rename1 `read_result cx a es = (INL v,es)` >>
  `mid.storage_trace = es.storage_trace` by
    (qpat_assum `mid = Scoped v` SUBST1_TAC >> simp[Abbr `Scoped`]) >>
  `Live cond Hm k (a::rs) es G tn s` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> Live _ _ _ _ _ _ _ _`
       (qspec_then `Hm` irule) >>
     qpat_assum `mid.storage_trace = es.storage_trace` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `k < len /\ lookup_scopes id es.scopes = NONE` by
    (qpat_assum `Live cond Hm k _ _ _ _ _` mp_tac >>
     qpat_assum `Abbrev (Live = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     BETA_TAC >> pure_rewrite_tac[for_captured_storage_live_def] >>
     strip_tac >> conj_tac
     >- (qpat_assum `len = LENGTH vs` SUBST1_TAC >>
         qpat_assum `a::rs = DROP k vs`
           (ACCEPT_TAC o CONJUNCT1 o MATCH_MP DROP_EQ_CONS o SYM)) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    Entry H (es with gas_obs := []) v k t G1 tn1` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Qhead H _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
     strip_tac >> rename1 `Entry H _ v' k t G1 tn1` >>
     qpat_assum `read_result cx a es = (INL v',es)` mp_tac >>
     qpat_assum `read_result cx a es = (INL v,es)` (fn th => simp[NoAsms,th]) >>
     disch_then SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  `!f inst u. frag_reachable ctx func t f inst u ==> dalloca_no_wrap inst u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `Hm` (drule_then assume_tac)) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ (OK t,G1,tn1)`
       (mp_tac o MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
                            gas_origin_ptr_path_dalloca_no_wrap)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) mid` by
    (qpat_assum `mid = Scoped v` SUBST1_TAC >> simp[Abbr `Scoped`] >>
     drule_all captured_storage_body_admissible >> simp[]) >>
  qpat_x_assum `mid = Scoped v` SUBST_ALL_TAC >>
  qpat_assum `!v G1 tn1 z. _ ==> gas_outcome_full _ _ _ _ clean _ _ _`
    (qspecl_then [`v`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Resume for_captured_storage_cons_from_stages[increment]:
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ee.gas_obs = [] /\ ~t.vs_halted /\
    ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
      (~b ==> Live incr H k (a::rs) ee G1 tn1 t /\ k < len /\
              body_stmts_full_ok cx stmts)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> Qclean H _ _ _ _ _` mp_tac >>
     qpat_assum `Abbrev (Qclean = _)`
       (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >> BETA_TAC >>
     disch_then ACCEPT_TAC) >>
  pop_assum (fn th => assume_tac th >> qspec_then `H0` mp_tac th) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `res = INL (b:bool)` >>
  Cases_on `b`
  >- (qexistsl [`t`,`G1`,`tn1`] >> qx_gen_tac `H` >> disch_tac >>
      simp[] >> conj_tac
      >- (irule (CONJUNCT1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ (?b. _)`
        (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `res = INL T` (fn th => simp[NoAsms,th])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> Live incr H k (a::rs) ee G1 tn1 t` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ (?b. _)`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `res = INL F` (fn th => simp[NoAsms,th])) >>
  qpat_assum `!ee G1 tn1 t. _ ==> ?u G2 tn2. _`
    (qspecl_then [`ee`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G2` (qx_choose_then `tn2` assume_tac))) >>
  qexistsl [`u`,`G2`,`tn2`] >> qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ Live cond H _ _ _ _ _ _` drule >>
  strip_tac >> simp[] >>
  conj_tac
  >- (qpat_assum `Live cond H _ _ _ _ _ _` mp_tac >>
      simp[NoAsms,Abbr `Live`,for_captured_storage_live_def]) >>
  qexists `SUC k` >> first_assum ACCEPT_TAC
QED

Finalise for_captured_storage_cons_from_stages
