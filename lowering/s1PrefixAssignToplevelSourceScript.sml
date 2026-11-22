(* Request-prefix companion to bodyFullAssignToplevelSource. *)
Theory s1PrefixAssignToplevelSource
Ancestors
  s1PrefixPreds bodyFullAssignToplevelSource s1PrefixDefs s1PrefixNames
  tuplePlaceStep vyperPlaceFrames vyperStorageTrace vyperInterpreter vyperState list

Theorem body_assign_toplevel_word_prefix_source:
  gasContext$gas_admissible (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
    (stmtSimDefs$stmt_res_ok lctx) es /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q1
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn) /\
  (!marks res mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      Q1 H res (mid with gas_obs := []) G1 tn1 t) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (es,s,G,tn) Q R) /\
  (!marks res mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      Q1 H res (mid with gas_obs := []) G1 tn1 t) ==>
       gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (es,s,G,tn)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (es,s,G,tn)
Proof
  strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ (bind _ _) _`
    (qx_choose_then `marks` (CONJUNCTS_THEN2 assume_tac (mk_asm "rhs_sites")) o
     REWRITE_RULE [gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `st = es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
  rename1 `bind (eval_expr cx e) (read_result cx) st = (rhs,mid)` >>
  `?rest. mid.storage_trace = obs_pre ++ StorageOutcome rq outcome :: rest` by
    (qpat_x_assum `eval_stmt _ _ st = _` mp_tac >>
     pure_once_rewrite_tac[Once evaluate_def] >>
     pure_rewrite_tac[GSYM bind_assoc] >>
     Cases_on `rhs` >> simp[Once bind_def]
     >- (PairCases_on `nsid` >> simp[Once evaluate_def] >>
         simp[Once evaluate_def, GSYM bind_assoc] >>
         Cases_on `lookup_global cx nsid0 nsid1 mid` >>
         rename1 `lookup_global cx _ _ mid = (target,at_target)` >>
         disch_tac >>
         `ee.storage_trace = at_target.storage_trace` by
           (Cases_on `target` >> gvs[bind_def]
            >- (rename1 `lookup_global _ _ _ _ = (INL target,_)` >>
                Cases_on `get_place target at_target` >>
                rename1 `get_place _ _ = (got,after_get)` >>
                drule_then SUBST_ALL_TAC get_place_state >>
                Cases_on `got` >> gvs[] >>
                metis_tac[write_place_storage_trace]) >> simp[]) >>
         `?addon. at_target.storage_trace = mid.storage_trace ++ addon` by
           metis_tac[storage_trace_frame_lookup_global, storage_trace_frame_prefix] >>
         drule lookup_global_no_outcome >>
         gvs[rich_listTheory.DROP_APPEND1] >> strip_tac >>
         qpat_x_assum `mid.storage_trace ++ _ = _` mp_tac >>
         once_rewrite_tac[APPEND_EQ_APPEND] >> strip_tac
         >- (qexists_tac `l` >> simp[]) >>
         qpat_x_assum `EVERY _ (DROP _ _)` mp_tac >>
         simp[DROP_APPEND1, DROP_LENGTH_NIL, EVERY_APPEND] >>
         strip_tac >> CCONTR_TAC >>
         `LAST l = StorageOutcome rq outcome` by
           metis_tac[rich_listTheory.LAST_APPEND_NOT_NIL, LAST_APPEND_CONS, LAST_DEF] >>
         `MEM (StorageOutcome rq outcome) l` by
           metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
         fs[EVERY_MEM] >>
         qpat_x_assum `!ob. MEM ob l ==> _`
           (qspec_then `StorageOutcome rq outcome` mp_tac) >> simp[]) >>
     simp[] >> metis_tac[]) >>
  asm "rhs_sites" irule >>
  simp[] >> qexistsl_tac [`mid`,`rhs`,`rest`,`tail`] >> fs[Abbr `st`]
QED
