(* Compose all-tail default replays at a shared source and native cut. *)
Theory s1PrefixBoolChainDefaultChildConcat
Ancestors
  gasOutcomeFull gasSummaryCompose fragGasOriginPtr rich_list

Theorem bool_chain_default_child_concat:
  ((!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
             (INL a, mid with gas_obs := tail)) /\
    (!tail. next a (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
             (res, fin with gas_obs := tail)) /\
    t.vs_gas_readings = DROP (LENGTH left) s.vs_gas_readings /\
    isPREFIX mid.storage_trace fin.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (s,G,tn) left (OK t,G1,tn1)) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (t,G1,tn1) right (r,G2,tn2)) ==>
    (!tail. bind source next
              (es with gas_obs := gas_explicit (left ++ right) s.vs_gas_readings ++ tail) =
             (res, fin with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (s,G,tn) (left ++ right) (r,G2,tn2))) /\
  ((!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
             (INR exc, mid with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (s,G,tn) left (r1,G1,tn1)) ==>
    (!tail. bind source next
              (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
             (INR exc, mid with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (s,G,tn) left (r1,G1,tn1)))
Proof
  conj_tac
  >- (strip_tac >> conj_tac
      >- (pure_rewrite_tac[gasSummaryTheory.gas_explicit_append] >>
          irule gas_source_bind_normal >> qexistsl_tac [`mid`, `a`] >> fs[]) >>
      rpt strip_tac >>
      `valid_horizon cx st0 H mid.storage_trace` by
        (fs[IS_PREFIX_APPEND] >> metis_tac[valid_horizon_append]) >>
      metis_tac[gas_origin_ptr_path_append]) >>
  simp[gas_source_bind_exception]
QED
