Theory s1PrefixTupleNestedHeadBind
Ancestors
  tupleWidenedStoreEntry bodyFullTargetDefs s1PrefixCompose s1PrefixProps
  s1PrefixDefs gasOutcomeFullCompose gasOutcomeFull gasExemptCert gasStorage
  bodyPtrDefs vyperStorageFootprint vyperStorageTrace tuplePlaceStep
  vyperInterpreter vyperState exprSimDefs allocaHistory sum list
  vyperPlaceWriteSoundness vyperTypeInvariants

(* The place computation can issue requests. Only the subsequent write is
   silent; its continuation starts at the very same marked place endpoint. *)
Theorem tuple_widened_nested_head_bind:
  EL j gs = BaseTarget head /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_target_place cx head) (src,s,G,tn)
    (\H res mid Gp tp sp. ?path.
      res = INL (ImmutablePlace NONE id path) /\
      imm_target_post H ctx func cenv cx src c place_cs s mid id path ty place_result sp /\
      expr_sim_inv cenv cx env mid /\ state_well_typed mid /\
      runtime_place_typed cx mid (ImmutablePlace NONE id path) tv /\
      runtime_place_writable cx mid (ImmutablePlace NONE id path) /\
      sp.vs_current_bb = place_cs.cs_current_bb /\
      sp.vs_inst_idx = LENGTH place_cs.cs_current_insts /\
      alloca_history func sp /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sp) /\
      s.vs_alloca_next <= sp.vs_alloca_next /\ ~sp.vs_halted /\ mid.gas_obs = [] /\
      ghost_inv_at (DF H) lo d cenv cx mid Gp tp sp /\
      target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id path)) place_result Gp tp sp /\
      op_prov Gp (FST place_result) = NONE /\ ghost_kept_at lo cenv src c G tn s Gp tp)
    (\H res mid gt r. expr_exit res r /\ halt_exit H cx mid res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_target_place cx head) (src,s,G,tn) /\
  (!marks mid Gp tp sp path.
    (!tail. eval_target_place cx head
      (src with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (ImmutablePlace NONE id path),mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK sp,Gp,tp)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      imm_target_post H ctx func cenv cx src c place_cs s mid id path ty place_result sp /\
      expr_sim_inv cenv cx env mid /\ state_well_typed mid /\
      runtime_place_typed cx mid (ImmutablePlace NONE id path) tv /\
      runtime_place_writable cx mid (ImmutablePlace NONE id path) /\
      sp.vs_current_bb = place_cs.cs_current_bb /\
      sp.vs_inst_idx = LENGTH place_cs.cs_current_insts /\
      alloca_history func sp /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sp) /\
      s.vs_alloca_next <= sp.vs_alloca_next /\ ~sp.vs_halted /\ mid.gas_obs = [] /\
      ghost_inv_at (DF H) lo d cenv cx mid Gp tp sp /\
      target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id path)) place_result Gp tp sp /\
      op_prov Gp (FST place_result) = NONE /\ ghost_kept_at lo cenv src c G tn s Gp tp) ==>
    ?fin q Gf tf'.
      (!tail. write_place cx (ImmutablePlace NONE id path) (EL j vs)
        (mid with gas_obs := tail) = (INL (),fin with gas_obs := tail)) /\
      fin.gas_obs = [] /\
      (!H. valid_horizon cx st0 H fin.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (sp,Gp,tp) [] (OK q,Gf,tf')) /\
      (?c2 sh2 obs2.
        tuple_widened_store_entry [] (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
          (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf)
          (SUC j) c2 sh2 fin q Gf tf' obs2)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (assign_tuple_targets cx (EL j gs) (EL j vs)) (src,s,G,tn)
    (\H res mid G2 tn2 s2. ?c2 sh2 obs2.
      tuple_widened_store_entry [] (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
        (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf)
        (SUC j) c2 sh2 mid s2 G2 tn2 obs2)
    (\H res ee gt r. ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (assign_tuple_targets cx (EL j gs) (EL j vs)) (src,s,G,tn)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ placeQ placeR` >>
  simp[Once evaluate_def] >> conj_tac
  >- (irule gas_outcome_full_bind_all_path >> BETA_TAC >>
      simp[storage_trace_frame_write_place, cj 8 evaluate_storage_trace_frame] >>
      conj_tac
      >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >>
          goal_assum (drule_at Any) >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> simp[]) >>
      qexists_tac `placeQ` >> reverse conj_tac
      >- (qpat_assum `gas_outcome_full _ _ _ _ _ _ placeQ placeR`
            (mp_then Any irule gas_outcome_full_post_mono) >>
          simp[Abbr `placeR`] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def]) >>
      map_every qx_gen_tac [`marks`,`res`,`mid`,`Gp`,`tp`,`sp`] >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[storage_trace_domain_def] >>
      unabbrev_all_tac >> RULE_ASSUM_TAC BETA_RULE >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> ?path. _`
        (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
      gvs[] >>
      qpat_assum `!marks mid Gp tp sp path. _`
        (qspecl_then [`marks`,`mid`,`Gp`,`tp`,`sp`,`path`] mp_tac) >>
      simp[] >>
      strip_tac >> irule gas_outcome_full_pure >> simp[] >>
      qexistsl_tac [`Gf`,`fin`,`INL ()`,`q`,`tf'`] >>
      `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
      simp[] >> rpt strip_tac >> goal_assum (drule_at Any)) >>
  simp[Once evaluate_def] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ placeQ placeR`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_write_place, cj 8 evaluate_storage_trace_frame,
       cj 8 evaluate_requests_outcomes_frame] >>
  conj_tac
  >- (rpt strip_tac >> drule write_place_storage_trace >> simp[DROP_LENGTH_NIL]) >>
  conj_tac >- simp[Abbr `placeQ`, PULL_EXISTS] >>
  simp[Abbr `placeR`] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def]
QED
