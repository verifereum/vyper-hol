(* Fold requests through the used defaults, one marshalled singleton at a time. *)
Theory s1PrefixBoolChainDefaultSuffixFold
Ancestors
  s1PrefixIntCallStageList s1PrefixCompose s1PrefixProps
  vyperStorageTrace vyperStorageFootprint vyperState list

(* Readiness relates the paired compiler cuts, the remaining flags and
   types, the accumulated arguments, and the current execution states.
   The head's normal post Q is used at the cut after marshalling, not
   at the end of the raw expression code. *)
Theorem bool_chain_default_suffix_prefix_fold:
  (!v. storage_trace_frame (next v)) /\
  (!si shi ops vals ptys pflags es s G tn.
    ready [] (si,shi,[],[],ops,vals,ptys,pflags) (es,s,G,tn) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (next vals) (es,s,G,tn)) /\
  (!a rs si shi flags dtys ops vals ptys pflags es s G tn.
    ready (a::rs) (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) ==>
    ?flag fs dt ts opnd sm shm Q R.
      flags = flag::fs /\ dtys = dt::ts /\
      compile_stage_intcall_args compile_expr ce [a] [flag] [dt] si = ([opnd],sm) /\
      compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
        [gas_shadow_expr a] [flag] [dt] shi = ([opnd],shm) /\
      gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
        (eval_exprs cx [a]) (es,s,G,tn) /\
      gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
        (eval_exprs cx [a]) (es,s,G,tn) Q R /\
      (!H res ee gt r. R H res ee gt r ==> ISR res) /\
      (!marks hs mid G1 tn1 t.
        (!tail. eval_exprs cx [a]
          (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL hs,mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\
        gas_path ctx func s (LENGTH marks) (OK t) /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H (INL hs) mid G1 tn1 t) ==>
        ready rs (sm,shm,fs,ts,ops ++ [opnd],vals ++ hs,ptys ++ [dt],pflags ++ [flag])
          (mid,t,G1,tn1))) /\
  (!si shi flags dtys ops vals ptys pflags es s G tn.
    ready [] (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) ==>
    flags = [] /\ dtys = []) ==>
  !ds si shi flags dtys ops vals ptys pflags es s G tn.
    ready ds (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (bind (eval_exprs cx ds) (\vs. next (vals ++ vs))) (es,s,G,tn)
Proof
  strip_tac >> Induct_on `ds`
  >- (rpt strip_tac >> simp[intcall_stage_nil_source,bind_return] >>
      first_x_assum irule >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a rs si shi flags dtys ops vals ptys pflags es s G tn. _`
    (drule_then strip_assume_tac) >>
  simp[Once intcall_stage_cons_source,bind_assoc,bind_return,APPEND_ASSOC] >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx [_]) _ _ _`
    (mp_then Any irule gas_prefix_full_bind_path) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       evaluate_requests_outcomes_frame] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`marks`,`hs`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  qpat_assum `!si shi flags dtys ops vals ptys pflags es s G tn. _ ==>
      gas_prefix_full _ _ _ (bind (eval_exprs cx _) _) _` irule >>
  `ready ds (sm,shm,fs,ts,ops ++ [opnd],vals ++ hs,ptys ++ [dt],pflags ++ [flag])
      (mid,t,G1,tn1)` by
    (qpat_assum `!marks hs mid G1 tn1 t. _ ==> ready _ _ _`
       irule >> simp[] >> qexists_tac `marks` >> simp[]) >>
  pop_assum (irule_at Any)
QED
