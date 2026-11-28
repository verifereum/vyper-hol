(* Reached default-list cuts, from the original default entry through marshalling. *)
Theory s1PrefixBoolChainUsedDefaultBind
Ancestors
  s1PrefixBoolChainDefaultCallback s1PrefixBoolChainPushedChildren
  s1PrefixBoolChainDefaultSuffixFold s1PrefixIntCallStageSingleton s1PrefixIntCallStageList
  bodyFullCreateHeld gasSummaryCompose fragGasPath exprLowering compileEnv
  vyperState vyperTypeCallGraph vyperReadOnlyEval list pair

Theorem stage_intcall_args_snoc[local]:
  !done flags tys start ops si.
  LENGTH done = LENGTH flags /\ LENGTH done = LENGTH tys /\
  compile_stage_intcall_args cfn ce done flags tys start = (ops,si) /\
  compile_stage_intcall_args cfn ce [a] [flag] [ty] si = ([opnd],sm) ==>
  compile_stage_intcall_args cfn ce (done ++ [a]) (flags ++ [flag]) (tys ++ [ty]) start =
    (ops ++ [opnd],sm)
Proof
  Induct >- simp[compile_stage_intcall_args_def,comp_return_def] >>
  Cases_on `flags` >> simp[] >> Cases_on `tys` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stage_intcall_args _ _ (_::done) _ _ start = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_stage_intcall_args_cons_cut]) >>
  qmatch_goalsub_rename_tac `compile_stage_intcall_args cfn ce [e] [f] [dt]` >>
  Cases_on `compile_stage_intcall_args cfn ce [e] [f] [dt] start` >>
  simp[comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `!flags tys start ops si. _` (fn ih =>
    qpat_assum `compile_stage_intcall_args _ _ done _ _ _ = _`
      (mp_then (Pos (el 3)) mp_tac ih)) >>
  simp[Once compile_stage_intcall_args_cons_cut,comp_bind_def,comp_return_def,APPEND_ASSOC]
QED

Theorem default_replay_snoc[local]:
  gas_path ctx func start (LENGTH prev) (OK s) /\
  (!tail. eval_exprs pushed done
    (src with gas_obs := gas_explicit prev start.vs_gas_readings ++ tail) =
    (INL dvs,es with gas_obs := tail)) /\
  gas_path ctx func s (LENGTH marks) (OK t) /\
  (!tail. eval_exprs pushed [a]
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL hs,mid with gas_obs := tail)) ==>
  gas_path ctx func start (LENGTH (prev ++ marks)) (OK t) /\
  (!tail. eval_exprs pushed (done ++ [a])
    (src with gas_obs := gas_explicit (prev ++ marks) start.vs_gas_readings ++ tail) =
    (INL (dvs ++ hs),mid with gas_obs := tail))
Proof
  strip_tac >> conj_tac
  >- (pure_rewrite_tac[LENGTH_APPEND] >>
      irule gas_path_then >> qexists_tac `s` >> simp[]) >>
  gen_tac >>
  `gas_explicit (prev ++ marks) start.vs_gas_readings =
   gas_explicit prev start.vs_gas_readings ++ gas_explicit marks s.vs_gas_readings` by
    (irule gas_explicit_append_path >> metis_tac[]) >>
  once_rewrite_tac[create_eval_exprs_append] >>
  asm_simp_tac std_ss [GSYM APPEND_ASSOC,bind_def,return_def] >> simp[]
QED

(* The nil port closes over the fixed supplied replay and its saved scope.
   Its varying fields come from readiness and the default execution history. *)
Theorem bool_chain_used_default_bind_prefix:
  (ds0 <> [] ==> LENGTH (remcode pushed) < rank) /\
  (!c a. LENGTH (remcode c) < rank /\
       (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok c a) /\
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (vyperTypeCallGraph$int_calls_exprs ds0) /\
  body_inv tops ctx ce pushed /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ gas_shadow_state sf shf /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok H (DF H) lo ce pushed) /\
  (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
  (!v. storage_trace_frame (next v)) /\
  (!dops dvs es s G tn marks.
    compile_stage_intcall_args compile_expr ce ds0 flags0 tys0 cstart = (dops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr ds0) flags0 tys0 shstart = (dops,shf) /\
    gas_path ctx func start (LENGTH marks) (OK s) /\
    (!tail. eval_exprs pushed ds0
      (src with gas_obs := gas_explicit marks start.vs_gas_readings ++ tail) =
      (INL dvs,es with gas_obs := tail)) /\
    storage_trace_domain pushed st0 es.storage_trace /\
    gas_admissible (next (svs ++ dvs)) P es /\
    (!H. valid_horizon pushed st0 H es.storage_trace ==>
      intcall_args_stage_post (DF,lo,d,ctx,func,ce,pushed,tenv with current_src := NONE)
        ([]:expr list,sa,s0,es0,G0,tn0,sf)
        ([],[],[],sops ++ dops,svs ++ dvs,stys ++ tys0,sflags ++ flags0,pin,clean_words,keep_sites)
        H (INL [] : value list + exception) es G tn s) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      pushed st0 (next (svs ++ dvs)) (es,s,G,tn)) ==>
  !rs si shi flags dtys ops vals ptys pflags es s G tn.
  bool_chain_default_ready
    (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,ce,pushed,tenv with current_src := NONE,st0)
    (sa,s0,es0,G0,tn0,sf,shf,pin,clean_words,keep_sites) next P rs
    (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) /\
  (?done dops dvs fs ts prev.
    ds0 = done ++ rs /\ flags0 = fs ++ flags /\ tys0 = ts ++ dtys /\
    LENGTH done = LENGTH fs /\ LENGTH done = LENGTH ts /\
    ops = sops ++ dops /\ vals = svs ++ dvs /\ ptys = stys ++ ts /\ pflags = sflags ++ fs /\
    compile_stage_intcall_args compile_expr ce done fs ts cstart = (dops,si) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr done) fs ts shstart = (dops,shi) /\
    gas_path ctx func start (LENGTH prev) (OK s) /\
    (!tail. eval_exprs pushed done
      (src with gas_obs := gas_explicit prev start.vs_gas_readings ++ tail) =
      (INL dvs,es with gas_obs := tail))) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    pushed st0 (bind (eval_exprs pushed rs) (\vs. next (vals ++ vs))) (es,s,G,tn)
Proof
  strip_tac >>
  qabbrev_tac `ready = \rs (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn).
    bool_chain_default_ready
      (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,ce,pushed,tenv with current_src := NONE,st0)
      (sa,s0,es0,G0,tn0,sf,shf,pin,clean_words,keep_sites) next P rs
      (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) /\
    (?done dops dvs fs ts prev.
      ds0 = done ++ rs /\ flags0 = fs ++ flags /\ tys0 = ts ++ dtys /\
      LENGTH done = LENGTH fs /\ LENGTH done = LENGTH ts /\
      ops = sops ++ dops /\ vals = svs ++ dvs /\ ptys = stys ++ ts /\ pflags = sflags ++ fs /\
      compile_stage_intcall_args compile_expr ce done fs ts cstart = (dops,si) /\
      compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
        (MAP gas_shadow_expr done) fs ts shstart = (dops,shi) /\
      gas_path ctx func start (LENGTH prev) (OK s) /\
      (!tail. eval_exprs pushed done
        (src with gas_obs := gas_explicit prev start.vs_gas_readings ++ tail) =
        (INL dvs,es with gas_obs := tail)))` >>
  `!ds si shi flags dtys ops vals ptys pflags es s G tn.
     ready ds (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       pushed st0 (bind (eval_exprs pushed ds) (\vs. next (vals ++ vs))) (es,s,G,tn)`
  suffices_by (simp[Abbr `ready`]) >>
  ho_match_mp_tac (Q.INST [`ce` |-> `ce`, `tops` |-> `cx_tops pushed`]
    bool_chain_default_suffix_prefix_fold) >> simp[] >>
  conj_tac >- suspend "nil" >>
  conj_tac >- suspend "cons" >>
  simp[Abbr `ready`] >> rpt strip_tac >> drule bool_chain_default_ready_nil >> simp[]
QED

Resume bool_chain_used_default_bind_prefix[nil]:
  simp[Abbr `ready`] >> rpt strip_tac >>
  qpat_x_assum `bool_chain_default_ready _ _ _ _ [] _ _` mp_tac >>
  simp[bool_chain_default_ready_def,compile_stage_intcall_args_def,comp_return_def,
       intcall_stage_nil_source,bind_return] >> strip_tac >>
  gvs[] >> last_x_assum irule >> metis_tac[]
QED

Resume bool_chain_used_default_bind_prefix[cons]:
  simp[Abbr `ready`] >> rpt gen_tac >> strip_tac >>
  qpat_assum `bool_chain_default_ready _ _ _ _ (a::rs) _ _`
    (mp_then (Pos (el 13)) (qspec_then `PG` mp_tac)
      bool_chain_default_singleton_callback) >>
  (impl_tac >- suspend "child") >>
  disch_then (qx_choosel_then [`flag`,`rest_flags`,`dt`,`rest_tys`,`opnd`,`sm`,`shm`,`Q`,`R`]
    strip_assume_tac) >>
  map_every qexists_tac [`flag`,`rest_flags`,`dt`,`rest_tys`,`opnd`,`sm`,`shm`,`Q`,`R`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> suspend "advance"
QED

Resume bool_chain_used_default_bind_prefix[child]:
  `LENGTH (remcode pushed) < rank` by
    (qpat_assum `ds0 <> [] ==> _` irule >> simp[]) >>
  qpat_assum `bool_chain_default_ready _ _ _ _ (a::rs) _ _`
    (strip_assume_tac o SIMP_RULE std_ss [bool_chain_default_ready_def,EVERY_DEF]) >>
  `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (int_calls_expr a)` by
    (gvs[int_calls_exprs_FLAT_MAP, MAP_APPEND, EVERY_FLAT, EVERY_APPEND]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> drule_all bool_chain_pushed_default_child >>
  disch_then (fn th => FIRST [irule (cj 3 th), irule (cj 4 th)]) >>
  first_assum (irule_at Any)
QED

Resume bool_chain_used_default_bind_prefix[advance]:
  map_every qx_gen_tac [`marks`,`hs`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  conj_tac
  >- (qpat_assum `!marks hs mid G1 tn1 t. _ ==> bool_chain_default_ready _ _ _ _ _ _ _`
        irule >> simp[] >> qexists_tac `marks` >> simp[]) >>
  qexistsl_tac [`done ++ [a]`,`dops ++ [opnd]`,`dvs ++ hs`,
    `fs ++ [flag]`,`ts ++ [dt]`,`prev ++ marks`] >>
  simp[APPEND_ASSOC,MAP_APPEND] >>
  conj_tac
  >- (irule stage_intcall_args_snoc >> simp[] >> qexists_tac `si` >> simp[]) >>
  conj_tac
  >- (irule stage_intcall_args_snoc >> simp[] >> qexists_tac `shi` >> simp[]) >>
  drule_all default_replay_snoc >> simp[]
QED

Finalise bool_chain_used_default_bind_prefix
