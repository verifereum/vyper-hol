(* Prefix replay of the remaining exact-layout tuple stores. *)
Theory s1PrefixAssignTupleExactReplay
Ancestors
  s1PrefixAssignTupleExactHead s1PrefixCompose s1PrefixFrame s1PrefixProps
  s1PrefixPreds bodyFullPreds bodyFullAssignTuple bodyTupleExactStoreCursor
  bodyFullTargetDefs bodyFullTupleTargetProjection stmtSimForRounds vyperStorageFootprint vyperTypeDefaults
  vyperInterpreter vyperStorageTrace vyperState valueEncoding list

Theorem exact_replay_cursor_shape[local]:
  tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
    (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
    (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys1,tvs1,vs1,ops1,k,p)
    (cur,shadow_cur,src,u,Gu,tu) ==>
  LENGTH tys1 = LENGTH todo /\ LENGTH tvs1 = LENGTH todo /\
  LENGTH vs1 = LENGTH todo /\ LENGTH ops1 = LENGTH todo /\
  EVERY (\g. ?bt. g = BaseTarget bt) todo
Proof
  pure_rewrite_tac[tuple_exact_store_cursor_def,tuple_exact_cursor_common_def,
                   values_have_types_LIST_REL] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  `LENGTH tys1 = LENGTH todo /\ LENGTH tvs1 = LENGTH todo /\
   LENGTH vs1 = LENGTH todo /\ LENGTH ops1 = LENGTH todo` by gvs[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
  qpat_assum `EVERY (\g. case g of BaseTarget _ => _ | TupleTarget _ => F) todo`
    (qspec_then `g` mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  Cases_on `g` >> simp[NoAsms] >> first_assum ACCEPT_TAC
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> Induct
  >- (rpt gen_tac >> strip_tac >>
      drule_then strip_assume_tac exact_replay_cursor_shape >>
      Cases_on `vs1` >> fs[] >>
      simp[Once evaluate_def] >> irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_return,return_def]) >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac exact_replay_cursor_shape >>
  Cases_on `tys1` >> fs[] >> Cases_on `tvs1` >> fs[] >>
  Cases_on `vs1` >> fs[] >> Cases_on `ops1` >> fs[] >>
  qmatch_asmsub_rename_tac `tuple_exact_store_cursor _ _ _ _ _
     (BaseTarget bt::todo,sty::tys_tail,stv::tvs_tail,vi::vs_tail,op0::ops_tail,k,p) _` >>
  dxrule_then strip_assume_tac body_tuple_targets_full_ok_cons_parts >>
  qpat_x_assum `body_tuple_targets_prefix_ok _ (_::_) (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE[body_tuple_target_prefix_ok_def]) >>
  drule_then assume_tac body_tuple_target_full_ok_base >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (assign_tuple_targets cx (BaseTarget bt) vi) (src,u,Gu,tu)` by
    (drule_all tuple_assign_exact_store_head_prefix >> simp[]) >>
  qpat_assum `tuple_exact_store_cursor _ _ _ _ _ _ _`
    (mp_then Any (qspecl_then [`shadow_ctx`,`ARB`,`PG`] mp_tac)
       tuple_assign_exact_store_head_outcome) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!bt'. _ /\ immutable_root cx bt' /\ _ ==> _`
       (qspec_then `bt` mp_tac) >> simp[NoAsms])) >>
  disch_then (qx_choosel_then [`sm`,`shadow_sm`] strip_assume_tac) >>
  `assign_tuple_target_list cx (BaseTarget bt::todo) (vi::vs_tail) =
     ignore_bind (assign_tuple_targets cx (BaseTarget bt) vi)
       (assign_tuple_target_list cx todo vs_tail)` by simp[Once evaluate_def] >>
  qpat_assum `assign_tuple_target_list _ (_::_) (_::_) = _` (pure_rewrite_tac o single) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (mp_then Any irule gas_prefix_full_ignore_bind) >>
  simp[evaluate_storage_trace_frame,evaluate_requests_outcomes_frame] >> conj_tac
  >- suspend "tail" >>
  simp[quantHeuristicsTheory.ISR_exists]
QED
*)
Theorem tuple_assign_exact_residual_store_prefix:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  values_have_types tvs vs /\ val_wf (TupleTV tvs) (ArrayV (TupleV vs)) ==>
  !todo tys1 tvs1 vs1 ops1 k cur shadow_cur src u Gu tu.
    (!bt. MEM (BaseTarget bt) todo /\ immutable_root cx bt /\
         ~(?nsid. bt = TopLevelNameTarget nsid) ==>
      !(H : (bool # bytes32 # type_value) list # num list) src mid u t sa sb id path ty r obs name b cap p tvs.
        eval_target_place cx bt (src with gas_obs := obs) =
          (INL (ImmutablePlace NONE id path),mid) /\
        imm_target_post H ctx func cenv cx src sa sb u mid id path ty r t /\
        local_region cenv src.scopes u name b cap /\
        b <= p /\ p + type_memory_size_list tvs <= b+cap /\
        local_path_at cenv cx name (p-b) (TupleTV tvs) ==>
        mem_bytes_at p (type_memory_size_list tvs) t.vs_memory =
          mem_bytes_at p (type_memory_size_list tvs) u.vs_memory) /\
    tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
      (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
      (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys1,tvs1,vs1,ops1,k,p)
      (cur,shadow_cur,src,u,Gu,tu) /\
    ~u.vs_halted /\ gas_admissible (assign_tuple_target_list cx todo vs1) ok src /\
    body_tuple_targets_full_ok cx todo vs1 /\ body_tuple_targets_prefix_ok cx todo vs1 ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (assign_tuple_target_list cx todo vs1) (src,u,Gu,tu)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_assign_exact_residual_store_prefix[tail]:
  map_every qx_gen_tac [`marks`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `?ee x ee'. assign_tuple_targets cx (BaseTarget bt) vi ee = (INL x,ee')` by
    (qpat_assum `!tail. assign_tuple_targets _ _ _ _ = _`
       (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  qpat_assum `assign_tuple_target_list _ (_::_) (_::_) = _`
    (fn th => qpat_x_assum `gas_admissible _ _ src`
       (assume_tac o REWRITE_RULE[th,ignore_bind_def])) >>
  drule_all gas_admissible_bind_tail >> simp[] >> strip_tac >>
  `tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
     (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
     (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys_tail,tvs_tail,vs_tail,ops_tail,SUC k,p)
     (sm,shadow_sm,mid,t,G1,tn1)` by
    (pure_rewrite_tac[tuple_exact_store_cursor_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  pop_assum (fn cursor => first_assum (fn ih => mp_then Any irule ih cursor)) >>
  simp[] >> conj_tac
  >- (qx_gen_tac `bt0` >> strip_tac >>
      qpat_assum `!bt'. _ /\ immutable_root cx bt' /\ _ ==> _`
        (qspec_then `bt0` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  conj_tac >> first_assum irule >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise tuple_assign_exact_residual_store_prefix
*)
