(* Extract the selected Array capture once and retain it across all suffixes. *)
Theory bodyForArrayOriginRoundsMods
Ancestors
  bodyForArrayOriginConsMods bodyForArrayNilCutMods bodyForRoundsDomainMods
  bodyForArraySelectedPacketMods bodyForArrayHeaderMods vyperStorageFootprint

val _ = Parse.hide "body";

Theorem for_array_origin_rounds_mods:
  contract_inv mods exps ctx c cx /\ module_body_inv mods src tops c cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id fty (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id fty (Array e) n body) ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  type_stmt env ret_ty (For id fty (Array e) n body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root c env)
    (For id fty (Array e) n body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmt (For id fty (Array e) n body)) /\
      IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
      IS_SOME (FLOOKUP c.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id fty (Array e) n body)) /\
  stmt_loop_calls_ok mods (For id fty (Array e) n body) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ c ret_ty /\
  evaluate_type (get_tenv cx) fty = SOME tyv /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  local_ptrs_reserved c sa0 /\ ~block_is_terminated sbCopy /\
  (is_slot_addressed loc ==>
    ?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    for_array_selected_entry_mods mods exps cx env st0 tyv id body
      (DF,lo,d,ctx,func,shadow_func) (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var),
       (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy),
       (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody)) H vs ee G tn t) /\
  gas_admissible (eval_for cx tyv id body vs) (stmt_res_ok lctx) ee ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_for cx tyv id body vs) (ee,t,G,tn)
    (\H res ee G1 tn1 t. res = INL () /\
      for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0 H ee G1 tn1 t)
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choose_then `P` strip_assume_tac)
    for_array_selected_entry_extract_mods >>
  qabbrev_tac `InvX = \H rs ee G tn t.
    for_array_selected_header_mods mods exps (DF,lo,d,ctx,func,shadow_func)
      cx env st0 (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var),
       (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy),
       (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody)) P H vs rs ee G tn t` >>
  qabbrev_tac `DoneX = for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0` >>
  `~t.vs_halted` by suspend "unhalted" >>
  irule (BETA_RULE (Q.INST [`Inv` |-> `InvX`, `Done` |-> `DoneX`,
    `R` |-> `\H ex ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z)`]
    for_rounds_bind_domain_mods)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`InvX`, `stmt_res_ok lctx`] >>
  conj_tac >- suspend "cons" >>
  conj_tac >- suspend "nil" >>
  simp[Abbr `InvX`]
QED

Resume for_array_origin_rounds_mods[unhalted]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!K. _ ==> for_array_selected_header_mods _ _ _ _ _ _ _ _ P K _ _ _ _ _ _`
    (drule_then assume_tac) >>
  PairCases_on `P` >>
  qhdtm_x_assum `for_array_selected_header_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_selected_header_route_mods]) >>
  qhdtm_x_assum `for_array_header_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
  first_assum ACCEPT_TAC
QED

Resume for_array_origin_rounds_mods[cons]:
  simp[Abbr `InvX`, Abbr `DoneX`] >> rpt gen_tac >> strip_tac >>
  irule for_array_origin_cons_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt (first_assum (irule_at Any)) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_origin_rounds_mods[nil]:
  simp[Abbr `InvX`, Abbr `DoneX`] >> rpt gen_tac >> strip_tac >>
  PairCases_on `P` >>
  qpat_x_assum `!H. _ ==> for_array_selected_header_mods _ _ _ _ _ _ _ _ _ H _ [] _ _ _ _`
    (assume_tac o REWRITE_RULE [for_array_selected_header_route_mods]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. _ ==> for_nonslot_layout _ _ _ _ _ _ _ /\ _`
    (map_every assume_tac o CONJUNCTS o
     SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qpat_assum `!H. _ ==> for_nonslot_layout _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qhdtm_assum `for_nonslot_layout`
    (mp_then (Pat `for_nonslot_layout _ _ _ _ _ _ _`) irule
      (INST_TYPE [alpha |-> ``:eval_result``] for_array_nil_from_cuts_mods)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  first_assum (part_match_exists_tac I o concl) >>
  first_assum ACCEPT_TAC
QED

Finalise for_array_origin_rounds_mods
