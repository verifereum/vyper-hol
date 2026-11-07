(* Memory-mode address and bytes argument continuation for raw_call. *)
Theory rawCallPrefixMemory
Ancestors
  bodyMemRawCallBounds rawCallGasMemory rawCallArgumentMemory exprSimRawCall exprSimHash bodyMemoryPreds exprSimMemDefs
  exprSimDefs exprSimProps exprLoweringProps loweringPosts bodySim
  compileEnv venomState vyperInterpreter vyperState fragExec exprSimSource exprSimHypsDefs
  bodyArgsMemory

Theorem raw_call_addr_data_sim_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  fn_has_code sa s2 func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gsA av esA tA gsD bs esD tD.
    bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
    esA.gas_obs = [] /\
    expr_post ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
      (INL (BytesV bs),esD) /\ esD.gas_obs = [] /\
    expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    expr_store_bound cx (expr_type d) (BytesV bs) data tD /\
    tD.vs_current_bb = s2.cs_current_bb /\
    tD.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func tD /\ s0.vs_alloca_next <= tD.vs_alloca_next /\ ~tD.vs_halted /\
    expr_sim_inv cenv cx env esD /\ body_exprs_mem_ok cx kws ==>
    gas_outcome T (cx_tops cx) (ctx,func) (k av (BytesV bs)) (esD,tD) Q R) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (k av))) (es,s0) Q R
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx (BaseT AddressT) a es` by
    (fs[body_exprs_mem_ok_def] >> metis_tac[body_expr_mem_ok_def]) >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule raw_call_mem_value_bind >>
  qpat_assum `lower_value _ _ _ a sa = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "data"
QED

Resume raw_call_addr_data_sim_mem[data]:
  `expr_body_pre cenv cx env a (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (irule (cj 1 expr_body_pre_base_result) >> goal_assum (drule_at Any) >>
     simp[ETA_THM] >> qexists_tac `INL v` >> fs[bind_def]) >>
  `expr_body_pre cenv cx env d ee` by
    (irule expr_body_pre_raw_call_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `body_exprs_mem_ok cx (d::kws)` by
    (qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     fs[body_exprs_mem_ok_def] >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type d) d ee` by
    (fs[body_exprs_mem_ok_def] >> metis_tac[body_expr_mem_ok_def]) >>
  `gas_admissible (bind (eval_expr cx d) (read_result cx)) expr_res_ok ee` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  `expr_sim_mem ctx func cenv cx (BaseT (BytesT (Dynamic n))) d ee` by metis_tac[] >>
  irule raw_call_mem_value_bind >>
  qpat_assum `lower_value _ _ _ d s1 = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "values"
QED

Resume raw_call_addr_data_sim_mem[values]:
  `expr_body_pre cenv cx env d (ee with gas_obs := gs')` by simp[] >>
  `expr_sim_inv cenv cx env ee'` by
    (irule (cj 1 expr_body_pre_base_result) >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `INL v'` >> fs[bind_def]) >>
  `value_has_type (BaseTV (BytesT (Dynamic n))) v'` by
    (irule (cj 3 expr_body_pre_base_result) >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `ee'` >> fs[bind_def]) >>
  `body_exprs_mem_ok cx kws` by
    (qpat_x_assum `bind _ _ (ee with gas_obs := gs') = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     fs[body_exprs_mem_ok_def] >> metis_tac[]) >>
  Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`gs`,`gs'`] >> simp[] >> decide_tac
QED

Finalise raw_call_addr_data_sim_mem

(* The header run's S1 endpoint is also the endpoint of the counted memory run. *)
Theorem raw_call_data_endpoint_mem[local]:
  expr_post ctx func cenv cx d es1 s1 s2 ta es2 (BytesV bs) data td /\
  expr_type d = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type d) (BytesV bs) data td /\
  expr_val_rel cx (BaseT AddressT) av addr td /\
  (!x. addr = Var x \/ data = Var x ==> not_fresh_at s2 x) /\
  (!l. addr <> Label l) /\ local_ptrs_reserved cenv s2 /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr_op,s4) /\
  fn_has_code s2 s4 func /\ fn_inst_ids_distinct func /\
  alloca_history func td /\ ~td.vs_halted /\
  td.vs_current_bb = s2.cs_current_bb /\
  td.vs_inst_idx = LENGTH s2.cs_current_insts ==>
  ?u b. run_inst_seq (emitted_insts s2 s4) td = OK u /\
    gas_path_mem ctx func td 0 (OK (u with vs_inst_idx := LENGTH s4.cs_current_insts)) /\
    alloca_history func (u with vs_inst_idx := LENGTH s4.cs_current_insts) /\
    expr_val_rel cx (BaseT AddressT) av addr u /\
    eval_operand data td = SOME (n2w b) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op u = SOME (n2w (b+32)) /\
    mem_bytes_at (b+32) (LENGTH bs) u.vs_memory = bs /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    b+32+LENGTH bs <= u.vs_alloca_next /\
    u.vs_alloca_next = td.vs_alloca_next /\
    u.vs_memory = td.vs_memory /\ u.vs_allocas = td.vs_allocas /\
    (u with vs_vars := td.vs_vars) = td /\
    stmt_state_rel ctx func cenv cx es2 u /\ wb_frame cenv es2 s2 td u /\
    ~u.vs_halted /\ u.vs_current_bb = s4.cs_current_bb /\
    (!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> not_fresh_at s4 x)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es2 td` by fs[expr_post_def] >>
  `alloca_inv td` by fs[stmt_state_rel_def] >>
  `td.vs_alloca_next <= td.vs_alloca_next` by simp[] >>
  `?b. eval_operand data td = SOME (n2w b) /\
       mem_word_at b td.vs_memory = n2w (LENGTH bs) /\
       b + 32 + LENGTH bs < dimword (:256) /\
       b + 32 + LENGTH bs <= td.vs_alloca_next` by
    (drule_all raw_call_input_bounds >> strip_tac >>
     qexists_tac `b` >> simp[] >> decide_tac) >>
  drule_all raw_call_addr_data_post >> strip_tac >>
  `b = b'` by
    (`b < dimword (:256) /\ b' < dimword (:256)` by decide_tac >>
     fs[wordsTheory.n2w_11]) >>
  qpat_x_assum `b = b'` SUBST_ALL_TAC >> suspend "counted"
QED

Resume raw_call_data_endpoint_mem[counted]:
  `!x. data = Var x ==> not_fresh_at s2 x` by simp[] >>
  `b' < dimword (:256) /\ b' + 32 <= td.vs_alloca_next` by decide_tac >>
  drule_all raw_call_data_prefix_counted_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  gvs[] >>
  `t.vs_alloca_next = td.vs_alloca_next` by
    (qpat_x_assum `_ with vs_vars := _ = td`
       (mp_tac o Q.AP_TERM `\s. s.vs_alloca_next`) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `_ with vs_vars := _ = td`
       (mp_tac o Q.AP_TERM `\s. s.vs_halted`) >> simp[]) >>
  qexists_tac `b'` >>
  `b' + 32 < dimword (:256)` by decide_tac >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise raw_call_data_endpoint_mem

Theorem raw_call_kwargs_ready_mem[local]:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx kws /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es ==>
  typed_args_ready_mem ctx func cenv cx (K (BaseT (UintT 256)))
    (expr_sim_inv cenv cx env) kws
Proof
  strip_tac >> drule raw_call_pre_flags >> strip_tac >>
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  irule typed_args_ready_mem_of_body >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule expr_body_pre_raw_call_arg >>
      qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
        (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  fs[listTheory.EVERY_MEM, is_word_type_def]
QED
