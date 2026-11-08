(* Memory-mode address and bytes argument continuation for raw_call. *)
Theory rawCallPrefixMemory
Ancestors
  bodyMemRawCallBounds rawCallGasMemory rawCallArgumentMemory exprSimRawCall exprSimHash bodyMemoryPreds exprSimMemDefs
  exprSimDefs exprSimProps exprLoweringProps loweringPosts bodySim
  compileEnv venomState vyperInterpreter vyperState fragExec exprSimSource exprSimHypsDefs
  bodyArgsMemory exprSimWordArgs exprWordOperand exprSimOperands exprSimHyps
  exprOperandVar exprSafeOperand exprSimPrecompiles list
  vyperEvalExprPreservesScopesDom

Theorem raw_call_addr_data_sim_mem[local]:
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

Theorem raw_call_prefix_sim_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr_op,s4) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
    ((vo,go,ignored),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  fn_has_code sa s6 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gsA av esA tA gsD bs esD tD gsK kvs esK tm tk t xs b gw.
    bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) =
      (INL av,esA) /\ esA.gas_obs = [] /\
    expr_post ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
      (INL (BytesV bs),esD) /\ esD.gas_obs = [] /\
    expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
    esK.gas_obs = [] /\ expr_sim_inv cenv cx env esK /\
    typed_args_post ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
    vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
    go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored = NONE /\
    expr_val_rel cx (BaseT AddressT) av addr t /\
    (!op w. MEM op xs /\ eval_operand op tk = SOME w ==>
       eval_operand op t = SOME w) /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op t = SOME (n2w (b+32)) /\
    eval_operand gas t = SOME gw /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    stmt_state_rel ctx func cenv cx esK t /\ wb_frame cenv es sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
    t.vs_inst_idx = LENGTH s6.cs_current_insts /\
    (!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/
         MEM (Var x) xs ==> not_fresh_at s6 x) /\
    safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 ptr_op /\
    safe_operand s6 gas /\ safe_operand s6
      (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    b+32+LENGTH bs <= t.vs_alloca_next ==>
    gas_outcome T (cx_tops cx) (ctx,func) (k av (BytesV bs) kvs) (esK,t) Q R) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (\dv.
     bind (eval_exprs cx kws) (k av dv)))) (es,s0) Q R
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa s4` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  drule raw_call_pre_flags >> strip_tac >>
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by fs[] >>
  drule_all raw_call_kwargs_word_args >> strip_tac >>
  qspecl_then [`kws`, `cenv`, `K (BaseT (UintT 256))`] mp_tac lower_word_args_shape >>
  (impl_tac
   >- (rpt strip_tac >>
       `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
       `MEM e (a::d::kws)` by simp[] >>
       `expr_body_pre cenv cx env e es` by
         (drule_all expr_body_pre_raw_call_arg >> simp[]) >>
       `is_word_type (expr_type e)` by fs[listTheory.EVERY_MEM, is_word_type_def] >>
       drule_all expr_body_pre_lower_value_word_shape >> simp[])) >>
  disch_then drule >> strip_tac >>
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND] >> simp[ci_mono_refl]) >>
  `cs_extends s4 s6` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s2 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  ho_match_mp_tac raw_call_addr_data_sim_mem >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ a sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ d s1 = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "data"
QED

Resume raw_call_prefix_sim_mem[data]:
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `expr_type a = BaseT AddressT /\
   ?cap. expr_type d = BaseT (BytesT (Dynamic cap))` by
    (drule raw_call_pre_operands >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[expr_body_pre_def]) >>
  `safe_operand s1 addr` by
    (irule lower_value_word_safe_operand >>
     first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     qexists_tac `env` >>
     drule_at (Pat `expr_body_pre _ _ _ a _`) expr_body_pre_var_types_well_formed >>
     fs[expr_body_pre_def, is_word_type_def]) >>
  `(!x. addr = Var x ==> not_fresh_at s1 x) /\ (!l. addr <> Label l)` by
    fs[safe_operand_def] >>
  drule_all expr_post_operand_word >> strip_tac >>
  `expr_val_rel cx (BaseT AddressT) av addr tD` by
    (fs[expr_post_def, expr_val_rel_def] >>
     gvs[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  `expr_body_pre cenv cx env d esD` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `!x. addr = Var x \/ data = Var x ==> not_fresh_at s2 x` by
    (rpt strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `s1` >> fs[ci_mono_def]) >>
     metis_tac[compile_lower_value_var]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  suspend "header"
QED

Resume raw_call_prefix_sim_mem[header]:
  `cs_extends s2 s4` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s4 func /\ fn_has_code s4 s6 func` by
    metis_tac[fn_has_code_split] >>
  `cs_extends sa s2` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s2 s4 func` by metis_tac[fn_has_code_split] >>
  drule_all raw_call_data_endpoint_mem >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func tD 0 (OK tm)` >>
  irule raw_call_implicit_mem_suffix >>
  simp[] >> qexistsl_tac [`0`, `tm`] >> simp[] >>
  suspend "keyword_setup"
QED

Resume raw_call_prefix_sim_mem[keyword_setup]:
  drule_all raw_call_kwargs_ready_mem >>
  disch_then (qspec_then `func` assume_tac) >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `esD`] >>
     simp[] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (irule expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, is_word_type_def]) >>
  `local_ptrs_reserved cenv s4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `fn_has_code s4 s5 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `stmt_state_rel ctx func cenv cx esD tm /\ ~tm.vs_halted /\
   tm.vs_current_bb = s4.cs_current_bb /\
   tm.vs_inst_idx = LENGTH s4.cs_current_insts` by
    simp[Abbr `tm`, stmt_state_rel_inst_idx] >>
  irule raw_call_kwargs_mem_bind >>
  qpat_assum `typed_args_ready_mem _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> fs[wb_args_exit_def] >> metis_tac[]) >>
  rpt strip_tac >> suspend "keyword_endpoint"
QED

Resume raw_call_prefix_sim_mem[keyword_endpoint]:
  `expr_sim_inv cenv cx env (esD with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all typed_args_ready_mem_inv >> simp[]) >>
  `b < dimword (:256)` by decide_tac >>
  `!x. data = Var x ==> not_fresh_at s2 x` by simp[] >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data tm /\
   eval_operand data tm = SOME (n2w b)` by
    (simp[Abbr `tm`] >> drule_all raw_call_data_slice_placement >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH bs) tm.vs_memory = bs` by fs[Abbr `tm`] >>
  `s2.cs_next_id <= s4.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by
    (qpat_x_assum `evaluate_type _ (expr_type d) = _` mp_tac >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs` by
    (drule_all raw_call_kwargs_payload >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv esD s4 tm t` by
    fs[typed_args_post_def] >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s4` >> simp[]) >>
  `!g. go = SOME g ==> ?w. eval_operand g t = SOME w` by
    (rpt strip_tac >>
     `MEM g xs` by metis_tac[raw_call_kwarg_mem] >>
     qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[typed_args_post_def] >> strip_tac >>
     drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  drule_all raw_call_optional_gas_run >> strip_tac >>
  suspend "optional_path"
QED

Resume raw_call_prefix_sim_mem[optional_path]:
  `fn_has_code s5 s6 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  drule_all raw_call_optional_gas_counted_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `tf = t' with vs_inst_idx := LENGTH s6.cs_current_insts` >>
  irule raw_call_implicit_mem_suffix >> simp[] >>
  qexistsl_tac [`if IS_NONE go then 1 else 0`,`tf`] >> simp[Abbr `tf`] >>
  suspend "final_endpoint"
QED

Resume raw_call_prefix_sim_mem[final_endpoint]:
  `!x. not_fresh_at s4 x ==> not_fresh_at s5 x` by
    (fs[not_fresh_at_def] >> decide_tac) >>
  `!op w. (!x. op = Var x ==> not_fresh_at s4 x) /\
           (!l. op <> Label l) /\ eval_operand op tm = SOME w ==>
           eval_operand op t' = SOME w` by
    (qpat_x_assum `wb_frame cenv esD s4 tm t` mp_tac >>
     qpat_x_assum `wb_frame cenv ee s5 t t'` mp_tac >>
     qpat_x_assum `!x. not_fresh_at s4 x ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `op` >> gvs[eval_operand_def] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `!op w. MEM op xs /\ eval_operand op t = SOME w ==>
          eval_operand op t' = SOME w` by
    (qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `wb_frame cenv ee s5 t t'` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  suspend "frames"
QED

Resume raw_call_prefix_sim_mem[frames]:
  `MAP FDOM es.scopes = MAP FDOM esA.scopes` by
    (qpat_x_assum `bind (eval_expr cx a) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esA.scopes = MAP FDOM esD.scopes` by
    (qpat_x_assum `bind (eval_expr cx d) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esD.scopes = MAP FDOM ee.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `wb_frame cenv es sa s0 tA /\ wb_frame cenv esA s1 tA tD` by
    (qpat_x_assum `expr_post _ _ _ _ a _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `expr_post _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[expr_post_def, wb_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 tD` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`esA`,`s1`,`tA`] >> fs[ci_mono_def]) >>
  suspend "frame_slice"
QED

Resume raw_call_prefix_sim_mem[frame_slice]:
  `wb_frame cenv esD s2 tD tm` by
    (simp[Abbr `tm`, wb_frame_def, locals_kept_def, lookup_var_def] >>
     fs[wb_frame_def, locals_kept_def, lookup_var_def]) >>
  `wb_frame cenv es sa s0 tm` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`esD`,`s2`,`tD`] >> fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es sa s0 t` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`esD`,`s4`,`tm`] >> fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`ee`,`s5`,`t`] >> fs[ci_mono_def] >> decide_tac) >>
  suspend "pack"
QED

Resume raw_call_prefix_sim_mem[pack]:
  `safe_operand s3 len /\ safe_operand s4 ptr_op` by
    metis_tac[emit_op_safe_operand] >>
  `eval_operand len tm = SOME (n2w (LENGTH bs)) /\
   eval_operand ptr_op tm = SOME (n2w (b+32))` by
    simp[Abbr `tm`, eval_operand_def] >>
  `eval_operand len t' = SOME (n2w (LENGTH bs)) /\
   eval_operand ptr_op t' = SOME (n2w (b+32))` by
    (fs[safe_operand_def] >> metis_tac[]) >>
  `expr_val_rel cx (BaseT AddressT) av addr tm` by
    fs[Abbr `tm`, expr_val_rel_def, is_word_type_def, eval_operand_def] >>
  `expr_val_rel cx (BaseT AddressT) av addr t'` by
    (qpat_x_assum `expr_val_rel _ _ _ addr tm` mp_tac >>
     qpat_x_assum `!op w. (_ /\ _ /\ _) ==> _` mp_tac >>
     qpat_x_assum `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> _` mp_tac >>
     qpat_x_assum `!l. addr <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_val_rel_def, is_word_type_def] >> metis_tac[]) >>
  suspend "freshness"
QED

Resume raw_call_prefix_sim_mem[freshness]:
  `!x. gas = Var x ==> not_fresh_at s6 x` by
    (qpat_x_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
     qpat_x_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `ci_mono s5 s6` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `go` >> gvs[]
     >- metis_tac[emit_op_safe_operand, safe_operand_def] >>
     `MEM (Var x) xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/
       MEM (Var x) xs ==> not_fresh_at s6 x` by
    (qpat_x_assum `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> _` mp_tac >>
     qpat_x_assum `!x. gas = Var x ==> _` mp_tac >>
     qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `ci_mono s5 s6` mp_tac >>
     qpat_x_assum `s4.cs_next_var <= s5.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, not_fresh_at_def, ci_mono_def] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "safety"
QED

Resume raw_call_prefix_sim_mem[safety]:
  `!l. gas <> Label l` by
    (qpat_x_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
     qpat_x_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_x_assum `EVERY _ xs` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `go` >> gvs[]
     >- metis_tac[emit_op_safe_operand, safe_operand_def] >>
     `MEM (Label l) xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 ptr_op /\
   safe_operand s6 gas` by
    (qpat_x_assum `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/ _ ==> _` mp_tac >>
     qpat_x_assum `!l. addr <> Label l` mp_tac >>
     qpat_x_assum `safe_operand s3 len` mp_tac >>
     qpat_x_assum `safe_operand s4 ptr_op` mp_tac >>
     qpat_x_assum `!l. gas <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[safe_operand_def] >> metis_tac[]) >>
  `safe_operand s6 (case ext_call_kwarg EKValue flags.rcf_kws xs of
    NONE => Lit 0w | SOME v => v)` by
    (Cases_on `ext_call_kwarg EKValue flags.rcf_kws xs` >> simp[] >>
     `MEM x xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM, safe_operand_def] >> metis_tac[]) >>
  suspend "continuation"
QED

Resume raw_call_prefix_sim_mem[continuation]:
  `s0.vs_alloca_next <= t'.vs_alloca_next /\
   b+32+LENGTH bs <= t'.vs_alloca_next` by
    (fs[Abbr `tm`] >> decide_tac) >>
  qpat_x_assum `!gsA av esA tA gsD bs esD tD gsK kvs esK tm tk t xs b gw. _`
    irule >>
  simp[stmt_state_rel_inst_idx, eval_operand_def,
       expr_val_rel_def, is_word_type_def] >>
  conj_tac >- (qexists_tac `b` >> fs[]) >>
  conj_tac >- fs[expr_val_rel_def, is_word_type_def] >>
  conj_tac
  >- (qpat_x_assum `wb_frame cenv es sa s0 t'` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[wb_frame_def, locals_kept_def, lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`esA`,`esD`,`gsA`,`gsD`,`gs`,`tA`,`tD`,`t`,`tm`,`xs`] >>
  simp[] >> first_x_assum ACCEPT_TAC
QED

Finalise raw_call_prefix_sim_mem
