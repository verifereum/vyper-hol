(* Counted memory raw call followed by the joint pointer endpoint. *)
Theory bodyFullRawCallCall
Ancestors
  bodyFullRawCallCallFrame bodyFullRawCallCallOrigin bodyFullRawCallCallStorage
  exprSimRawCall exprSimRawCallCalldata emitHelperProps exprLoweringProps fragExec
  words finite_map pred_set list arithmetic emitHelper compileEnv venomState
  venomInst memLocDefs codegenRel contextCodegenRel venomExecSemantics bodyPtrDefs
  loweringStateRelDefs ptrDiscipline exprSafeOperand unitTransformDefs decoderGhostFramePtr
  memSafeRun instMemFrontier

Theorem raw_call_inst_mem_safe_at:
  eval_operand dp s = SOME (n2w ib) /\ eval_operand dl s = SOME (n2w len) /\
  eval_operand out s = SOME (n2w ro) /\
  IS_SOME (eval_operand gas s) /\ IS_SOME (eval_operand addr s) /\
  IS_SOME (eval_operand value s) /\
  ib < dimword (:256) /\ len < dimword (:256) /\
  ro < dimword (:256) /\ cap < dimword (:256) /\
  (len = 0 \/ ib + len <= s.vs_alloca_next \/
   ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= ib /\ ib + len <= w2n s.vs_fmp) /\
  (cap <> 0 ==> ro + cap <= s.vs_alloca_next) ==>
  mem_safe_step 0 ctx
    (mk_inst id (case kind of
      RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
      (if kind = RegularCall then [gas;addr;value;dp;dl;out;Lit (n2w cap)]
       else [gas;addr;dp;dl;out;Lit (n2w cap)]) [dst]) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_goalsub_abbrev_tac `mem_safe_step 0 ctx inst s` >>
  `source_memory_read_ranges inst s = [(ib,len)] /\
   source_memory_write_ranges inst s = [(ro,cap)] /\
   inst_dload_in_section inst s /\ inst.inst_opcode <> INVOKE /\
   inst.inst_opcode <> DALLOCA` by
    (qunabbrev_tac `inst` >> Cases_on `kind` >>
     fs[optionTheory.IS_SOME_EXISTS] >>
     simp[mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
          mem_read_ops_def, mem_write_ops_def, memory_range_of_operands_def,
          eval_operand_def, inst_dload_in_section_def, w2n_n2w]) >>
  simp[mem_safe_step_non_invoke, inst_mem_below_frontiers_def,
       inst_mem_below_frontier_def] >>
  metis_tac[]
QED

Triviality raw_call_written_taint:
  ((inst.inst_opcode = CALL /\ LENGTH inst.inst_operands = 7) \/
   (MEM inst.inst_opcode [STATICCALL; DELEGATECALL] /\
    LENGTH inst.inst_operands = 6)) /\
  source_memory_write_ranges inst s = [(dst,cap)] /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  (step_taint inst s u tn).t_mem =
    tn.t_mem DIFF {j | dst <= j /\ j < dst + LENGTH (TAKE cap u.vs_returndata)}
Proof
  strip_tac >>
  `new_site_bytes s u = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `written_taint tn inst s = {}` by
    (simp[written_taint_def] >>
     namedCases_on `inst.inst_operands` ["", "a rest"] >> gvs[] >>
     namedCases_on `rest` ["", "b rest2"] >> gvs[] >>
     namedCases_on `rest2` ["", "c rest3"] >> gvs[] >>
     Cases_on `rest3` >> gvs[]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def, range_bytes_def,
       LENGTH_TAKE_EQ, MIN_DEF, EXTENSION] >>
  Cases_on `cap < LENGTH u.vs_returndata` >>
  Cases_on `cap <= LENGTH u.vs_returndata` >> gvs[] >>
  `cap = LENGTH u.vs_returndata` by decide_tac >> simp[]
QED

Theorem raw_call_actual_call_mem_safe_full:
  emit_op (case call_ty of
    RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  inst = mk_inst sa.cs_next_id (case call_ty of
    RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)])
    [STRING #"%" (toString sa.cs_next_var)] /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if call_ty = RegularCall then val_word else 0w) =
    (case value_opt of NONE => 0 | SOME n => n) /\
  (call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
    gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G tn p s cap) /\
  mem_safe_step 0 ctx inst s /\
  (cap = 0 \/ lo <= w2n ro) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n ro) cap b sz) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      u.vs_memory = (write_memory_with_expansion (w2n ro)
        (TAKE cap outcome.co_returnData) s).vs_memory /\
      u.vs_returndata = outcome.co_returnData /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_fmp = s.vs_fmp /\
      (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s) /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
           (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),(step_prov PG G inst u),(step_taint inst s
             u tn)) /\
         ghost_inv_at D lo d cenv cx (SND (adopt_call_outcome rq outcome es1)) (step_prov PG G inst u)
           (step_taint inst s u tn) (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
         ghost_kept_at lo cenv es sa G tn s (step_prov PG G inst u) (step_taint inst s u tn) /\
         eval_operand ok (u with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (bool_to_word
           outcome.co_success) /\
         op_taint (step_taint inst s u tn) ok = {} /\ op_prov (step_prov PG G inst u) ok = NONE /\
         (step_taint inst s u tn).t_mem = tn.t_mem DIFF
           {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap outcome.co_returnData)}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w cap : bytes32) = cap` by simp[w2n_n2w] >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + cap <= b` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name b sz. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[regions_disjoint_def, DISJ_COMM]) >>
  qpat_x_assum `inst = _` (mk_asm "call_inst") >>
  qpat_x_assum `w2w aw = target` (SUBST_ALL_TAC o SYM) >>
  drule raw_call_kind_oracle_emit_run_aged >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand gas_op s = _`)) >>
  disch_then (drule_at (Pat `eval_operand val_op s = _`)) >>
  disch_then (qspecl_then [`gas`,`aw`] mp_tac) >>
  simp[] >>
  (impl_tac >- (conj_tac >> rpt strip_tac >> res_tac >> decide_tac)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK u` >>
  asm_x "call_inst" assume_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule fn_has_code_same_block >>
     disch_then (qspec_then `[inst]` mp_tac) >> simp[] >>
     metis_tac[ADD_0, EL, prim_recTheory.LESS_0]) >>
  `t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t = _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >> simp[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_fmp = s.vs_fmp /\ u.vs_immutables = s.vs_immutables /\
   u.vs_memory = (write_memory_with_expansion (w2n ro)
     (TAKE cap outcome.co_returnData) s).vs_memory /\
   u.vs_returndata = outcome.co_returnData` by simp[Abbr `u`,update_var_def] >>
  `inst.inst_opcode = (case call_ty of
     RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL) /\
   inst.inst_operands =
     (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
      else [gas_op;to_op;dp;dl;op;Lit (n2w cap)]) /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by simp[mk_inst_def] >>
  `source_memory_write_ranges inst s = [(w2n ro,cap)] /\
   source_memory_read_ranges inst s = [(w2n ao,w2n az)]` by
    (Cases_on `call_ty` >>
     simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
          mem_write_ops_def, mem_read_ops_def, memory_range_of_operands_def,
          eval_operand_def]) >>
  suspend "ghost"
QED

Resume raw_call_actual_call_mem_safe_full[ghost]:
  `(if call_ty = DelegateCall then exec_delegatecall inst s gas aw ao az ro (n2w cap : bytes32)
    else exec_ext_call inst s gas aw (if call_ty = RegularCall then val_word else 0w)
      ao az ro (n2w cap : bytes32) (call_ty = StaticCall \/ s.vs_call_ctx.cc_static)) = OK u` by
    (qpat_assum `inst.inst_opcode = _` mp_tac >>
     qpat_assum `inst.inst_operands = _` mp_tac >>
     qpat_assum `step_inst_base inst s = OK u` mp_tac >>
     map_every (fn pattern => qpat_assum pattern mp_tac)
       [`eval_operand gas_op s = SOME gas`, `eval_operand to_op s = SOME aw`,
        `eval_operand dp s = SOME ao`, `eval_operand dl s = SOME az`,
        `eval_operand op s = SOME ro`, `eval_operand val_op s = SOME val_word`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `call_ty` >> simp[] >> rpt strip_tac >>
     qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
     qpat_assum `inst.inst_opcode = _` (fn eq =>
       let val th = valOf (List.find (fn th =>
         let val (_,body) = strip_forall (concl th)
         in aconv (rhs (fst (dest_imp body))) (rhs (concl eq)) end)
         (CONJUNCTS step_inst_base_opcode_eqs))
       in PURE_ONCE_REWRITE_TAC [MATCH_MP th eq] end) >>
     simp[eval_operand_def] >>
     TRY (IF_CASES_TAC >> simp[NoAsms]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `stor_taint_ok_at D tn s` by
    (qpat_assum `ghost_inv_at D lo d cenv cx es G tn s` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  `stor_taint_ok_at D (step_taint inst s u tn) u` by
    (Cases_on `call_ty` >>
     qpat_x_assum `(if _ then exec_delegatecall _ _ _ _ _ _ _ _ else _) = _`
       (assume_tac o SRULE []) >>
     qpat_x_assum `inst.inst_opcode = _` (assume_tac o SRULE []) >>
     FIRST [drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`)
              raw_call_exec_stor_taint_at,
            drule_at (Pat `exec_delegatecall _ _ _ _ _ _ _ _ = _`)
              raw_delegate_call_exec_stor_taint_at] >>
     disch_then (qspecl_then [`tn`,`D`] mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP (step_prov PG G inst u) x = FLOOKUP G x /\
    op_taint (step_taint inst s u tn) (Var x) = op_taint tn (Var x) /\
    lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x s` by
    (gen_tac >> strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var)` by fs[not_fresh_at_def] >>
     conj_tac >- (irule step_prov_other_output >> simp[]) >>
     conj_tac >- (irule step_taint_other_output >> simp[]) >>
     simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `(step_taint inst s u tn).t_mem = tn.t_mem DIFF
    {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap outcome.co_returnData)}` by
    (qpat_assum `u.vs_returndata = _` (fn th => REWRITE_TAC[GSYM th]) >>
     irule raw_call_written_taint >> Cases_on `call_ty` >> simp[]) >>
  qexists `u` >> simp_tac bool_ss [LET_THM] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "safe"
  >- suspend "origin"
  >- suspend "frame"
  >- suspend "kept"
  >- suspend "taint"
  >- suspend "prov"
  >> simp[]
QED

Resume raw_call_actual_call_mem_safe_full[safe]:
  Cases >> simp[safe_operand_def, eval_operand_def] >>
  rpt strip_tac >>
  rename1 `lookup_var x u = lookup_var x s` >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by fs[not_fresh_at_def] >>
  simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Resume raw_call_actual_call_mem_safe_full[origin]:
  qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o SRULE [ghost_inv_at_def]) >>
  let
    val operands = [`bb` |-> `bb`, `ao` |-> `ao`, `az` |-> `az`,
      `dl` |-> `dl`, `dp` |-> `dp`, `gas_op` |-> `gas_op`, `op` |-> `op`,
      `rn` |-> `(n2w cap : bytes32)`, `ro` |-> `ro`, `rz` |-> `Lit (n2w cap)`,
      `to_op` |-> `to_op`]
    val ordinary = Q.INST ((`val_op` |-> `val_op`) :: operands) raw_call_step_mem_safe_origin_full
    val delegate = Q.INST operands raw_delegate_call_step_mem_safe_origin_full
    fun close rule =
      mp_tac rule >> impl_tac
      >- (qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts` (fn index =>
           qpat_assum `get_instruction bb s.vs_inst_idx = SOME inst` (fn fetch =>
             simp[eval_operand_def, fetch, REWRITE_RULE [index] fetch]))) >>
      disch_then ACCEPT_TAC
  in
    (Cases_on `call_ty` >>
     qpat_x_assum `inst.inst_opcode = _` (assume_tac o SRULE []) >>
     qpat_x_assum `inst.inst_operands = _` (assume_tac o SRULE [])) THENL
      [close ordinary, close delegate, close ordinary]
  end
QED

Resume raw_call_actual_call_mem_safe_full[frame]:
  drule raw_call_kind_take_adopt_fields >> strip_tac >>
  irule raw_call_clean_write_ghost_at >>
  conj_tac >-
    (qpat_x_assum `stor_taint_ok_at _ _ _` mp_tac >>
     simp[stor_taint_ok_at_def]) >>
  qexistsl [`G`,`TAKE cap outcome.co_returnData`,`w2n ro`,`es`,`func`,`s`,`sa`,`tn`] >>
  simp[] >>
  reverse conj_tac >-
    (qpat_x_assum `cap = 0 \/ lo <= _` mp_tac >> metis_tac[TAKE_0]) >>
  rpt strip_tac >>
  qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _` drule >>
  simp[regions_disjoint_def, LENGTH_TAKE_EQ] >>
  Cases_on `cap <= LENGTH outcome.co_returnData` >> simp[]
QED

Resume raw_call_actual_call_mem_safe_full[kept]:
  simp[ghost_kept_at_def]
QED

Resume raw_call_actual_call_mem_safe_full[taint]:
  Cases_on `call_ty` >>
  simp[step_taint_def, op_taint_def, set_var_taint_def,
       out_taint_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Resume raw_call_actual_call_mem_safe_full[prov]:
  qpat_assum `ok = _` (fn th => rewrite_tac[th]) >>
  irule step_prov_out_none >>
  Cases_on `call_ty` >> simp[out_prov_def]
QED

Finalise raw_call_actual_call_mem_safe_full

Theorem raw_call_actual_call_full:
  emit_op (case call_ty of
    RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  inst = mk_inst sa.cs_next_id (case call_ty of
    RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)])
    [STRING #"%" (toString sa.cs_next_var)] /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if call_ty = RegularCall then val_word else 0w) =
    (case value_opt of NONE => 0 | SOME n => n) /\
  (call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
    gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G tn p s cap) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (cap = 0 \/ w2n ro + cap <= s.vs_alloca_next) /\
  (cap = 0 \/ lo <= w2n ro) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n ro) cap b sz) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      u.vs_memory = (write_memory_with_expansion (w2n ro)
        (TAKE cap outcome.co_returnData) s).vs_memory /\
      u.vs_returndata = outcome.co_returnData /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_fmp = s.vs_fmp /\
      (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s) /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
           (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),(step_prov PG G inst u),(step_taint inst s
             u tn)) /\
         ghost_inv_at D lo d cenv cx (SND (adopt_call_outcome rq outcome es1)) (step_prov PG G inst u)
           (step_taint inst s u tn) (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
         ghost_kept_at lo cenv es sa G tn s (step_prov PG G inst u) (step_taint inst s u tn) /\
         eval_operand ok (u with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (bool_to_word
           outcome.co_success) /\
         op_taint (step_taint inst s u tn) ok = {} /\ op_prov (step_prov PG G inst u) ok = NONE /\
         (step_taint inst s u tn).t_mem = tn.t_mem DIFF
           {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap outcome.co_returnData)}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `call_ty` >> simp[mk_inst_def]) >>
  `inst_dload_in_section inst s` by
    (Cases_on `call_ty` >> simp[mk_inst_def, inst_dload_in_section_def]) >>
  `source_memory_write_ranges inst s = [(w2n ro,cap)] /\
   source_memory_read_ranges inst s = [(w2n ao,w2n az)]` by
    (Cases_on `call_ty` >>
     simp[mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
          mem_write_ops_def, mem_read_ops_def, memory_range_of_operands_def,
          eval_operand_def, w2n_n2w]) >>
  `inst_mem_below_frontier inst s` by
    (fs[inst_mem_below_frontier_def, w2n_eq_0]) >>
  `mem_safe_step 0 ctx inst s` by
    (Cases_on `call_ty` >> simp[mem_safe_step_non_invoke, mk_inst_def]) >>
  mp_tac raw_call_actual_call_mem_safe_full >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
