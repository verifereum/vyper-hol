(* Operational assembly for the specified actual call.  The two semantic
   interfaces are ordinary universally quantified premises, not suppliers. *)
Theory bodyFullRawCallCallPrepare
Ancestors
  rawCallMemoryFramePtr oracleCallStepPtr bodyFullRawCallCallStorage
  emitHelperProps exprLoweringProps fragExec words finite_map pred_set list arithmetic
  emitHelper compileEnv venomState venomInst memLocDefs unitTransformDefs codegenRel contextCodegenRel
  venomCallOracleDefs venomExecSemantics bodyPtrDefs loweringStateRelDefs decoderGhostFramePtr ptrDiscipline exprSafeOperand

Theorem raw_call_actual_call_from_interfaces:
  (!inst gas_op to_op val_op dp dl op rz s ao az ro rn G tn lo D ctx
      func bb u explicit PG.
    ((inst.inst_opcode = CALL /\
      inst.inst_operands = [gas_op;to_op;val_op;dp;dl;op;rz]) \/
     (inst.inst_opcode = STATICCALL /\
      inst.inst_operands = [gas_op;to_op;dp;dl;op;rz])) /\
    eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
    eval_operand op s = SOME ro /\ eval_operand rz s = SOME rn /\
    (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
    (rn <> 0w ==> ?p. op = Var p /\ ptr_covers G tn p s (w2n rn)) /\
    EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
    allocas_from lo s /\ stor_taint_ok_at D tn s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    inst_mem_below_frontier inst s /\
    ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst_base inst s = OK u ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G inst u, step_taint inst s u tn)) ==>
  (!D lo d cenv cx es G tn s func sa HG un u ee dst bytes.
    ghost_inv_at D lo d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP HG x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x) /\
      lookup_var x u = lookup_var x s) /\
    ee.scopes = es.scopes /\
    u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
    un.t_mem = tn.t_mem DIFF {i | dst <= i /\ i < dst + LENGTH bytes} /\
    (bytes = [] \/ lo <= dst) /\
    (!name a len. local_region cenv es.scopes s name a len ==>
      regions_disjoint dst (LENGTH bytes) a len) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    stor_taint_ok_at D un u ==>
    ghost_inv_at D lo d cenv cx ee HG un u) ==>
  !stat gas_op to_op dp dl op cap val_op sa ok sb inst s u func cenv es ctx
    gas aw ao az ro val_word target value_opt rq outcome es1 t tn G PG D lo d cx explicit.
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  inst = mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)])
    [STRING #"%" (toString sa.cs_next_var)] /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  u = update_var (STRING #"%" (toString sa.cs_next_var))
    (bool_to_word outcome.co_success) t /\
  t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
    vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
    vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
    vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
  t.vs_memory = (write_memory_with_expansion (w2n ro)
    (TAKE cap outcome.co_returnData) s).vs_memory /\
  t.vs_returndata = outcome.co_returnData /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G tn p s cap) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (cap = 0 \/ w2n ro + cap <= s.vs_alloca_next) /\
  (cap = 0 \/ lo <= w2n ro) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n ro) cap b sz) /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  let HG = step_prov PG G inst u;
      un = step_taint inst s u tn
  in gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),HG,un) /\
     ghost_inv_at D lo d cenv cx (SND (adopt_call_outcome rq outcome es1)) HG un
       (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
     ghost_kept_at lo cenv es sa G tn s HG un /\
     eval_operand ok (u with vs_inst_idx := LENGTH sb.cs_current_insts) =
       SOME (bool_to_word outcome.co_success) /\
     op_taint un ok = {} /\ op_prov HG ok = NONE /\
     un.t_mem = tn.t_mem DIFF
       {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap outcome.co_returnData)} /\
     (!j. w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap outcome.co_returnData) ==>
       j NOTIN un.t_mem) /\
     (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s)
Proof
  disch_then (mk_asm "origin") >>
  disch_then (mk_asm "frame") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
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
   u.vs_returndata = outcome.co_returnData` by simp[update_var_def] >>
  `inst.inst_opcode = (if stat then STATICCALL else CALL) /\
   inst.inst_operands = (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
       else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by simp[mk_inst_def] >>
  `source_memory_write_ranges inst s = [(w2n ro,cap)] /\
   source_memory_read_ranges inst s = [(w2n ao,w2n az)]` by
    (Cases_on `stat` >>
     simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
          mem_write_ops_def, mem_read_ops_def, memory_range_of_operands_def,
          eval_operand_def, w2n_n2w]) >>
  `inst_mem_below_frontier inst s` by
    (simp[inst_mem_below_frontier_def] >>
     qpat_x_assum `w2n az = 0 \/ _` mp_tac >> simp[]) >>
  `exec_ext_call inst s gas aw (if stat then 0w else val_word)
      ao az ro (n2w cap : 256 word) stat = OK u` by
    (asm_x "origin" kall_tac >> asm_x "frame" kall_tac >>
     qpat_x_assum `t = _` kall_tac >>
     qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
     Cases_on `stat` >> Cases_on `s.vs_call_ctx.cc_static` >>
     Cases_on `val_word = 0w` >>
     simp[step_inst_base_opcode_eqs, eval_operand_def, w2n_eq_0] >>
     simp[exec_ext_call_def, venom_call_request_def]) >>
  `stor_taint_ok_at D (step_taint inst s u tn) u` by
    (drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`)
       raw_call_exec_stor_taint_at >>
     disch_then (qspecl_then [`tn`,`D`] mp_tac) >>
     impl_tac >- (Cases_on `stat` >> simp[] >>
       qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
       simp[ghost_inv_at_def]) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP (step_prov PG G inst u) x = FLOOKUP G x /\
    op_taint (step_taint inst s u tn) (Var x) = op_taint tn (Var x) /\
    lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x s` by
    (gen_tac >> strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var)` by
       fs[not_fresh_at_def] >>
     conj_tac >- (irule step_prov_other_output >> simp[]) >>
     conj_tac >- (irule step_taint_other_output >> simp[]) >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `(step_taint inst s u tn).t_mem = tn.t_mem DIFF
    {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap outcome.co_returnData)}` by
    (drule_at (Pat `source_memory_write_ranges _ _ = _`) oracle_call_write_taint >>
     disch_then (qspecl_then [`tn`,`u`] mp_tac) >>
     impl_tac >- (Cases_on `stat` >> simp[]) >> simp[]) >>
  pure_rewrite_tac[LET_THM] >>
  rpt conj_tac
  >- suspend "origin"
  >- suspend "frame"
  >- suspend "kept"
  >- suspend "status"
  >- suspend "taint"
  >- suspend "prov"
  >- simp[]
  >- simp[]
  >> suspend "safe"
QED

Resume raw_call_actual_call_from_interfaces[origin]:
  cheat
QED
Resume raw_call_actual_call_from_interfaces[frame]:
  cheat
QED
Resume raw_call_actual_call_from_interfaces[kept]:
  cheat
QED
Resume raw_call_actual_call_from_interfaces[status]:
  cheat
QED
Resume raw_call_actual_call_from_interfaces[taint]:
  cheat
QED
Resume raw_call_actual_call_from_interfaces[prov]:
  cheat
QED
Resume raw_call_actual_call_from_interfaces[safe]:
  cheat
QED

Finalise raw_call_actual_call_from_interfaces
