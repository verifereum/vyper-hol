(* Discharge the semantic interfaces for the one specified actual call. *)
Theory bodyFullRawCallCall
Ancestors
  bodyFullRawCallCallPrepare bodyFullRawCallCallOrigin bodyFullRawCallCallFrame

Theorem raw_call_actual_call_full:
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
  (stat \/ s.vs_call_ctx.cc_static) = IS_NONE value_opt /\
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
  mp_tac raw_call_actual_call_from_interfaces >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_step_origin_full)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_clean_write_ghost_at)) >>
  disch_then MATCH_ACCEPT_TAC
QED
