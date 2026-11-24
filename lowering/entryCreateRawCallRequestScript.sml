(* Confine the actual request step before composing the return suffix. *)
Theory entryCreateRawCallRequest
Ancestors
  bodyFullRawCall entryCreateAdminSequence entryCreatePathScope entryCreateFocusSpec
  entryCreateCompletedCut gasOutcomeFullCompose exprLoweringProps
  fragGasOriginPtr fragGasOrigin fragExec venomInst venomState
  venomExecSemantics arithmetic gasStorage gasSummary vyperStorageFootprint
  abiEncoderProps fragExec exprSimDefs bodySimFull bodyPtrDefs ptrDiscipline
  exprSimHyps exprSimSource memLocDefs words bodyFullPreds

Theorem raw_call_request_step_scope:
  emit_op opc ops sa = (ok,sc) /\ MEM opc [CALL;STATICCALL;DELEGATECALL] /\
  fn_has_code sa sc func /\ create_operand_at sa s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sc) s = OK u ==>
  create_operand_full_scope sa sc explicit ctx func s []
    (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts))
Proof
  strip_tac >> irule create_admin_sequence_scope >> simp[] >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  fs[same_blocks_def,abiEncoderPropsTheory.frag_ids_def,mk_inst_def,is_terminator_def]
QED

Theorem raw_call_request_abort_scope:
  ~create_operand_at sb s /\ exit_result r /\
  gas_origin_edge T explicit ctx func s [] r ==>
  create_operand_full_scope sa sb explicit ctx func s [] r
Proof
  strip_tac >> irule (Q.INST [`left` |-> `[]`,`last` |-> `[]`]
    (SPEC_ALL create_operand_full_scope_terminal) |> SIMP_RULE (srw_ss()) []) >>
  conj_tac >- simp[] >> qexists_tac `s` >> fs[create_operand_at_def]
QED

(* Interpret the observed result at its original physical and ghost endpoint.
   If the source leaves the domain there is no request witness to transport. *)
Theorem raw_call_observed_scoped[local]:
  raw_call_observed_outcome
    (create_operand_full_scope sa sb E C f s []) (DF,lo,E,C,f,PG) cx st0
    source (es,s,G,tn) Q R ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sb
    source (es,s,G,tn) Q R
Proof
  rewrite_tac[raw_call_observed_outcome_def, scoped_operand_outcome_def] >>
  strip_tac >> qexists_tac `[]`
  >- (disj1_tac >> conj_tac >- simp[gas_bad_storage_at_def,gas_explicit_def] >>
      conj_tac >- (simp[create_operand_focus_scope_def] >> qexists_tac `s` >> simp[]) >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`,`f`,`PG`,`G`,`tn`,`s`] >>
      simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil,storage_trace_domain_def]) >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`ee`,`r`,`Gf`,`tnf`] >> simp[gas_explicit_def]
QED

Theorem raw_call_request_prepend[local]:
  create_operand_at s7 t7 /\ ~t7.vs_halted /\
  s7.cs_next_id < sb.cs_next_id /\
  (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
          i.inst_id <> s7.cs_next_id) /\
  emit_op opc ops s7 = (ok,sc) /\ MEM opc [CALL;STATICCALL;DELEGATECALL] /\
  fn_has_code s7 sc func /\ run_inst_seq (emitted_insts s7 sc) t7 = OK u /\
  create_operand_full_scope sc sb E ctx func
    (u with vs_inst_idx := LENGTH sc.cs_current_insts) [] r ==>
  create_operand_full_scope s7 sb E ctx func t7 [] r
Proof
  strip_tac >> drule_all raw_call_request_step_scope >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  irule (SIMP_RULE bool_ss [listTheory.APPEND]
    (Q.INST [`left` |-> `[]`,`right` |-> `[]`] create_operand_full_scope_prepend)) >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >>
  simp[frag_ids_def] >> rpt strip_tac >> res_tac >> decide_tac
QED

(* The installed request is strictly inside the interval. The post-call
   supplier supplies scope on the same result as its all-horizon post. *)
Theorem raw_call_continuation_scoped:
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = raw_call_return_type flags /\ type_alloc_ok cenv (expr_type e) /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\
  (flags.rcf_is_static ==> amount = 0) /\
  amount < dimword (:256) /\ flags.rcf_max_outsize < dimword (:256) /\
  expr_sim_inv cenv cx env esK /\ esK.gas_obs = [] /\
  storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),sout) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vv = (if flags.rcf_max_outsize = 0
        then StackValue (raw_call_return_type flags) result
        else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esK t7 /\
    storage_well_formed_on cx esK (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7) /\
  return_buf_frame dframe cenv sa t7 /\
  wb_frame cenv es esK sa s0 t7 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
  ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
  t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
  s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
  eval_operand addr t7 = SOME (w2w target) /\
  eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p) t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
       g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\
   w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH bs) t7 = bs /\
  (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  eval_operand ov t7 = SOME (n2w ob) /\
  eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob + 32)) /\
  (flags.rcf_max_outsize = 0 ==> ov = op) /\
  ob + (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256) /\
  FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_prov G7 ov = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_prov G7 op = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
    regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) lb sz) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  EVERY (\x. op_taint tn7 x = {})
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p)] /\
  EVERY (safe_operand s7)
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p);ov;op] /\
  (!x. MEM (Var x)
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p);ov;op] ==> not_fresh_at s7 x) /\
  ~create_operand_at sb t7 /\ s7.cs_next_id < sb.cs_next_id /\
  (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
          i.inst_id <> s7.cs_next_id) /\
  raw_call_finish_rule (\sc sb E C f s r. create_operand_full_scope sc sb E C f s [] r)
  ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 s7 sb
    (eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs))
    (esK,t7,G7,tn7)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
        ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
           ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee (Value v) vv t /\
           (!t' p. vv = LocatedValue t' p ==>
                   p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val, ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                      SOME rt /\
                    eval_operand (vv_operand vv) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\
               ~is_word_type (post_value_type cenv e) ==>
               ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r.
      expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_operand_at s7 t7` by simp[create_operand_at_def] >>
  `!r. exit_result r /\ gas_origin_edge T (gas_explicit_sites ctx shadow_ctx) ctx func t7 [] r ==>
       create_operand_full_scope s7 sb (gas_explicit_sites ctx shadow_ctx) ctx func t7 [] r` by
    (rpt strip_tac >> irule raw_call_request_abort_scope >> simp[]) >>
  `!opc ops ok sc u r.
      emit_op opc ops s7 = (ok,sc) /\ MEM opc [CALL;STATICCALL;DELEGATECALL] /\
      fn_has_code s7 sc func /\ run_inst_seq (emitted_insts s7 sc) t7 = OK u /\
      create_operand_full_scope sc sb (gas_explicit_sites ctx shadow_ctx) ctx func
        (u with vs_inst_idx := LENGTH sc.cs_current_insts) [] r ==>
      create_operand_full_scope s7 sb (gas_explicit_sites ctx shadow_ctx) ctx func t7 [] r` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule raw_call_request_prepend >>
     first_assum (irule_at Any) >> first_assum (irule_at Any) >>
     qexistsl_tac [`ops`,`opc`,`ok`] >> simp[]) >>
  irule raw_call_observed_scoped >>
  irule (BETA_RULE (Q.INST
    [`finish_ok` |-> `\sc sb E C f s r. create_operand_full_scope sc sb E C f s [] r`,
     `accept` |-> `create_operand_full_scope s7 sb (gas_explicit_sites ctx shadow_ctx) ctx func t7 []`]
    raw_call_continuation_observed)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `~(_ /\ _)` (ACCEPT_TAC o REWRITE_RULE [DE_MORGAN_THM])) >>
  ((qexistsl_tac [`addr`,`dp`,`gas`,`gw`,`ib`,`len`,`ob`,`op`,`ov`,`result`,
                  `s6`,`sout`,`xs`] >> rpt conj_tac >> first_assum ACCEPT_TAC)
   ORELSE (qexists_tac `env` >> rpt conj_tac >> first_assum ACCEPT_TAC))
QED
