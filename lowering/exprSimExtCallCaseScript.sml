(*
 * Expression simulation: extcall and staticcall, as one case lemma
 *
 * extcall/staticcall in SOME oracle mode, including reverts and
 * default_return_value (#553).  The source evaluates the target, then the
 * positional arguments, each read as it is evaluated, then the keyword
 * operands; the hypotheses of
 * compile_extcall_case give the operands' judgments in that order, as the
 * body induction's hypotheses do (bodySimCallCases's body_extcall_case).
 * exprSimCallExtcall and bodySimCallExtcall derive the two piece theorems
 * from it.
 *
 * TOP-LEVEL:
 *   compile_extcall_case — extcall's expr_sim_case and expr_vv_case from
 *     its operands' judgments
 *
 * Why it holds: the call request agrees with the source's.  The selector is
 * cenv.ce_method_id, which expr_sim_inv pins to function_selector of the
 * declared ABI types; the calldata is the selector followed by the arguments
 * encoded at their own lowered types, at the encoded length (vyper#5127),
 * as build_ext_calldata sends; a storage, transient or immutable argument is
 * read at its own declared type (vyper#5239).  The extcodesize check and the
 * void result are keyed on return_type = NoneT on both sides, and typing
 * rules out default_return_value on a void call.  The call itself is an
 * oracle step (extCallOracleStep: venom_call_request_source,
 * exec_ext_call_oracle_step), as for send (exprSimSend).  A revert copies
 * the returndata and REVERTs; empty returndata with a default takes the
 * default after the code recheck; otherwise the returndata is decoded with
 * the bounded memory decoder.
 *)

Theory exprSimExtCallCase
Ancestors
  list rich_list loweringPosts supportedExprTraverse exprSimHypsDefs exprSimHyps vyperAST
  vyperInterpreter vyperState exprSimDefs
  extCallOracleStep rawCallMemoryFramePtr vyperCallOutcomeFrame vyperCallOutcome exprBopSimProps
  bodyIntCallJointPureSource exprCanMutateProps bodyFullExtCallRequestInterfaces
  bodyFullExtCallRequestSnapshot bodyFullExtCallRequestSnapshotWord valueCopyBytes
  vyperStorageTrace vyperStorageFootprint gasStorage gasOutcome gasSummary
  gasSummaryCompose aggregateCountedOutcome compileEnv emitHelper context
  venomExecSemantics venomState venomInst exprLoweringProps memoryReadProps
  fragGasSeq fragGasSeqAbort fragGasPath fragGasMode fragExec gasCount
  finite_map arithmetic
  extcallReturnCallerSuccess extcallReturnCallerReject extCallCodeCheck
  extcallReturnDefaultResources extcallReturnDefaultRouting extcallReturnDefaultStore
  extcallReturnDefaultDecode extcallReturnDefaultOwnership extcallReturnDefaultIntervals
  extcallReturnInterface extcallReturnDefaultTypes

(* A storage or transient pointer an effect-free operand leaves reads live
   slots at es': no byte of the slots it reads is dead but those its own
   type leaves dead (storage_read_live). *)
Theorem vv_post_storage_live:
  !ctx func cenv cx e es sa sb s0 es' tv vv s t p w tvt.
    vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ~expr_has_effect e /\
    vv = LocatedValue t p /\
    eval_operand p.ptr_operand s = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tvt ==>
    (p.ptr_location = LocStorage ==>
     storage_read_live H F (get_storage cx es' F) w tvt) /\
    (p.ptr_location = LocTransient ==>
     storage_read_live H T (get_storage cx es' T) w tvt)
Proof
  rpt strip_tac >> gvs[vv_post_def] >> metis_tac[]
QED

(* An effect-free expression's fragment keeps every live local whole and
   every window clear of its own allocations. *)
Theorem vv_post_pure_memory_frame:
  !ctx func cenv cx e es sa sb s0 es' tv vv s.
    vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
    (!off len.
       (!inst b sz.
          MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
          loweringStateRelDefs$regions_disjoint off len b sz) ==>
       mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `pure_frame cenv func es sa s0 s` by gvs[vv_post_def] >>
  pop_assum mp_tac >> rewrite_tac[pure_frame_def]
QED

(* Source boundary: each positional argument is read as it is evaluated,
   before the keyword operands. *)
Theorem eval_extcall_stages:
  eval_expr cx (Call ann (ExtCall static skip sig opts) args dflt) =
    do target <- eval_exprs cx (TAKE 1 args);
       vs <- eval_exprs cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 args));
       kwargs <- eval_exprs cx (DROP (1 + LENGTH (FST (SND sig))) args);
       eval_ext_call cx static skip sig opts (target ++ vs ++ kwargs)
    od
Proof
  simp[Once evaluate_def]
QED

(* ===== The split: request, call step, return ===== *)

(* The default operand of a call that has default_return_value: none on a
   void call; its type default_ty (the lowered type it is stored from) is
   the return type or, for bytestrings, another bytestring type; its value
   is typed at both; and, for a memory default, a region below the next
   alloca, so no later alloca overlaps it.
   has_default is the lowering's flag, default_opt the source's keyword
   value. *)
Definition extcall_default_ready_def:
  extcall_default_ready cx ret_type has_default default_op default_ty
      default_opt t <=>
    (has_default <=> IS_SOME default_opt) /\
    (ret_type = NoneT ==> ~has_default) /\
    !d. default_opt = SOME d ==>
        (default_ty = ret_type \/
         is_bytestring_type default_ty /\ is_bytestring_type ret_type) /\
        ?tv rtv w. evaluate_type (get_tenv cx) default_ty = SOME tv /\
               evaluate_type (get_tenv cx) ret_type = SOME rtv /\
               value_has_type tv d /\ val_wf tv d /\
               value_has_type rtv d /\ val_wf rtv d /\
               eval_operand default_op t = SOME w /\
               expr_val_rel cx default_ty d default_op t /\
               (~is_word_type default_ty ==>
                w2n w + val_footprint tv d <= t.vs_alloca_next)
End

(* At sp, just before the extcodesize check and the CALL: the source has
   evaluated and read every operand and built the request (target, value,
   calldata); the CALL's operands evaluate to them, calldata is the bytes
   at call_offset, and the return buffer (cap bytes at buf_op, an alloca
   made after sa) is clear of the locals, the immutables, the allocas before
   sa and a memory default. *)
Definition extcall_request_ready_def:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t <=>
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\
       storage_well_formed_on cx ee (FST H)) /\ wb_frame cenv es ee sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\ ee.gas_obs = [] /\
    outcomes_accounts_typed ee.outcomes /\
    accounts_runtime_well_typed ee.accounts /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id /\
    local_ptrs_reserved cenv sp /\
    EVERY (safe_operand sp)
      [addr_op; value_op; gas_op; buf_op; call_offset; call_len; default_op] /\
    (?aw. eval_operand addr_op t = SOME aw /\ w2w aw = target) /\
    (is_static <=> value_opt = NONE) /\
    (?vw. eval_operand value_op t = SOME vw /\
          w2n vw = (case value_opt of NONE => 0 | SOME n => n)) /\
    IS_SOME (eval_operand gas_op t) /\
    (?ao az. eval_operand call_offset t = SOME ao /\
             eval_operand call_len t = SOME az /\
             read_memory (w2n ao) (w2n az) t = calldata) /\
    (?ro. eval_operand buf_op t = SOME ro /\ w2n ro + cap < dimword (:256) /\
          (?live buf_size. sa.cs_next_id <= live /\ live < sp.cs_next_id /\
             cap <= buf_size /\
             FLOOKUP t.vs_allocas live = SOME (w2n ro, buf_size)) /\
          (!name b sz. local_region cenv ee.scopes t name b sz ==>
             loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) /\
          (!name b sz. local_region cenv es.scopes s0 name b sz ==>
             loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) /\
          (!aid b sz. aid < sa.cs_next_id /\
             FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
             loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) /\
          (cenv.ce_is_ctor ==> !name tv v off.
             FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
               SOME (ImmutableLoc off) /\
             FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
                        NONE => FEMPTY
                      | SOME imms => get_source_immutables cenv.ce_module imms)
               name = SOME (tv,v) ==>
             loweringStateRelDefs$regions_disjoint (w2n ro) cap off
               (type_memory_size tv)) /\
          (!d w tv. default_opt = SOME d /\ ~is_word_type default_ty /\
             eval_operand default_op t = SOME w /\
             evaluate_type (get_tenv cx) default_ty = SOME tv ==>
             loweringStateRelDefs$regions_disjoint (w2n ro) cap (w2n w)
               (val_footprint tv d))) /\
    extcall_default_ready cx ret_type has_default default_op default_ty
      default_opt t
End

(* At sr, the start of the block after a successful call: the source has
   the call's returndata, which Venom holds too, and the return buffer (an
   alloca made after sa) holds its first cap bytes. *)
Definition extcall_returned_def:
  extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap
      target has_default default_op default_ty default_opt returnData ee t <=>
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\
       storage_well_formed_on cx ee (FST H)) /\ wb_frame cenv es ee sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = sr.cs_current_bb /\
    t.vs_inst_idx = LENGTH sr.cs_current_insts /\ ee.gas_obs = [] /\
    accounts_runtime_well_typed ee.accounts /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sr.cs_next_var /\ sa.cs_next_id <= sr.cs_next_id /\
    local_ptrs_reserved cenv sr /\
    EVERY (safe_operand sr) [addr_op; buf_op; default_op] /\
    (?aw. eval_operand addr_op t = SOME aw /\ w2w aw = target) /\
    t.vs_returndata = returnData /\ LENGTH returnData < dimword (:256) /\
    (?ro. eval_operand buf_op t = SOME ro /\ w2n ro + cap < dimword (:256) /\
          (?live buf_size. sa.cs_next_id <= live /\ live < sr.cs_next_id /\
             cap <= buf_size /\
             FLOOKUP t.vs_allocas live = SOME (w2n ro, buf_size)) /\
          mem_bytes_at (w2n ro) (LENGTH (TAKE cap returnData)) t.vs_memory =
            TAKE cap returnData) /\
    extcall_default_ready cx ret_type has_default default_op default_ty
      default_opt t
End

Theorem extcall_request_frame_call_value_initial_domain:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  storage_trace_domain cx st0 ee.storage_trace ==>
  frame_call_value cx value_opt ee = (INL value_opt, ee)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
     ctx func cenv cx ee t` by metis_tac[extcall_request_ready_def] >>
  `~cx.txn.is_static` by fs[exprLoweringPropsTheory.stmt_state_rel_def,
                          loweringStateRelDefsTheory.state_rel_def] >>
  simp[frame_call_value_def, vyperStateTheory.return_def]
QED

Theorem extcall_request_oracle_core_initial_domain:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  inst.inst_outputs = [out] ==>
  ?aw vw ao az ro gas u.
    eval_operand addr_op t = SOME aw /\ w2w aw = target /\
    eval_operand value_op t = SOME vw /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    eval_operand call_offset t = SOME ao /\
    eval_operand call_len t = SOME az /\
    eval_operand buf_op t = SOME ro /\ eval_operand gas_op t = SOME gas /\
    read_memory (w2n ao) (w2n az) t = calldata /\
    exec_ext_call inst t gas aw vw ao az ro ((n2w cap):bytes32) stat =
      OK (update_var out (if oc.co_success then 1w else 0w) u) /\
    u = t with <|vs_outcomes := u.vs_outcomes; vs_requests := u.vs_requests;
      vs_accounts := u.vs_accounts; vs_transient := u.vs_transient;
      vs_logs := u.vs_logs; vs_pending_deletions := u.vs_pending_deletions;
      vs_returndata := u.vs_returndata; vs_memory := u.vs_memory|> /\
    u.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE cap oc.co_returnData) t).vs_memory /\
    u.vs_returndata = oc.co_returnData /\
    (!H. valid_horizon cx st0 H
       (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
      (local_ptrs_rel func cenv ee.scopes u /\
       immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee u ==>
       state_rel H func cenv cx (SND (adopt_call_outcome rq oc consumed)) u))
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H
      (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
      valid_horizon cx st0 H ee.storage_trace` by
    (rpt strip_tac >>
     `adopt_call_outcome rq oc consumed =
        (INL (), SND (adopt_call_outcome rq oc consumed))` by
       simp[adopt_call_outcome_equation] >>
     metis_tac[valid_horizon_frame, storage_trace_frame_adopt,
               storage_trace_frame_take_call]) >>
  fs[extcall_request_ready_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
    ee.storage_trace` by fs[storage_trace_domain_def] >>
  `state_rel (storage_trace_horizon ee.storage_trace)
    func cenv cx ee t` by metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  Cases_on `eval_operand gas_op t` >> gvs[] >> rename1 `_ = SOME gas` >>
  `cap < dimword (:256)` by decide_tac >>
  `w2n ((n2w cap):bytes32) = cap` by simp[] >>
  `IS_NONE value_opt = (value_opt = NONE)` by (Cases_on `value_opt` >> simp[]) >>
  VALID (drule_then mp_tac (INST_TYPE [Type.beta |-> ``:bytes32``, Type.gamma |-> ``:256``, Type.delta |-> ``:256``] exec_ext_call_oracle_step) >>
    disch_then (qspec_then `inst` mp_tac) >> simp[] >>
    disch_then drule_all >>
    disch_then (strip_assume_tac o Q.ISPECL
      [`gas:bytes32`, `ro:bytes32`, `(n2w cap):bytes32`])) >>
  qexists_tac `s'` >> simp[] >> rpt strip_tac >>
  `state_rel H func cenv cx ee t` by metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  VALID (drule_then mp_tac (INST_TYPE [Type.beta |-> ``:bytes32``, Type.gamma |-> ``:256``, Type.delta |-> ``:256``] exec_ext_call_oracle_step) >>
    disch_then (qspec_then `inst` mp_tac) >> simp[] >>
    disch_then drule_all >>
    disch_then (strip_assume_tac o Q.ISPECL
      [`gas:bytes32`, `ro:bytes32`, `(n2w cap):bytes32`])) >>
  `s'' = s'` by
    (qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `s'' = _` mp_tac >>
     qpat_x_assum `s' = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomStateTheory.update_var_def,
          venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  gvs[]
QED

Theorem extcall_request_memory_rel:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  valid_horizon cx st0 H ee.storage_trace /\
  eval_operand buf_op t = SOME ro /\
  u.vs_vars = t.vs_vars /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\
  u.vs_data_section = t.vs_data_section /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory ==>
  local_ptrs_rel func cenv ee.scopes u /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee u
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
  `local_ptrs_rel func cenv ee.scopes t /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee t` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def] >>
  conj_tac
  >- (irule local_ptrs_rel_clean_write_frame >>
      qexistsl_tac [`TAKE cap rd`, `w2n ro`, `t`] >>
      simp[venomStateTheory.lookup_var_def] >> rpt strip_tac >>
      first_x_assum drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `t` >>
  simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion] >>
  rpt strip_tac >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  first_x_assum drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_request_wb_frame:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  v.vs_allocas = t.vs_allocas /\ v.vs_alloca_next = t.vs_alloca_next /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!x. not_fresh_at sp x ==> lookup_var x v = lookup_var x t) ==>
  wb_frame cenv es ee sa s0 v
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
  fs[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sp x` by
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >> metis_tac[])
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `regions_disjoint (w2n ro) cap off sz` by metis_tac[] >>
      `mem_bytes_at off sz
        (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory =
       mem_bytes_at off sz t.vs_memory` by
        (irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      metis_tac[]) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >> qexists_tac `t` >>
  simp[] >> rpt strip_tac >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_request_default_frame:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  v.vs_alloca_next = t.vs_alloca_next /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!x. not_fresh_at sp x ==> lookup_var x v = lookup_var x t) ==>
  extcall_default_ready cx ret_type has_default default_op default_ty default_opt v
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  `safe_operand sp default_op` by fs[] >>
  `!w. eval_operand default_op t = SOME w ==>
       eval_operand default_op v = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     fs[exprSafeOperandTheory.safe_operand_def] >>
     qexistsl_tac [`sp`, `t`] >> metis_tac[]) >>
  fs[extcall_default_ready_def] >> rpt strip_tac >>
  first_x_assum drule >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexistsl_tac [`tv`, `rtv`, `w`] >> simp[] >>
  Cases_on `is_word_type default_ty`
  >- gvs[loweringPostsTheory.expr_val_rel_def] >>
  irule exprSimPropsTheory.expr_val_rel_footprint_agree >>
  simp[] >> qexists_tac `t` >> simp[] >>
  sym_tac >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
  `regions_disjoint (w2n ro) cap (w2n w) (val_footprint tv d)` by metis_tac[] >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_request_structural_frame:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  valid_horizon cx st0 H (SND (adopt_call_outcome rq oc consumed)).storage_trace /\
  state_rel H func cenv cx (SND (adopt_call_outcome rq oc consumed))
    (update_var out word u) /\
  ~not_fresh_at sp out /\
  u = t with <|vs_outcomes := u.vs_outcomes; vs_requests := u.vs_requests;
    vs_accounts := u.vs_accounts; vs_transient := u.vs_transient;
    vs_logs := u.vs_logs; vs_pending_deletions := u.vs_pending_deletions;
    vs_returndata := u.vs_returndata; vs_memory := u.vs_memory|> ==>
  stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed))
    (update_var out word u)
Proof
  strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (`adopt_call_outcome rq oc consumed =
        (INL (), SND (adopt_call_outcome rq oc consumed))` by
       simp[adopt_call_outcome_equation] >>
     metis_tac[valid_horizon_frame, storage_trace_frame_adopt,
       storage_trace_frame_take_call]) >>
  drule oracle_take_adoption_locals >> strip_tac >>
  fs[extcall_request_ready_def] >>
  `stmt_state_rel H ctx func cenv cx ee t` by metis_tac[] >>
  `!x. not_fresh_at sp x ==>
    lookup_var x (update_var out word u) = lookup_var x t` by
    (rpt strip_tac >>
     `x <> out` by metis_tac[] >>
     simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_labels = t.vs_labels /\ u.vs_fmp = t.vs_fmp` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def] >> rpt conj_tac
  >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `t` >>
      simp[venomStateTheory.update_var_def] >> metis_tac[])
  >- (fs[exprLoweringPropsTheory.alloca_room_def,
         exprLoweringPropsTheory.pending_alloca_size_def,
         venomStateTheory.update_var_def] >> metis_tac[])
  >- (fs[exprLoweringPropsTheory.fmp_room_def,
         exprLoweringPropsTheory.pending_alloca_size_def,
         venomStateTheory.update_var_def] >> metis_tac[])
  >- (irule exprLoweringPropsTheory.immutable_alloca_sep_fields >>
      qexistsl_tac [`t`, `ee`] >> simp[venomStateTheory.update_var_def] >>
      rpt strip_tac >> qexists_tac `id` >>
      irule exprSimPropsTheory.local_region_frame >> conj_tac
      >- (qexists_tac `func` >> fs[loweringStateRelDefsTheory.state_rel_def]) >>
      qexistsl_tac [`sp`, `ee.scopes`, `update_var out word u`] >>
      simp[venomStateTheory.update_var_def] >>
      fs[venomStateTheory.update_var_def] >> metis_tac[])
  >- (irule exprLoweringPropsTheory.immutable_base_zero_frame >>
      qexists_tac `t` >> simp[venomStateTheory.update_var_def] >>
      fs[loweringStateRelDefsTheory.local_ptrs_reserved_def,
         venomStateTheory.update_var_def] >> metis_tac[]) >>
  fs[venomStateTheory.update_var_def] >> metis_tac[]
QED


(* (1) Operands and request.  The lowering up to the extcodesize check, run
   against the source up to the built calldata: whatever runs the rest of
   eval_ext_call from a ready request, with the lowered call step at sp and
   the return handling at sr, runs the whole call. *)
Theorem extcall_request_setup:
  !nocalls ctx func cenv cx env ann is_static skip fname arg_types ret_type
   opts args dflt ty es st0 sa sb vv s0 Q.
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       exprs_case nocalls ctx func cenv cx
         (TAKE (LENGTH arg_types) (DROP 1 args))) /\
    (!s target t s' vs t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_exprs cx (TAKE (LENGTH arg_types) (DROP 1 args)) s' =
         (INL vs, t') ==>
       exprs_case nocalls ctx func cenv cx
         (DROP (1 + LENGTH arg_types) args)) /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    (nocalls ==>
     int_calls_expr
       (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
          args dflt) = []) /\
    compile_expr cenv ty
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) sa = (vv, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible
      (eval_expr cx
         (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
            args dflt)) expr_vv_res_ok es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!sp sr u result_op addr_op value_op gas_op buf_op call_offset call_len
      has_default default_op default_ty target_v rest target value_opt
      calldata ee t.
       (* the lowered call step, sp to sr *)
       comp_ignore_bind
         (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
          else comp_return ())
         (comp_bind
            (if is_static then
               emit_op STATICCALL
                 [gas_op; addr_op; call_offset; call_len; buf_op;
                  Lit (n2w (abi_size_bound cenv.ce_struct_fields
                     (if needs_external_call_wrap ret_type
                      then TupleT [ret_type] else ret_type)))]
             else
               emit_op CALL
                 [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
                  Lit (n2w (abi_size_bound cenv.ce_struct_fields
                     (if needs_external_call_wrap ret_type
                      then TupleT [ret_type] else ret_type)))])
         (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
          comp_bind (fresh_label "extcall_cont") (\cont_lbl.
          comp_ignore_bind
            (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
          (comp_ignore_bind (new_block fail_lbl)
          (comp_bind (emit_op RETURNDATASIZE []) (\rds.
          comp_bind (compile_alloc_buffer 0) (\fail_buf.
          comp_ignore_bind
            (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
          (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
             (new_block cont_lbl)))))))))) sp = (u, sr) /\
       (* the lowered return handling, sr to sb *)
       (let wrapped = (if needs_external_call_wrap ret_type
                       then TupleT [ret_type] else ret_type) in
        let min_size = abi_static_size cenv.ce_struct_fields wrapped in
        let dec_info = type_to_abi_dec_info cenv.ce_struct_fields cenv wrapped in
        (if ret_type = NoneT then comp_return (Lit 0w)
         else if has_default then
           comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
             (\r. compile_default_return_path cenv ret_type default_ty
                    buf_op r.buf_operand default_op addr_op skip min_size
                    (abi_size_bound cenv.ce_struct_fields wrapped) dec_info)
         else
           comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
             (\r. comp_bind (compile_return_value_decode min_size
                         (abi_size_bound cenv.ce_struct_fields wrapped))
             (\hi_op. comp_ignore_bind
                (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
                   buf_op hi_op dec_info)
                (comp_return r.buf_operand)))) sr = (result_op, sb)) /\
       vv = (if ret_type = NoneT then StackValue ann result_op
             else LocatedValue ann (mk_ptr result_op LocMemory)) /\
       fn_has_code sp sr func /\ fn_has_code sr sb func /\
       (* the source's request *)
       LENGTH rest = LENGTH arg_types + LENGTH opts /\
       ext_call_opts_ok is_static opts /\
       dest_AddressV target_v = SOME target /\
       value_opt =
         (if is_static then NONE
          else case ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest) of
                 NONE => SOME 0
               | SOME v => dest_NumV v) /\
       build_ext_calldata (get_tenv cx) fname arg_types
         (TAKE (LENGTH arg_types) rest) = SOME calldata /\
       extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
         addr_op value_op gas_op buf_op call_offset call_len
         (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type))
         target value_opt calldata has_default default_op default_ty
         (ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)) ee t ==>
       gas_outcome F (cx_tops cx) (ctx,func) cx st0
         (eval_ext_call cx is_static skip (fname,arg_types,ret_type) opts
            (target_v :: rest)) (ee,t) Q (\H res ee r. expr_exit res r)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (eval_expr cx
         (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
            args dflt)) (es,s0) Q (\H res ee r. expr_exit res r)
Proof
  cheat
QED

(* (2) The call step.  From a ready request at sp: the extcodesize check
   against the source's precheck, the CALL or STATICCALL as an oracle step
   (extCallOracleStep), and a failed call's returndata copy and REVERT
   against the source's RevertData; a successful call reaches sr with the
   returndata in the buffer. *)
(* The oracle prefix leaves the supplied gas-observation suffix untouched.
   Unlike a normalized source frame, this equation retains the trace. *)
Theorem extcall_call_prefix_observation:
  ee.outcomes = SOME os ==>
  (do accounts <- get_accounts;
      check (ext_call_precheck_ok skip ret_type target accounts)
            "ExtCall target has no code";
      value_opt' <- frame_call_value cx value_opt;
      eval_ext_call_effects cx target calldata value_opt' gas accounts
   od) (ee with gas_obs := tail) =
  (let (res, last) =
     (do accounts <- get_accounts;
         check (ext_call_precheck_ok skip ret_type target accounts)
               "ExtCall target has no code";
         value_opt' <- frame_call_value cx value_opt;
         eval_ext_call_effects cx target calldata value_opt' gas accounts
      od) ee
   in (res, last with gas_obs := tail))
Proof
  strip_tac >>
  simp[get_accounts_def, bind_def, ignore_bind_def, check_def,
       vyperStateTheory.assert_def, return_def, raise_def] >>
  Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts` >> simp[] >>
  simp[frame_call_value_def, bind_def, ignore_bind_def, check_def,
       vyperStateTheory.assert_def, return_def, raise_def] >>
  Cases_on `cx.txn.is_static` >> simp[] >>
  Cases_on `value_opt = NONE \/ value_opt = SOME 0` >>
  simp[vyperStateTheory.assert_def, bind_def, ignore_bind_def, return_def] >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def, return_def,
       take_call_outcome_def, take_request_outcome_def,
       call_outcome_request_def] >>
  pairarg_tac >> simp[] >>
  rpt IF_CASES_TAC >>
  simp[bind_def, ignore_bind_def, return_def, raise_def,
       adopt_call_outcome_equation] >>
  Cases_on `outcome.co_success` >> simp[return_def, raise_def] >>
  Cases_on `value_opt = NONE` >> simp[]
QED

(* In oracle mode the prefix exposes the failure before adoption. *)
Theorem extcall_call_prefix_oracle:
  ee.outcomes = SOME os ==>
  (do accounts <- get_accounts;
      check (ext_call_precheck_ok skip ret_type target accounts)
            "ExtCall target has no code";
      value_opt' <- frame_call_value cx value_opt;
      eval_ext_call_effects cx target calldata value_opt' gas accounts
   od) ee =
  (do check (ext_call_precheck_ok skip ret_type target ee.accounts)
            "ExtCall target has no code";
      value_opt' <- frame_call_value cx value_opt;
      (rq,oc) <- take_call_outcome target calldata value_opt';
      if oc.co_success then
        do adopt_call_outcome rq oc; return oc.co_returnData od
      else raise (Error (RevertData oc.co_returnData))
   od) ee
Proof
  strip_tac >>
  simp[get_accounts_def, bind_def, ignore_bind_def, check_def,
       vyperStateTheory.assert_def, return_def] >>
  Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts` >> simp[] >>
  simp[frame_call_value_def, bind_def, ignore_bind_def, check_def,
       vyperStateTheory.assert_def, return_def] >>
  Cases_on `cx.txn.is_static` >> simp[] >>
  Cases_on `value_opt = NONE \/ value_opt = SOME 0` >>
  simp[vyperStateTheory.assert_def, bind_def, ignore_bind_def, return_def] >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `take_call_outcome target calldata vo ee` >>
  Cases_on `take_call_outcome target calldata vo ee` >>
  rename1 `_ = (result,mid)` >> Cases_on `result` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.co_success` >> simp[bind_def, return_def, raise_def]
QED

Theorem extcall_call_prefix_trace_frame:
  storage_trace_frame
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
              "ExtCall target has no code";
        value_opt' <- frame_call_value cx value_opt;
        eval_ext_call_effects cx target calldata value_opt' gas accounts
     od)
Proof
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads] >> gen_tac >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_call_value, storage_trace_frame_ext_effects]
QED

Theorem extcall_call_finish_shape:
  comp_bind (fresh_label "extcall_fail") (\fail_lbl.
    comp_bind (fresh_label "extcall_cont") (\cont_lbl.
    comp_ignore_bind
      (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
    (comp_ignore_bind (new_block fail_lbl)
    (comp_bind (emit_op RETURNDATASIZE []) (\rds.
    comp_bind (compile_alloc_buffer 0) (\fail_buf.
    comp_ignore_bind
      (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
    (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
      (new_block cont_lbl)))))))) sc = (u,sr) ==>
  let fl = fresh_label_output "extcall_fail" sc.cs_next_label;
      cl = fresh_label_output "extcall_cont" (sc.cs_next_label + 1);
      rv = STRING #"%" (toString sc.cs_next_var);
      bv = STRING #"%" (toString (sc.cs_next_var + 1)) in
  u = fl /\ sr.cs_current_bb = cl /\ sr.cs_current_insts = [] /\
  sr.cs_next_var = sc.cs_next_var + 2 /\
  sr.cs_next_id = sc.cs_next_id + 5 /\
  sr.cs_next_label = sc.cs_next_label + 2 /\
  sr.cs_blocks =
    <|bb_label := fl; bb_instructions :=
      [mk_inst (sc.cs_next_id + 1) RETURNDATASIZE [] [rv];
       mk_inst (sc.cs_next_id + 2) ALLOCA [Lit 0w] [bv];
       mk_inst (sc.cs_next_id + 3) RETURNDATACOPY [Var bv; Lit 0w; Var rv] [];
       mk_inst (sc.cs_next_id + 4) REVERT [Var bv; Var rv] []]|> ::
    <|bb_label := sc.cs_current_bb; bb_instructions :=
      sc.cs_current_insts ++
      [mk_inst sc.cs_next_id JNZ [success; Label cl; Label fl] []]|> ::
    sc.cs_blocks
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, emit_inst_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, new_block_def,
       compile_alloc_buffer_def] >> strip_tac >> gvs[]
QED

Theorem extcall_call_revert_run[local]:
  rv <> bv /\ LENGTH s.vs_returndata < dimword (:256) ==>
  ?mid z.
    run_inst_seq
      [mk_inst id RETURNDATASIZE [] [rv];
       mk_inst (id + 1) ALLOCA [Lit 0w] [bv];
       mk_inst (id + 2) RETURNDATACOPY [Var bv; Lit 0w; Var rv] []] s = OK mid /\
    step_inst_base (mk_inst (id + 3) REVERT [Var bv; Var rv] [])
      (mid with vs_inst_idx := 3) = Abort Revert_abort z /\
    z.vs_returndata = s.vs_returndata /\
    mid.vs_current_bb = s.vs_current_bb /\ mid.vs_halted = s.vs_halted
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var rv (n2w (LENGTH s.vs_returndata)) s` >>
  `?s2 w. exec_alloca (mk_inst (id + 1) ALLOCA [Lit 0w] [bv]) s1 (0w:bytes32) = OK s2 /\
      lookup_var bv s2 = SOME w /\
      lookup_var rv s2 = SOME (n2w (LENGTH s.vs_returndata)) /\
      s2.vs_returndata = s.vs_returndata /\
      s2.vs_current_bb = s.vs_current_bb /\ s2.vs_halted = s.vs_halted` by
    (Cases_on `FLOOKUP s1.vs_allocas (id + 1)`
     >- gvs[exec_alloca_def, mk_inst_def, lookup_var_def, update_var_def,
            FLOOKUP_UPDATE, Abbr `s1`] >>
     PairCases_on `x` >>
     gvs[exec_alloca_def, mk_inst_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, Abbr `s1`]) >>
  fs[Abbr `s1`, mk_inst_def] >>
  qabbrev_tac `mid = write_memory_with_expansion (w2n w) s.vs_returndata s2` >>
  qexists_tac `mid` >>
  `run_inst_seq
      [mk_inst id RETURNDATASIZE [] [rv];
       mk_inst (id + 1) ALLOCA [Lit 0w] [bv];
       mk_inst (id + 2) RETURNDATACOPY [Var bv; Lit 0w; Var rv] []] s = OK mid` by
    (simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read0_def, is_terminator_def] >>
     qpat_x_assum `exec_alloca _ _ _ = OK _` (fn th => rewrite_tac[th]) >>
     simp[eval_operand_def, wordsTheory.w2n_n2w, LESS_MOD, Abbr `mid`]) >>
  simp[] >>
  `lookup_var bv mid = SOME w /\
   lookup_var rv mid = SOME (n2w (LENGTH s.vs_returndata))` by
    simp[Abbr `mid`, lookup_var_def, write_memory_with_expansion_def,
         GSYM lookup_var_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       lookup_var_def, wordsTheory.w2n_n2w, LESS_MOD] >>
  fs[mk_inst_def] >>
  simp[revert_state_def, set_returndata_def, GSYM read_memory_def,
       Abbr `mid`, read_memory_write_self] >>
  simp[write_memory_with_expansion_def]
QED

Theorem extcall_call_revert_path[local]:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ rv <> bv /\
  LENGTH s.vs_returndata < dimword (:256) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := fl; bb_instructions :=
      [mk_inst id RETURNDATASIZE [] [rv];
       mk_inst (id + 1) ALLOCA [Lit 0w] [bv];
       mk_inst (id + 2) RETURNDATACOPY [Var bv; Lit 0w; Var rv] [];
       mk_inst (id + 3) REVERT [Var bv; Var rv] []]|> ==>
  ?z. gas_marked_path F ctx func s 0 (Abort Revert_abort z) /\
      z.vs_returndata = s.vs_returndata
Proof
  strip_tac >> drule_all extcall_call_revert_run >>
  disch_then (qspec_then `id` strip_assume_tac) >>
  `gas_path ctx func s 0 (OK (mid with vs_inst_idx := 3))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> simp[] >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `[mk_inst (id + 3) REVERT [Var bv; Var rv] []]` >> simp[]) >>
  `gas_path_edge ctx func (mid with vs_inst_idx := 3) 0 (Abort Revert_abort z)` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[get_instruction_def, step_inst_non_invoke, mk_inst_def,
          gas_count_step_def, fragExecTheory.exit_result_def] >>
     fs[mk_inst_def, fragExecTheory.exit_result_def]) >>
  qexists_tac `z` >> simp[gas_marked_path_def] >>
  `gas_path ctx func (mid with vs_inst_idx := 3) 0 (Abort Revert_abort z)` by
    (irule (cj 3 gas_path_rules) >> simp[fragExecTheory.exit_result_def]) >>
  metis_tac[gas_path_then, ADD_CLAUSES]
QED

Theorem extcall_call_finish_path:
  comp_bind (fresh_label "extcall_fail") (\fail_lbl.
    comp_bind (fresh_label "extcall_cont") (\cont_lbl.
    comp_ignore_bind
      (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
    (comp_ignore_bind (new_block fail_lbl)
    (comp_bind (emit_op RETURNDATASIZE []) (\rds.
    comp_bind (compile_alloc_buffer 0) (\fail_buf.
    comp_ignore_bind
      (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
    (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
      (new_block cont_lbl)))))))) sc = (u,sr) /\
  fn_has_code sc sr func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand success s = SOME (if ok then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  cs_extends sc sr /\ sr.cs_current_insts = [] /\
  (if ok then
     gas_marked_path F ctx func s 0 (OK (jump_to sr.cs_current_bb s))
   else ?z. gas_marked_path F ctx func s 0 (Abort Revert_abort z) /\
            z.vs_returndata = s.vs_returndata)
Proof
  strip_tac >> drule extcall_call_finish_shape >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sr.cs_blocks = fb :: jb :: sc.cs_blocks` >>
  `cs_extends sc sr` by
    simp[cs_extends_def, Abbr `jb`, IS_PREFIX_APPEND] >>
  simp[] >>
  `lookup_block sc.cs_current_bb func.fn_blocks = SOME jb /\
   lookup_block u func.fn_blocks = SOME fb` by
    (`jb.bb_label = sc.cs_current_bb /\ fb.bb_label = u` by
       simp[Abbr `jb`, Abbr `fb`] >>
     fs[fn_has_code_def, emitted_blocks_def] >> metis_tac[]) >>
  `gas_path_edge ctx func s 0
     (OK (jump_to (if ok then sr.cs_current_bb else u) s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[Abbr `jb`, get_instruction_def, EL_LENGTH_APPEND,
          step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_inst_base_opcode_eqs, eval_operand_def, is_terminator_def,
          jump_to_def] >> Cases_on `ok` >> simp[] >> metis_tac[]) >>
  Cases_on `ok` >> gvs[]
  >- (simp[gas_marked_path_def] >>
      metis_tac[gas_path_rules, gas_path_edge_normal, ADD_CLAUSES]) >>
  `?z. gas_marked_path F ctx func
         (jump_to (fresh_label_output "extcall_fail" sc.cs_next_label) s)
         0 (Abort Revert_abort z) /\
       z.vs_returndata =
         (jump_to (fresh_label_output "extcall_fail" sc.cs_next_label) s).vs_returndata` by
    (irule extcall_call_revert_path >>
     simp[jump_to_def, Abbr `fb`, ASCIInumbersTheory.toString_11] >>
     qexistsl_tac [`STRING #"%" (toString (sc.cs_next_var + 1))`,
                   `sc.cs_next_id + 1`, `STRING #"%" (toString sc.cs_next_var)`] >>
     simp[ASCIInumbersTheory.toString_11, ADD_ASSOC]) >>
  qexists_tac `z` >> simp[gas_marked_path_def] >>
  fs[gas_marked_path_def] >> simp[jump_to_def] >>
  metis_tac[cj 2 gas_path_rules, ADD_CLAUSES]
QED

Theorem extcall_call_step:
  !ctx func cenv cx es st0 sa s0 sp sr u is_static skip ret_type
   addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
   calldata gas has_default default_op default_ty default_opt ee t k Q.
    comp_ignore_bind
      (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
       else comp_return ())
      (comp_bind
         (if is_static then
            emit_op STATICCALL
              [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
          else
            emit_op CALL
              [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
               Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind
         (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
          (new_block cont_lbl)))))))))) sp = (u, sr) /\
    fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
    extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t /\
    (!returnData. storage_trace_frame (k returnData)) /\
    (!returnData ee' t'.
       extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap target
         has_default default_op default_ty default_opt returnData ee' t' /\
       storage_trace_domain cx st0 ee'.storage_trace ==>
       ?marks. gas_summary_at F (ctx,func) marks (k returnData) (ee',t')
                 (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==>
                    Q H res ee t)
                 (\res ee r. expr_exit res r)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          value_opt' <- frame_call_value cx value_opt;
          returnData <- eval_ext_call_effects cx target calldata value_opt'
                          gas accounts;
          k returnData
       od) (ee,t) Q (\H res ee r. expr_exit res r)
Proof
  cheat
QED

(* (3) Return handling.  From sr after a successful call: void, the
   default on empty returndata (with the code recheck) and the bounded
   memory decode, whose rejection of returndata the source's
   evaluate_abi_decode_return rejects aborts. *)
Theorem extcall_return_values:
  !ctx func cenv cx env es ann is_static skip fname arg_types ret_type opts
   args dflt st0 sa sb s0 sr result_op vv addr_op buf_op cap target
   has_default default_op default_ty default_opt returnData ee t.
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    cap = abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type) /\
    (let wrapped = (if needs_external_call_wrap ret_type
                    then TupleT [ret_type] else ret_type) in
     let min_size = abi_static_size cenv.ce_struct_fields wrapped in
     let dec_info = type_to_abi_dec_info cenv.ce_struct_fields cenv wrapped in
     (if ret_type = NoneT then comp_return (Lit 0w)
      else if has_default then
        comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
          (\r. compile_default_return_path cenv ret_type default_ty
                 buf_op r.buf_operand default_op addr_op skip min_size
                 (abi_size_bound cenv.ce_struct_fields wrapped) dec_info)
      else
        comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
          (\r. comp_bind (compile_return_value_decode min_size
                      (abi_size_bound cenv.ce_struct_fields wrapped))
          (\hi_op. comp_ignore_bind
             (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
                buf_op hi_op dec_info)
             (comp_return r.buf_operand)))) sr = (result_op, sb)) /\
    vv = (if ret_type = NoneT then StackValue ann result_op
          else LocatedValue ann (mk_ptr result_op LocMemory)) /\
    fn_has_code sr sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    storage_trace_domain cx st0 ee.storage_trace /\
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap target
      has_default default_op default_ty default_opt returnData ee t ==>
    ?marks. gas_summary_at F (ctx,func) marks
      (case (if returnData = [] then default_opt else NONE) of
         SOME default_v =>
           do accounts' <- get_accounts;
              check (skip \/ ext_call_has_code target accounts')
                    "ExtCall target has no code";
              return (Value default_v)
           od
       | NONE =>
           do ret_val <- lift_sum_runtime
                (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val)
           od) (ee,t)
      (\res ee' t'. !H. valid_horizon cx st0 H ee'.storage_trace ==>
         ?tv. res = INL tv /\
         vv_post H ctx func cenv cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt) es sa sb s0 ee' tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  cheat
QED

Theorem bind_return_left[local]:
  bind (return x) f = f x
Proof
  simp[FUN_EQ_THM, bind_def, return_def]
QED

Theorem assert_true[local]:
  assert T e = return ()
Proof
  simp[FUN_EQ_THM, assert_def, return_def]
QED

(* The rest of eval_ext_call from a built request: the precheck, the call
   and the return handling. *)
Theorem eval_ext_call_request:
  LENGTH rest = LENGTH arg_types + LENGTH opts /\
  ext_call_opts_ok stat opts /\
  dest_AddressV target_v = SOME target /\
  value_opt =
    (if stat then NONE
     else case ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest) of
            NONE => SOME 0
          | SOME v => dest_NumV v) /\
  (stat <=> value_opt = NONE) /\
  build_ext_calldata (get_tenv cx) fname arg_types
    (TAKE (LENGTH arg_types) rest) = SOME calldata ==>
  eval_ext_call cx stat skip (fname,arg_types,ret_type) opts
    (target_v :: rest) =
  do accounts <- get_accounts;
     check (ext_call_precheck_ok skip ret_type target accounts)
           "ExtCall target has no code";
     value_opt' <- frame_call_value cx value_opt;
     returnData <- eval_ext_call_effects cx target calldata value_opt'
       (forwarded_gas default_evm_gas_limit
          (ext_call_kwarg EKGas opts (DROP (LENGTH arg_types) rest))) accounts;
     case (if returnData = []
           then ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)
           else NONE) of
       SOME default_v =>
         do accounts' <- get_accounts;
            check (skip \/ ext_call_has_code target accounts')
                  "ExtCall target has no code";
            return (Value default_v)
         od
     | NONE =>
         do ret_val <- lift_sum_runtime
              (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
            return (Value ret_val)
         od
  od
Proof
  strip_tac >>
  qpat_x_assum `value_opt = _` SUBST_ALL_TAC >>
  qpat_x_assum `_ <=> _ = NONE` mp_tac >>
  `?kv. ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest) = kv` by
    simp[] >>
  Cases_on `stat` >> Cases_on `kv` >>
  TRY (rename1 `ext_call_kwarg _ _ _ = SOME v` >> Cases_on `dest_NumV v`) >>
  asm_simp_tac bool_ss [optionTheory.option_case_def] >> rpt strip_tac >>
  simp_tac bool_ss [eval_ext_call_def, LET_THM] >>
  asm_simp_tac bool_ss [type_check_def, assert_true, ignore_bind_def,
                        lift_option_type_def, optionTheory.option_case_def,
                        bind_return_left]
QED

Theorem compile_extcall_case:
  !nocalls ctx func cenv cx ann is_static skip sig opts args dflt.
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       exprs_case nocalls ctx func cenv cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args))) /\
    (!s target t s' vs t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_exprs cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 args)) s' =
         (INL vs, t') ==>
       exprs_case nocalls ctx func cenv cx
         (DROP (1 + LENGTH (FST (SND sig))) args)) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  rpt gen_tac >> PairCases_on `sig` >>
  PURE_REWRITE_TAC [pairTheory.FST, pairTheory.SND] >> strip_tac >>
  rename1 `ExtCall stat skip (fname,arg_types,ret_type) opts` >>
  `expr_vv_case nocalls ctx func cenv cx
     (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
        args dflt)` suffices_by simp[expr_sim_case_of_vv] >>
  rewrite_tac[expr_vv_case_def, expr_vv_sim_def] >> rpt strip_tac >>
  qspecl_then [`nocalls`, `ctx`, `func`, `cenv`, `cx`, `env`, `ann`, `stat`,
                `skip`, `fname`, `arg_types`, `ret_type`, `opts`, `args`,
                `dflt`, `ty`, `es`, `st0`, `sa`, `sb`, `vv`, `s0`]
    MATCH_MP_TAC extcall_request_setup >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, ALL_TAC] >>
  rpt strip_tac >>
  `stat <=> value_opt = NONE` by fs[extcall_request_ready_def] >>
  drule_all eval_ext_call_request >>
  disch_then (qspecl_then [`skip`, `ret_type`] SUBST1_TAC) >>
  ho_match_mp_tac extcall_call_step >>
  qpat_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `comp_ignore_bind _ _ _ = _` (irule_at Any) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt (pop_assum kall_tac) >> gen_tac >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_state_reads, storage_trace_frame_lifts,
           storage_trace_frame_ignore_bind, storage_trace_frame_checks,
           storage_trace_frame_return]) >>
  rpt strip_tac >>
  BETA_TAC >> irule extcall_return_values >>
  qpat_assum `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qexists_tac `result_op` >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]
QED
