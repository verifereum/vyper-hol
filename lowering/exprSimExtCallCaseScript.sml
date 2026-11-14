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
  gasSummaryCompose aggregateCountedOutcome
  extcallReturnCallerSuccess extcallReturnCallerReject extCallCodeCheck
  extcallReturnDefaultResources extcallReturnDefaultRouting extcallReturnDefaultStore
  extcallReturnDefaultDecode extcallReturnDefaultOwnership extcallReturnDefaultIntervals
  extcallReturnInterface extcallReturnDefaultTypes
  exprSimAbiEncodeArgsMaterializePath exprSimMemorySource
  exprLowering compileEnv abiEncodeMaterialize context aggregateEvaluatedLayout

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

Theorem extcall_default_ready_prefix_frame:
  extcall_default_ready cx rt hd dop dt dv s /\
  safe_operand st dop /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!d w tv. dv = SOME d /\ ~is_word_type dt /\
     eval_operand dop s = SOME w /\
     evaluate_type (get_tenv cx) dt = SOME tv ==>
     mem_bytes_at (w2n w) (val_footprint tv d) t.vs_memory =
     mem_bytes_at (w2n w) (val_footprint tv d) s.vs_memory) ==>
  extcall_default_ready cx rt hd dop dt dv t
Proof
  strip_tac >>
  `!w. eval_operand dop s = SOME w ==> eval_operand dop t = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     fs[exprSafeOperandTheory.safe_operand_def] >>
     qexistsl_tac [`st`, `s`] >> metis_tac[]) >>
  fs[extcall_default_ready_def] >> rpt strip_tac >>
  qpat_x_assum `!d. dv = SOME d ==> _` drule >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexistsl_tac [`tv`, `rtv`, `w`] >> simp[] >>
  reverse conj_tac >- (strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `is_word_type dt`
  >- gvs[loweringPostsTheory.expr_val_rel_def] >>
  irule exprSimPropsTheory.expr_val_rel_footprint_agree >>
  simp[] >> qexists_tac `s` >> metis_tac[]
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
Theorem extcall_request_default_materialize_marked:
  !ce e vv sm dst sb cx env es_pre ctx func es sa s0 es' tvv r
   st0 tr H0 v tv rt rtv.
  compile_materialize_vv ce (lowered_value_type ce e) vv sm = (dst,sb) /\
  expr_body_pre ce cx env e es_pre /\
  (!H. valid_horizon cx st0 H tr ==>
       vv_post H ctx func ce cx e es sa sm s0 es' tvv vv r) /\
  valid_horizon cx st0 H0 tr /\
  stmt_state_rel H0 ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tvv es' = (INL v,es') /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  rt <> NoneT /\ ~is_word_type rt /\
  (lowered_value_type ce e = rt \/
   is_bytestring_type (lowered_value_type ce e) /\ is_bytestring_type rt) /\
  evaluate_type (get_tenv cx) rt = SOME rtv /\
  value_has_type rtv v /\ val_wf rtv v ==>
  ?t. gas_marked_exec F (ctx,func) (read_result cx tvv) (es',r)
        [] (INL v) es' (OK t) /\
      (!H. valid_horizon cx st0 H tr ==>
         materialize_owned_post H ctx func ce cx e es sa sm sb s0 es' v dst tv t) /\
      extcall_default_ready cx rt T dst (lowered_value_type ce e) (SOME v) t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> (
  drule_all (BETA_RULE (Q.INST [`HP` |-> `\H. valid_horizon cx st0 H tr`]
    (SPEC_ALL compile_materialize_vv_owned_path))) >> strip_tac >>
  qexists_tac `t` >>
  conj_tac
  >- (simp[gas_marked_exec_def] >>
      drule read_result_gas_obs >> simp[]) >>
  simp[] >>
  `materialize_owned_post H0 ctx func ce cx e es sa sm sb s0 es' v dst tv t`
    by metis_tac[] >>
  qpat_x_assum `materialize_owned_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  rewrite_tac[materialize_owned_post_def] >> strip_tac >>
  `alloca_inv t` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ es' t` mp_tac >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `w2n w + type_memory_size tv <= t.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def] >>
  simp[extcall_default_ready_def] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  gvs[] >> decide_tac)
QED

Theorem extcall_request_positional_head_marked:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce tail)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (snap,sb) /\
  ~exprs_can_mutate ce tail /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL raw) ee (OK s) /\ ee.gas_obs = [] /\
  read_result cx raw ee = (INL v,ee) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv s) /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dv /\
  value_has_type sv v /\ value_has_type dv v /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u.
    gas_marked_exec F (ctx,func) (eval_exprs cx [e]) (es,s0)
      marks (INL [v]) ee (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (if is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))
     then ?op.
       snap = StackValue (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) op /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
          expr_post H ctx func ce cx e es sa sb s0 ee v op u)
     else sb = sm /\ u = s /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
          vv_post H ctx func ce cx e es sa sb s0 ee raw vv u) /\
       ((?tag p. vv = LocatedValue tag p /\
           snap = LocatedValue (lowered_value_type ce e) p /\
           vv_holds ce cx (lowered_value_type ce e) raw snap ee u /\
           vv_at ce cx (post_value_type ce e) sa sb ee raw snap u /\
           val_footprint sv v = val_footprint dv v) \/
        (?tag op. vv = StackValue tag op /\ snap = StackValue tag op /\
           (!H. valid_horizon cx st0 H ee.storage_trace ==>
              expr_post H ctx func ce cx e es sa sb s0 ee v op u))))
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))`
  >- (drule_all extcall_request_word_snapshot_marked_horizons >>
      strip_tac >>
      `v' = v` by
        (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >>
         disch_then (mp_tac o Q.SPEC `[]` o CONJUNCT1) >> gvs[]) >>
      qpat_x_assum `v' = v` SUBST_ALL_TAC >>
      qexists_tac `u` >> simp[] >>
      conj_tac
      >- (`gas_marked_exec F (ctx,func)
             (bind (eval_expr cx e) (read_result cx)) (es,s0)
             marks (INL v) ee (OK u)` by
            (once_rewrite_tac[GSYM APPEND_NIL] >>
             irule gas_marked_exec_bind_normal >>
             goal_assum (drule_at Any) >> simp[]) >>
          qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
          simp[gas_marked_exec_def] >> strip_tac >>
          simp[exprSimWordArgsTheory.eval_exprs_cons_action, bind_def,
               exprSimWordArgsTheory.eval_exprs_nil, return_def]) >>
      qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      drule fragGasModeTheory.gas_marked_path_exec >>
      metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `vv_holds ce cx (post_value_type ce e) raw vv ee s /\
   vv_at ce cx (post_value_type ce e) sa sm ee raw vv s` by
    metis_tac[vv_post_def] >>
  Cases_on `vv`
  >- (rename1 `StackValue tag op` >>
      gvs[ext_call_arg_value_def, vv_type_def,
          compile_snapshot_vv_def, comp_return_def] >>
      `gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
          [] (INL v) ee (OK s)` by
        (simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
              fragGasPathTheory.gas_path_rules] >>
         drule read_result_gas_obs >> simp[]) >>
      `gas_marked_exec F (ctx,func)
          (bind (eval_expr cx e) (read_result cx)) (es,s0)
          marks (INL v) ee (OK s)` by
        (once_rewrite_tac[GSYM APPEND_NIL] >>
         irule gas_marked_exec_bind_normal >>
         goal_assum (drule_at Any) >> simp[]) >>
      conj_tac
      >- (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
          simp[gas_marked_exec_def] >> strip_tac >>
          simp[exprSimWordArgsTheory.eval_exprs_cons_action, bind_def,
               exprSimWordArgsTheory.eval_exprs_nil, return_def]) >>
      metis_tac[abiEncodeMaterializeTheory.materialize_stack_vv_post_read]) >>
  rename1 `LocatedValue tag p` >>
  `~is_word_type (lowered_value_type ce e)` by
    gvs[ext_call_arg_value_def, vv_type_def] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by
    metis_tac[arg_type_fits_word_type] >>
  `post_value_type ce e = lowered_value_type ce e \/
   p.ptr_location = LocMemory /\
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[abiEncodeMaterializeTheory.materialize_compiled_nonword_capture_layout] >>
  `sb = sm /\ snap = LocatedValue (lowered_value_type ce e) p /\
   vv_holds ce cx (lowered_value_type ce e) raw snap ee s /\
   vv_at ce cx (post_value_type ce e) sa sm ee raw snap s /\
   val_footprint sv v = val_footprint dv v` by
    (irule extcall_request_nonword_snapshot_capture >>
     simp[] >> metis_tac[]) >>
  `gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
      [] (INL v) ee (OK s)` by
    (simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
          fragGasPathTheory.gas_path_rules] >>
     drule read_result_gas_obs >> simp[]) >>
  `gas_marked_exec F (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      marks (INL v) ee (OK s)` by
    (once_rewrite_tac[GSYM APPEND_NIL] >>
     irule gas_marked_exec_bind_normal >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `s` >> gvs[] >>
  qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  simp[exprSimWordArgsTheory.eval_exprs_cons_action, bind_def,
       exprSimWordArgsTheory.eval_exprs_nil, return_def]
QED

(* Each induction step exposes exactly the evaluation/snapshot/suffix cuts;
   in particular the head is compiled at its source type, not its ABI type. *)
Theorem extcall_request_positional_cut[local]:
  compile_ext_call_args compile_expr ce kws
    (MAP (lowered_value_type ce) (e::es)) (e::es) sa = (vals,sb) ==>
  ?vv sm snap sh rest.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (es ++ kws))
      (ext_call_arg_value (lowered_value_type ce e) vv) sm = (snap,sh) /\
    compile_ext_call_args compile_expr ce kws
      (MAP (lowered_value_type ce) es) es sh = (rest,sb) /\
    vals = snap::rest
Proof
  simp[compile_ext_call_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED

Theorem extcall_request_positional_nil[local]:
  expr_sim_inv ce cx env ea /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func ce cx ea r0 /\
    storage_well_formed_on cx ea (FST H)) /\
  ~r0.vs_halted /\ r0.vs_current_bb = ca.cs_current_bb /\
  r0.vs_inst_idx = LENGTH ca.cs_current_insts /\ local_ptrs_reserved ce ca /\
  (!vs. storage_trace_frame (kont vs)) /\
  (!ee t.
    (?H0. valid_horizon cx st0 H0 ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H)) /\
    wb_frame ce ea ee ca r0 t /\
    ~t.vs_halted /\ t.vs_current_bb = ca.cs_current_bb /\
    t.vs_inst_idx = LENGTH ca.cs_current_insts /\ ee.gas_obs = [] /\
    outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts /\
    MAP FDOM ea.scopes = MAP FDOM ee.scopes /\ local_ptrs_reserved ce ca /\
    expr_sim_inv ce cx env ee /\
    (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (ea with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
    pure_frame ce func ea ca r0 t ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0 (kont []) (ee,t) Q
      (\H res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_exprs cx []) kont) (ea,r0) Q (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, return_def] >>
  asm_rewrite_tac[bind_return] >>
  reverse (Cases_on `storage_trace_domain cx st0 ea.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[]) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
       storage_well_formed_on cx (ea with gas_obs := []) (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
     strip_tac >>
     irule (iffRL storage_well_formed_on_backends) >>
     qexists_tac `ea` >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) cx st0 (kont [])
     (ea with gas_obs := [],r0) Q (\H res ee r. expr_exit res r)` by
    (first_x_assum irule >>
     simp[exprSimWordArgsTheory.wb_frame_refl, expr_sim_inv_gas_obs] >>
     conj_tac >- metis_tac[storage_trace_domain_def] >>
     fs[expr_sim_inv_def,
        vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed]) >>
  drule gasOutcomeTheory.gas_outcome_start_gas_obs >>
  disch_then (qspec_then `ea.gas_obs` mp_tac) >> simp[]
QED

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
