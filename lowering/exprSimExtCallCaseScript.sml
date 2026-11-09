(*
 * Expression simulation: extcall and staticcall, as one case lemma
 *
 * extcall/staticcall in SOME oracle mode, including reverts and
 * default_return_value (#553).  The source evaluates the target, then the
 * positional arguments without reading them (eval_expr_results), then the
 * keyword operands, and reads the arguments last; the hypotheses of
 * compile_extcall_case give the operands' judgments in that order, as the
 * body induction's hypotheses do (bodySimCallCases's body_extcall_case).
 * exprSimCallExtcall and bodySimCallExtcall derive the two piece theorems
 * from it.
 *
 * TOP-LEVEL:
 *   compile_extcall_case — extcall's expr_sim_case and expr_vv_case from
 *     its operands' judgments
 *
 * ADMITTED:
 *   vv_post_pure_memory_frame — an effect-free operand's fragment keeps
 *     the live locals' bytes and writes memory only inside its own
 *     allocations.  It lets a positional memory
 *     or immutable operand, read only after the later operands, keep its
 *     value.  Held for the posts-interface round.
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
  extCallSeamPrecheck extCallSeamOracle extCallSeamFrame extCallSeamFinish
  extCallSeamSummary exprLowering emitHelper rawCallFragPath compileEnv
  exprExtRequestOperandCps exprExtRequestPrefix exprExtRequestValue
  exprLoweringProps exprSafeOperand fragGasPath gasSummary gasSummaryCompose

(* A storage or transient pointer an effect-free operand leaves reads live
   slots at es': no byte of the slots it reads is dead but those its own
   type leaves dead (storage_read_live). *)
Theorem vv_post_storage_live:
  !ctx func cenv cx e es sa sb s0 es' tv vv s t p w tvt.
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ~expr_has_effect e /\
    vv = LocatedValue t p /\
    eval_operand p.ptr_operand s = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tvt ==>
    (p.ptr_location = LocStorage ==>
     storage_read_live cx F (get_storage cx es' F) w tvt) /\
    (p.ptr_location = LocTransient ==>
     storage_read_live cx T (get_storage cx es' T) w tvt)
Proof
  rpt strip_tac >> gvs[vv_post_def] >> metis_tac[]
QED

(* An effect-free operand's fragment pops no scope and writes memory only
   inside allocations its own ALLOCA instructions make (func's ALLOCAs with
   ids from sa.cs_next_id): the live locals keep their bytes, and so does
   any region clear of those allocations, the constructor's immutable
   staging included.  A positional operand captured in memory, read only
   after the later operands, keeps its value. *)
Theorem vv_post_pure_memory_frame:
  !ctx func cenv cx e es sa sb s0 es' tv vv s.
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
    (!off len.
       (!inst b sz.
          MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
          compileEnv$regions_disjoint off len b sz) ==>
       mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory)
Proof
  (* Held for the posts-interface round: follows from vv_post_def once it
     frames an effect-free operand's memory writes to its own allocations. *)
  cheat
QED

(* Source boundary: positional locations are read only after kwargs. *)
Theorem eval_extcall_stages:
  eval_expr cx (Call ann (ExtCall static skip sig opts) args dflt) =
    do target <- eval_exprs cx (TAKE 1 args);
       results <- eval_expr_results cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args));
       kwargs <- eval_exprs cx (DROP (1 + LENGTH (FST (SND sig))) args);
       vs <- read_results cx results;
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
   evaluated and read every operand, keeping es's scopes, and built the
   request (target, value, calldata); the CALL's operands evaluate to them, calldata is the bytes
   at call_offset, and the return buffer (cap bytes at buf_op, an alloca
   made after sa) is clear of the locals, the immutables, the allocas before
   sa and a memory default. *)
Definition extcall_request_ready_def:
  extcall_request_ready ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t <=>
    stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\ ee.gas_obs = [] /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    outcomes_accounts_typed ee.outcomes /\
    accounts_runtime_well_typed ee.accounts /\
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
             compileEnv$regions_disjoint (w2n ro) cap b sz) /\
          (!name b sz. local_region cenv es.scopes s0 name b sz ==>
             compileEnv$regions_disjoint (w2n ro) cap b sz) /\
          (!aid b sz. aid < sa.cs_next_id /\
             FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
             compileEnv$regions_disjoint (w2n ro) cap b sz) /\
          (cenv.ce_is_ctor ==> !name tv v off.
             FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
               SOME (ImmutableLoc off) /\
             FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
                        NONE => FEMPTY
                      | SOME imms => get_source_immutables cenv.ce_module imms)
               name = SOME (tv,v) ==>
             compileEnv$regions_disjoint (w2n ro) cap off
               (type_memory_size tv)) /\
          (!d w tv. default_opt = SOME d /\ ~is_word_type default_ty /\
             eval_operand default_op t = SOME w /\
             evaluate_type (get_tenv cx) default_ty = SOME tv ==>
             compileEnv$regions_disjoint (w2n ro) cap (w2n w)
               (val_footprint tv d))) /\
    extcall_default_ready cx ret_type has_default default_op default_ty
      default_opt t
End

(* At sr, the start of the block after a successful call: the source has
   the call's returndata, which Venom holds too, still with es's scopes,
   and the return buffer (an
   alloca made after sa) holds its first cap bytes. *)
Definition extcall_returned_def:
  extcall_returned ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap target
      has_default default_op default_ty default_opt returnData ee t <=>
    stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = sr.cs_current_bb /\
    t.vs_inst_idx = LENGTH sr.cs_current_insts /\ ee.gas_obs = [] /\
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

(* (1) Operands and request.  The lowering up to the extcodesize check, run
   against the source up to the built calldata: whatever runs the rest of
   eval_ext_call from a ready request, with the lowered call step at sp and
   the return handling at sr, runs the whole call. *)
Theorem extcall_request_setup:
  !nocalls ctx func cenv cx env ann is_static skip fname arg_types ret_type
   opts args dflt ty es sa sb vv s0 Q.
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       results_case nocalls ctx func cenv cx
         (TAKE (LENGTH arg_types) (DROP 1 args))) /\
    (!s target t s' results t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_expr_results cx (TAKE (LENGTH arg_types) (DROP 1 args)) s' =
         (INL results, t') ==>
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
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
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
       extcall_request_ready ctx func cenv cx ret_type es sa s0 sp is_static
         addr_op value_op gas_op buf_op call_offset call_len
         (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type))
         target value_opt calldata has_default default_op default_ty
         (ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)) ee t ==>
       ?marks. gas_summary_at F (ctx,func) marks
         (eval_ext_call cx is_static skip (fname,arg_types,ret_type) opts
            (target_v :: rest)) (ee,t) Q (\res ee r. expr_exit res r)) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_expr cx
         (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
            args dflt)) (es,s0) Q (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `args`
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      simp[gasContextTheory.gas_admissible_def] >>
      disch_then (qspecl_then [`[]`, `INR (Error (TypeError "ExtCall operands"))`, `es with gas_obs := []`] mp_tac) >>
      simp[Once evaluate_def] >>
      simp[evaluate_def, bind_return, read_results_def, eval_ext_call_def,
           vyperStateTheory.raise_def, expr_vv_res_ok_def]) >>
  rename1 `h::rest` >>
  gvs[arithmeticTheory.ADD1] >>
  qpat_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[NoAsms, Once compile_expr_def, LET_THM,
       exprCallbackContractsTheory.compile_call_child_calls] >> strip_tac >>
  drule exprExtRequestShapeTheory.extrequest_compile_call_split >> strip_tac >>
  qpat_x_assum `let call_types = _ in _` mp_tac >>
  simp[NoAsms, LET_THM] >> pairarg_tac >> simp[] >> strip_tac >>
  drule_all exprExtRequestCodeTheory.extrequest_operand_code >> strip_tac >>
  fs[exprExtRequestStagesSourceTheory.extrequest_source_stages] >>
  irule (BETA_RULE (Q.INST [`kont` |->
    `\target rs kwargs. vyperState$bind (read_results cx rs) (\vs.
       eval_ext_call cx is_static' skip (fname,arg_types,ret_type) opts
         (target::(vs ++ kwargs)))`]
    exprExtRequestOperandCpsTheory.extrequest_operand_cps)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_multi_vvs _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  qexistsl [`is_static'`, `nocalls`, `env`, `dflt`, `ann`] >>
  simp[vv_post_storage_live, vv_post_pure_memory_frame] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[vv_post_storage_live] >>
  conj_tac >- metis_tac[vv_post_pure_memory_frame] >>
  rpt gen_tac >> strip_tac >>
  `?posvs. read_results cx rs ee = (INL posvs,ee)` by
    (qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SRULE [exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
     drule_all exprExtRequestStrongCaptureTheory.extrequest_strong_captures_projection >> strip_tac >>
     drule exprExtRequestCaptureTheory.extrequest_captures_read >> metis_tac[]) >>
  drule_at (Pat `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    exprExtRequestTypedCellsTheory.extrequest_call_typed_cells >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `extrequest_results_success _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_results _ _ _ = _`)) >>
  disch_then (qspec_then `target` mp_tac) >>
  (impl_tac >- (qexists_tac `used` >> simp[])) >> strip_tac >>
  drule_all exprExtRequestGasSelectionsTheory.extrequest_kwargs_gas_endpoint >> strip_tac >>
  drule_at (Pat `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    exprExtRequestAbiFitsTheory.extrequest_call_positional_calldata >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `extrequest_results_success _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_results _ _ _ = _`)) >>
  disch_then (qspec_then `target` mp_tac) >>
  (impl_tac >- (qexists_tac `used` >> simp[])) >> strip_tac >>
  drule_all exprExtRequestShapeTheory.extrequest_compile_kwargs_code >> strip_tac >>
  drule_all exprExtRequestPrefixTheory.extrequest_tuple_cells_history >> strip_tac >>
  `expr_body_pre cenv cx env h es` by
    (irule exprExtRequestShapeTheory.extrequest_body_pre_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     gvs[expr_body_pre_def]) >>
  `expr_sim_inv cenv cx env esA` by
    (qpat_assum `!tail. vyperState$bind (eval_expr cx h) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env h (es with gas_obs := used)` by simp[] >>
     fs[vyperStateTheory.bind_def] >>
     drule_at (Pat `(case _ of _ => _ | _ => _) = _`)
       (SRULE [vyperStateTheory.bind_def] exprSimSourceTheory.expr_body_pre_eval) >>
     simp[]) >>
  drule exprExtRequestStagesSourceTheory.extrequest_operand_body_pre >> strip_tac >>
  `expr_sim_inv cenv cx env esB` by
    (qpat_assum `extrequest_results_success _ _ _ _ _`
       (strip_assume_tac o SRULE [exprExtRequestUnreadCpsTheory.extrequest_results_success_def]) >>
     `expr_sim_inv cenv cx env mid` by
       (irule exprExtRequestStagesSourceTheory.extrequest_results_preserves_inv >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_TAKE, EVERY_DEF]) >> simp[]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SRULE [exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
     irule exprExtRequestStagesSourceTheory.extrequest_exprs_preserves_inv >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_DROP, EVERY_DEF]) >>
  `SUM (MAP (type_memory_bytes cenv)
      (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest))) < 2 ** 64 /\
   MAX (abi_size_bound cenv.ce_struct_fields
      (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest))))
     (abi_size_bound cenv.ce_struct_fields
      (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) + 32 < 2 ** 64` by
    (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (strip_assume_tac o SRULE [expr_body_pre_def,
          allocLimitsTheory.alloc_limits_expr_def,
          allocLimitsTheory.ext_call_alloc_ok_def, LET_THM]) >> simp[]) >>
  drule exprExtRequestTypedCellsTheory.extrequest_cells_layout >> strip_tac >>
  `LENGTH arg_vals = LENGTH (TAKE (LENGTH arg_types) rest)` by
    (qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ s4 t'` mp_tac >>
     simp[NoAsms, exprExtRequestStrongCaptureTheory.extrequest_strong_captures_def] >>
     strip_tac >> imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `MAP (\(e,r,vv,ty,tv,v). vv) cells = arg_vals` by
    (qpat_assum `MAP _ cells = ZIP _` (mp_tac o Q.AP_TERM `MAP FST`) >>
     simp[MAP_MAP_o, MAP_ZIP] >>
     `MAP (FST o (\(e,r,vv,ty,tv,v). (vv,ty))) cells =
      MAP (\(e,r,vv,ty,tv,v). vv) cells` by
       (irule MAP_CONG >> simp[] >> rpt strip_tac >> PairCases_on `x` >> simp[]) >>
     simp[]) >>
  `local_ptrs_reserved cenv s4` by
    fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
  `SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) =
     type_memory_size_list tvs` by
    (qpat_x_assum `MAP (\(e,r,vv,ty,tv,v). tv) cells = tvs` (fn th => rewrite_tac[GSYM th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Induct_on `cells` >> simp[valueEncodingTheory.type_memory_size_def] >>
     qx_gen_tac `cell` >> PairCases_on `cell` >> simp[valueEncodingTheory.type_memory_size_def]) >>
  `ee.gas_obs = []` by
    fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def] >>
  `SUM (MAP (type_memory_bytes cenv)
      (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest))) =
    type_memory_size_list tvs` by metis_tac[] >>
  `?t'' (w:bytes32).
    gas_marked_path F ctx func t' 0 (OK t'') /\
    stmt_state_rel ctx func cenv cx ee t'' /\
    extrequest_history_frame cenv cx ee s4 t' ee sp t'' /\
    ~t''.vs_halted /\ t''.vs_current_bb = sp.cs_current_bb /\
    t''.vs_inst_idx = LENGTH sp.cs_current_insts /\
    eval_operand len t'' = SOME (n2w (4 + LENGTH (enc
      (vyper_to_abi_type (get_tenv cx) (TupleT
        (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest)))) av))) /\
    eval_operand off t'' = SOME (n2w (w2n w + 28)) /\
    read_memory (w2n w + 28) (4 + LENGTH (enc
      (vyper_to_abi_type (get_tenv cx) (TupleT
        (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest)))) av)) t'' =
      function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types) ++
      enc (vyper_to_abi_type (get_tenv cx) (TupleT
        (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest)))) av /\
    FLOOKUP t''.vs_allocas s4.cs_next_id = SOME (w2n w, MAX
      (abi_size_bound cenv.ce_struct_fields (TupleT
        (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest))))
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) + 32) /\
    w2n w + abi_size_bound cenv.ce_struct_fields
      (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) < dimword (:256) /\
    local_ptrs_reserved cenv sp /\ safe_operand sp len /\ safe_operand sp off /\
    eval_operand buf t'' = SOME w /\ safe_operand sp buf` by
   (Cases_on `arg_vals = []`
  >- (`arg_types = []` by
        (drule exprExtRequestShapeTheory.extrequest_body_typed >>
         simp[Once vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
         fs[LENGTH_TAKE_EQ, LENGTH_NIL]) >>
      fs[valueEncodingTheory.type_memory_size_def] >>
      drule_at (Pat `extrequest_compile_prefix _ _ _ _ _ _ _ _ _ = _`)
        exprExtRequestPrefixTheory.extrequest_empty_prefix_endpoint >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (simp[] >> fs[wordsTheory.dimword_def] >> decide_tac)) >>
      strip_tac >>
      qpat_x_assum `posvs = []` SUBST_ALL_TAC >>
      gvs[vyperABITheory.vyper_to_abi_def] >>
      qexistsl_tac [`t''`, `w`] >> simp[contractABITheory.enc_def, listTheory.REV_DEF, wordsTheory.dimword_def]) >>
  `TAKE (LENGTH arg_types) rest <> []` by metis_tac[LENGTH_NIL] >>
  drule_at (Pat `extrequest_compile_prefix _ _ _ _ _ _ _ _ _ = _`)
    exprExtRequestPrefixTheory.extrequest_tuple_prefix_endpoint >>
  disch_then (drule_at (Pat `EVERY _ cells`)) >>
  disch_then (qspecl_then [`posvs`, `tvs`, `env`, `av`] mp_tac) >>
  (impl_tac >- (simp[valueEncodingTheory.type_memory_size_def] >>
    fs[wordsTheory.dimword_def] >> decide_tac)) >>
  strip_tac >> qexistsl_tac [`t''`, `w`] >> simp[]) >>
  `extrequest_history_frame cenv cx ee s3 t ee sp t''` by
    (irule exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >>
       fs[exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
     qexistsl_tac [`ee`, `s4`, `t'`] >> simp[]) >>
  `wb_frame cenv es sa s0 t''` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> reverse conj_tac
     >- (qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
     qexistsl_tac [`ee`, `s3`, `t`] >> simp[] >>
     irule exprExtRequestPrefixTheory.extrequest_history_writeback >>
     qexistsl_tac [`cx`, `ee`, `sp`] >> simp[]) >>
  `extrequest_kwarg_selection cenv cx ret_type EKDefault
     (ext_call_kwarg EKDefault opts vs) default_opt ee sp t''` by
    (irule exprExtRequestKwargsTheory.extrequest_kwarg_selection_transport >>
     qexistsl_tac [`ctx`, `ee`, `func`, `s4`, `t'`] >> simp[]) >>
  `extrequest_kwarg_selection cenv cx ret_type EKValue
     (ext_call_kwarg EKValue opts vs)
     (OPTION_MAP (\op. (op,ret_type)) value_opt) ee sp t''` by
    (irule exprExtRequestKwargsTheory.extrequest_kwarg_selection_transport >>
     qexistsl_tac [`ctx`, `ee`, `func`, `s4`, `t'`] >> simp[]) >>
  `eval_operand addr_op t'' = SOME (w2w target_addr)` by
    (irule exprExtRequestReconstructTheory.extrequest_history_operand >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any)) >>
  `eval_operand gas_op t'' = SOME gw` by
    (irule exprExtRequestReconstructTheory.extrequest_history_operand >>
     qexistsl_tac [`cenv`, `cx`, `ee`, `ee`, `s4`, `sp`, `t'`] >> simp[]) >>
  `extcall_default_ready cx ret_type has_default default_op default_ty
      (ext_call_kwarg EKDefault opts vs) t''` by
    (`IS_SOME default_opt ==> ret_type <> NoneT` by
       (Cases_on `default_opt` >> simp[] >> PairCases_on `x` >>
        drule_all exprExtRequestShapeTheory.extrequest_body_default_type >> simp[]) >>
     qpat_assum `IS_SOME default_opt ==> _` mp_tac >>
     qpat_assum `extrequest_kwarg_selection _ _ _ EKDefault _ _ _ sp t''` mp_tac >>
     qpat_assum `_ = (has_default,default_op,default_ty)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `default_opt` >>
     fs[extcall_default_ready_def,
        exprExtRequestKwargsTheory.extrequest_kwarg_selection_def] >>
     PairCases_on `x` >> gvs[] >>
     `ret_type <> NoneT` by fs[] >>
     conj_tac >- (Cases_on `ext_call_kwarg EKDefault opts vs` >> simp[] >> fs[]) >>
     rpt strip_tac >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def] >>
     `?w. eval_operand default_op t'' = SOME w` by
       (qpat_assum `expr_val_rel _ _ _ default_op t''` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[expr_val_rel_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `?inst p. MEM inst (fn_insts func) /\
      inst.inst_id = s4.cs_next_id /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [p] /\
      not_local_ptr cenv ee.scopes p /\ s4.cs_next_id < sp.cs_next_id` by
    (drule exprExtRequestPrefixTheory.extrequest_prefix_split >> strip_tac >>
     (`fn_has_code s4 sm func /\ ci_mono s4 sm /\ ci_mono sm sp` by
       (Cases_on `arg_vals = []`
        >- (fs[] >>
            `ci_mono s4 sm` by
              metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
            `ci_mono sm sn` by
              metis_tac[ci_mono_emit_void, pairTheory.SND] >>
            `ci_mono sn sp` by
              metis_tac[ci_mono_emit_op, pairTheory.SND] >>
            fs[ci_mono_def] >>
            metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
        fs[] >>
        drule_all exprExtRequestPrefixTheory.extrequest_tuple_prefix_code >>
        strip_tac >> fs[ci_mono_def] >>
        metis_tac[cs_extends_trans]) >>
     qpat_assum `compile_alloc_buffer _ s4 = _`
       (mp_then Any mp_tac exprSimAllocTheory.buffer_alloc_code) >>
     disch_then drule >> strip_tac >>
     qpat_assum `compile_alloc_buffer _ s4 = _`
       (strip_assume_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts) >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def] >>
     conj_tac >- (irule exprSimOperandsTheory.fresh_not_local_ptr >>
       qexists_tac `s4` >> simp[]) >>
     fs[ci_mono_def] >> decide_tac)) >>
  `!name b sz. local_region cenv ee.scopes t'' name b sz ==>
      compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) b sz` by
    (rpt strip_tac >>
     `alloca_inv t'' /\ local_ptrs_rel func cenv ee.scopes t''` by
       (qpat_assum `stmt_state_rel ctx func cenv cx ee t''` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[stmt_state_rel_def, state_rel_def]) >>
     qpat_assum `inst.inst_id = s4.cs_next_id`
       (fn th => rule_assum_tac (ONCE_REWRITE_RULE [GSYM th])) >>
     drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[compileEnvTheory.regions_disjoint_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
      compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) b sz` by
    (drule_all wordArgsPtrTheory.wb_frame_local_regions >> strip_tac >>
     metis_tac[]) >>
  `!aid b sz. aid <> s4.cs_next_id /\
      FLOOKUP t''.vs_allocas aid = SOME (b,sz) ==>
      compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) b sz` by
    (`allocas_non_overlapping t''` by
       (qpat_assum `stmt_state_rel ctx func cenv cx ee t''` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
     qpat_assum `FLOOKUP t''.vs_allocas s4.cs_next_id = SOME _` mp_tac >>
     qpat_assum `allocas_non_overlapping t''` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomMemDefsTheory.allocas_non_overlapping_def] >> rpt strip_tac >>
     first_x_assum drule >> disch_then drule >> simp[] >>
     simp[compileEnvTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
     decide_tac) >>
  `!aid b sz. aid < sa.cs_next_id /\
      FLOOKUP t''.vs_allocas aid = SOME (b,sz) ==>
      compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) b sz` by
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[] >>
     fs[ci_mono_def] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
        name = SOME (tv,v) ==>
      compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
        off (type_memory_size tv)` by
    (`immutable_alloca_sep func cenv cx ee t''` by
       (qpat_assum `stmt_state_rel ctx func cenv cx ee t''` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
     rpt strip_tac >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then drule >> disch_then drule >> strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspec_then `inst` mp_tac) >>
     simp[] >>
     simp[compileEnvTheory.regions_disjoint_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!d dw tv. ext_call_kwarg EKDefault opts vs = SOME d /\
      ~is_word_type default_ty /\ eval_operand default_op t'' = SOME dw /\
      evaluate_type (get_tenv cx) default_ty = SOME tv ==>
      compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
        (w2n dw) (val_footprint tv d)` by
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKDefault _ _ _ s4 t'` mp_tac >>
     qpat_assum `_ = (has_default,default_op,default_ty)` mp_tac >>
     qpat_assum `extrequest_history_frame _ _ _ s4 t' _ sp t''` mp_tac >>
     qpat_assum `!aid b sz. aid <> s4.cs_next_id /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `default_opt` >>
     fs[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def] >>
     PairCases_on `x` >> gvs[] >> rpt strip_tac >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def] >>
     `eval_operand default_op t'' = SOME w'` by
       (drule_all exprExtRequestReconstructTheory.extrequest_history_operand >> simp[]) >>
     `dw = w'` by gvs[] >> fs[] >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
     `FLOOKUP t''.vs_allocas aid = SOME (w2n w',size')` by metis_tac[] >>
     `compileEnv$regions_disjoint (w2n w)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
        (w2n w') size'` by (first_x_assum irule >> qexists_tac `aid` >> simp[]) >>
     fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts` by
    (qpat_assum `expr_sim_inv cenv cx env ee` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed]) >>
  `sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `safe_operand sp addr_op /\ safe_operand sp gas_op` by
    (conj_tac
     >- (irule safe_operand_mono >> qexists_tac `s3` >> simp[] >>
         fs[ci_mono_def] >> decide_tac) >>
     irule safe_operand_mono >> qexists_tac `s4` >> simp[] >> fs[ci_mono_def]) >>
  `safe_operand sp default_op` by
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKDefault _ _ _ sp t''` mp_tac >>
     qpat_assum `_ = (has_default,default_op,default_ty)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `default_opt` >>
     fs[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def, safe_operand_def] >>
     PairCases_on `x` >> gvs[] >>
     Cases_on `ext_call_kwarg EKDefault opts vs` >> gvs[] >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def, safe_operand_def]) >>
  `w2n w + MAX
      (abi_size_bound cenv.ce_struct_fields
        (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest))))
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) + 32
      <= t''.vs_alloca_next` by
    (qpat_assum `stmt_state_rel ctx func cenv cx ee t''` mp_tac >>
     qpat_assum `FLOOKUP t''.vs_allocas s4.cs_next_id = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `t''.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel ctx func cenv cx ee t''` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_state_rel_def, state_rel_def, alloca_room_def] >>
     strip_tac >> decide_tac) >>
  `safe_operand sp (case value_opt of NONE => Lit 0w | SOME v => v)` by
    (qpat_assum `extrequest_kwarg_selection _ _ _ EKValue _ _ _ sp t''` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `value_opt` >>
     simp[exprExtRequestKwargsTheory.extrequest_kwarg_selection_def, safe_operand_def] >>
     strip_tac >> Cases_on `ext_call_kwarg EKValue opts vs` >> gvs[] >>
     fs[exprExtRequestRetainedTheory.extrequest_retained_value_def, safe_operand_def]) >>
  `ext_call_opts_ok is_static' opts` by
    (qpat_assum `expr_body_pre cenv cx env (Call _ _ _ _) es` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[expr_body_pre_def] >>
     metis_tac[exprExtRequestShapeTheory.extrequest_typed_nonempty]) >>
  `extcall_request_ready ctx func cenv cx ret_type es sa s0 sp is_static'
      addr_op (case value_opt of NONE => Lit 0w | SOME v => v) gas_op buf off len
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
      target_addr
      (if is_static' then NONE else case ext_call_kwarg EKValue opts vs of
        NONE => SOME 0 | SOME v => dest_NumV v)
      (function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types) ++
        enc (vyper_to_abi_type (get_tenv cx)
          (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest)))) av)
      has_default default_op default_ty (ext_call_kwarg EKDefault opts vs) ee t''` by
    (simp[extcall_request_ready_def, wordsTheory.w2w_w2w] >>
     conj_tac >- wordsLib.WORD_DECIDE_TAC >>
     conj_tac >-
       (irule exprExtRequestValueTheory.extrequest_value_static >>
        goal_assum (drule_at Any)) >>
     conj_tac >-
       (qpat_assum `extrequest_kwarg_selection _ _ _ EKValue _ _ _ sp t''` mp_tac >>
        qpat_assum `ext_call_opts_ok is_static' opts` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        metis_tac[exprExtRequestValueTheory.extrequest_value_operand]) >>
     `!n a b p q D:num.
       n <= a /\ p + MAX a b + 32 <= q /\ q < D ==>
       n + 4 < D /\ p + b < D` by
       (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
        Cases_on `a <= b` >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
     `LENGTH (enc (vyper_to_abi_type (get_tenv cx)
        (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest)))) av) + 4
          < dimword (:256)` by
       (qpat_assum `!n a b p q D:num. _` mp_tac >>
        qpat_assum `LENGTH (enc _ av) <= _` mp_tac >>
        qpat_assum `w2n w + MAX _ _ + 32 <= _` mp_tac >>
        qpat_assum `t''.vs_alloca_next < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> metis_tac[]) >>
     `w2n w + 28 < dimword (:256)` by
       (qpat_assum `w2n w + MAX _ _ + 32 <= _` mp_tac >>
        qpat_assum `t''.vs_alloca_next < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> decide_tac) >>
     conj_tac >-
       (qpat_assum `read_memory (w2n w + 28) _ t'' = _` mp_tac >>
        qpat_assum `LENGTH (enc _ av) + 4 < dimword (:256)` mp_tac >>
        qpat_assum `w2n w + 28 < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        pure_rewrite_tac [cj 2 vyperABITheory.vyper_to_abi_type_def] >>
        simp[wordsTheory.dimword_def] >>
        CONV_TAC (DEPTH_CONV numLib.REDUCE_CONV) >>
        rpt strip_tac >>
        fs[arithmeticTheory.MOD_LESS, arithmeticTheory.ADD_COMM]) >>
     conj_tac >-
       (qpat_assum `w2n w + abi_size_bound _ _ < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[wordsTheory.dimword_def]) >>
     conj_tac >-
       (qexists_tac `s4.cs_next_id` >>
        qexists_tac `MAX
          (abi_size_bound cenv.ce_struct_fields
            (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH arg_types) rest))))
          (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) + 32` >>
        simp[] >> fs[ci_mono_def] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        `!a b:num. b <= MAX a b + 32` by
          (rpt gen_tac >> Cases_on `a <= b` >>
           simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
        metis_tac[]) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `!sp sr u result_op' addr_op' value_op gas_op' buf_op call_offset call_len has_default' default_op' default_ty' target_v rest' target calldata ee t. _`
    (mp_tac o SRULE [GSYM exprExtRequestShapeTheory.extrequest_compile_step_def,
                     GSYM exprExtRequestShapeTheory.extrequest_compile_return_def]) >>
  disch_then (drule_at (Pat `extrequest_compile_step _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `extrequest_compile_return _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then assume_tac >>
  `LENGTH posvs = LENGTH arg_types /\ LENGTH vs = LENGTH opts` by
    (qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SRULE [exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
     drule exprExtRequestShapeTheory.extrequest_body_typed >>
     simp[vyperTypeSystemTheory.well_typed_expr_def, LET_THM] >> strip_tac >>
     imp_res_tac vyperTypeArgFitsTheory.arg_types_fit_LENGTH >>
     qpat_assum `MAP (\(e,r,vv,ty,tv,v). v) cells = posvs` mp_tac >>
     qpat_assum `MAP (\(e,r,vv,ty,tv,v). ty) cells = _` mp_tac >>
     qpat_assum `LENGTH vs = LENGTH opts` mp_tac >>
     qpat_assum `LENGTH (MAP expr_type _) = LENGTH arg_types` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[LENGTH_MAP]) >>
  qpat_x_assum `!target_v rest' target calldata ee t. _`
    (qspecl_then [`target`, `posvs ++ vs`, `target_addr`] mp_tac) >>
  qpat_assum `LENGTH posvs = LENGTH arg_types`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[expr_type_def, TAKE_APPEND, DROP_APPEND] >>
  disch_then (qspecl_then [`ee`, `t''`] mp_tac) >>
  (impl_tac >-
    (qhdtm_assum `extcall_request_ready` mp_tac >>
     pure_rewrite_tac[cj 2 vyperABITheory.vyper_to_abi_type_def] >> simp[])) >>
  strip_tac >>
  `!tail. read_results cx rs (ee with gas_obs := tail) =
      (INL posvs, ee with gas_obs := tail)` by
    (gen_tac >>
     `extrequest_read_frame cx ee (ee with gas_obs := tail)` by
       simp[exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     drule exprExtRequestSuffixTheory.extrequest_read_results_frame >>
     disch_then (qspec_then `rs` mp_tac) >> simp[]) >>
  `gas_marked_path F ctx func t (if IS_NONE gas_opt then 1 else 0) (OK t'')` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  qhdtm_x_assum `gas_summary_at`
    (strip_assume_tac o SRULE [gasSummaryTheory.gas_summary_at_def]) >>
  (rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `REPLICATE (if IS_NONE gas_opt then 1 else 0) F ++ marks` >>
  disj1_tac >> rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`res`, `es_end`, `r`] >>
  conj_tac >-
    (irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
     qexistsl_tac [`ee`, `t''`, `posvs`] >>
     fs[gasSummaryTheory.gas_marked_exec_def, optionTheory.IS_NONE_EQ_NONE]) >>
  simp[])
QED


(* (2) The call step.  From a ready request at sp: the extcodesize check
   against the source's precheck, the CALL or STATICCALL as an oracle step
   (extCallOracleStep), and a failed call's returndata copy and REVERT
   against the source's RevertData; a successful call reaches sr with the
   returndata in the buffer. *)
Theorem extcall_call_step:
  !ctx func cenv cx es sa s0 sp sr u is_static skip ret_type
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
    extcall_request_ready ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t /\
    (!returnData ee' t'.
       extcall_returned ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap target
         has_default default_op default_ty default_opt returnData ee' t' ==>
       ?marks. gas_summary_at F (ctx,func) marks (k returnData) (ee',t') Q
                 (\res ee r. expr_exit res r)) ==>
    ?marks. gas_summary_at F (ctx,func) marks
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          value_opt' <- frame_call_value cx value_opt;
          returnData <- eval_ext_call_effects cx target calldata value_opt'
                          gas accounts;
          k returnData
       od) (ee,t) Q (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `comp_ignore_bind _ _ sp = _` mp_tac >>
  pure_once_rewrite_tac[comp_ignore_bind_def] >>
  pure_once_rewrite_tac[comp_bind_def] >> pure_rewrite_tac[LET_THM] >>
  pairarg_tac >> simp[] >>
  pure_once_rewrite_tac[comp_bind_def] >> pure_rewrite_tac[LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  fs[extcall_request_ready_def] >>
  drule_all extcall_source_prefix_obs >>
  disch_then (qspecl_then
    [`target`,`skip`,`ret_type`,`gas`,`calldata`,`value_opt`] strip_assume_tac) >>
  drule_all extcall_optional_precheck_path >>
  disch_then assume_tac >>
  drule extcall_optional_precheck_shape >> strip_tac >>
  drule extcall_finish_shape >> strip_tac >>
  rename1 `(if stat then emit_op STATICCALL _ else emit_op CALL _) cs' = (ok,cs'')` >>
  `emit_op (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr_op;call_offset;call_len;buf_op;Lit (n2w cap)]
       else [gas_op;addr_op;value_op;call_offset;call_len;buf_op;Lit (n2w cap)])
      cs' = (ok,cs'')` by (Cases_on `stat` >> gvs[]) >>
  `ci_mono cs' cs''` by
    (qmatch_asmsub_abbrev_tac `emit_op opc ops cs' = (ok,cs'')` >>
     qspecl_then [`opc`,`ops`,`cs'`] mp_tac ci_mono_emit_op >> simp[]) >>
  qmatch_asmsub_abbrev_tac `frag_path ctx sp cs' _ (\t'. _ /\ t' = pre) _` >>
  `stmt_state_rel ctx func cenv cx ee pre` by
    (simp[Abbr `pre`] >> irule (SRULE [] extcall_optional_precheck_stmt) >> simp[]) >>
  `wb_frame cenv es sa s0 pre` by
    (simp[Abbr `pre`] >> irule (SRULE [] extcall_optional_precheck_wb) >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >> simp[]) >>
  `!p. safe_operand sp p ==> eval_operand p pre = eval_operand p t` by
    (rpt strip_tac >> simp[Abbr `pre`] >>
     irule (SRULE [] extcall_optional_precheck_operands) >> simp[]) >>
  `pre.vs_memory = t.vs_memory /\ pre.vs_allocas = t.vs_allocas /\
   pre.vs_alloca_next = t.vs_alloca_next /\ pre.vs_fmp = t.vs_fmp /\
   pre.vs_halted = t.vs_halted /\ pre.vs_returndata = t.vs_returndata /\
   pre.vs_current_bb = t.vs_current_bb` by
    (simp[NoAsms, Abbr `pre`] >> irule (SRULE [] extcall_optional_precheck_fields) >> simp[]) >>
  `!scopes name b sz. local_region cenv scopes pre name b sz <=>
                     local_region cenv scopes t name b sz` by
    (rpt gen_tac >> simp[Abbr `pre`] >>
     irule (SRULE [] extcall_optional_precheck_regions) >> simp[]) >>
  `stat = IS_NONE value_opt` by (Cases_on `value_opt` >> gvs[]) >>
  `w2n (if stat then 0w else vw) =
     (case value_opt of NONE => 0 | SOME n => n)` by
    (Cases_on `value_opt` >> gvs[]) >>
  `cap < dimword (:256)` by simp[] >>
  `?gw. eval_operand gas_op pre = SOME gw` by (Cases_on `eval_operand gas_op t` >> gvs[]) >>
  drule_at (Pat `emit_op _ _ _ = _`) oracle_call_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ pre`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ pre`)) >>
  disch_then (qspec_then `value_opt` mp_tac) >>
  `eval_operand addr_op pre = SOME aw /\
   eval_operand call_offset pre = SOME ao /\ eval_operand call_len pre = SOME az /\
   eval_operand buf_op pre = SOME ro /\ eval_operand value_op pre = SOME vw` by simp[] >>
  `read_memory (w2n ao) (w2n az) pre = calldata` by
    (gvs[venomStateTheory.read_memory_def]) >>
  disch_then (drule_at (Pat `eval_operand value_op pre = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand buf_op pre = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand call_offset pre = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand call_len pre = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand addr_op pre = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand gas_op pre = SOME _`)) >>
  simp[] >>
  (impl_tac >- (fs[compileEnvTheory.regions_disjoint_def, DISJ_COMM] >>
                 rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `cs_extends cs' cs'' /\ cs_extends cs'' sr` by fs[ci_mono_def] >>
  `cs_extends cs' sr` by metis_tac[cs_extends_trans] >>
  `fn_has_code sp cs' func /\ fn_has_code cs' sr func` by
    (irule fragExecTheory.fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  `fn_has_code cs' cs'' func /\ fn_has_code cs'' sr func` by
    (irule fragExecTheory.fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `frag_path ctx sp cs' _ _ _` mp_tac >>
  simp[frag_path_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >>
  strip_tac
  >- suspend "precheck_pass"
  >> suspend "precheck_fail"
QED

Resume extcall_call_step[precheck_pass]:
  qpat_x_assum `frag_path ctx cs' cs'' _ _ _` mp_tac >>
  simp[frag_path_def] >> disch_then (qspec_then `func` mp_tac) >> simp[] >>
  strip_tac >>
  `eval_operand ok u' = SOME (if oc.co_success then 1w else 0w)` by
    (Cases_on `oc.co_success` >> gvs[venomExecSemanticsTheory.bool_to_word_def]) >>
  drule extcall_finish_path >>
  disch_then (qspec_then `oc.co_success` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand ok _ = _`)) >>
  simp[] >>
  disch_then (qspec_then `ctx` mp_tac) >>
  fs[wordsTheory.dimword_def] >>
  simp[frag_path_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >>
  qpat_x_assum `_ = OK u'` SUBST_ALL_TAC >>
  drule gas_path_normal >> strip_tac >> simp[] >>
  strip_tac
  >- suspend "call_success"
  >> suspend "call_failure"
QED

Resume extcall_call_step[call_success]:
  `!p. safe_operand sp p ==> eval_operand p u' = eval_operand p t` by simp[] >>
  `u'.vs_memory = (write_memory_with_expansion (w2n ro)
     (TAKE cap oc.co_returnData) t).vs_memory` by
    simp[venomStateTheory.write_memory_with_expansion_def] >>
  `extcall_default_ready cx ret_type has_default default_op default_ty default_opt u'` by
    (Cases_on `default_opt`
     >- fs[extcall_default_ready_def] >>
     fs[extcall_default_ready_def] >>
     gvs[] >>
     irule extcall_default_write_frame >>
     goal_assum (drule_at (Pat `expr_val_rel _ _ _ _ _`)) >>
     simp[] >> qexistsl [`w2n ro`, `TAKE cap oc.co_returnData`] >>
     simp[venomStateTheory.write_memory_with_expansion_def] >>
     fs[compileEnvTheory.regions_disjoint_def, LENGTH_TAKE_EQ] >>
     strip_tac >> fs[] >>
     Cases_on `cap <= LENGTH oc.co_returnData` >> gvs[] >> decide_tac) >>
  `extcall_default_ready cx ret_type has_default default_op default_ty default_opt
      (jump_to sr.cs_current_bb u')` by
    (fs[extcall_default_ready_def] >> rpt strip_tac >>
     gvs[extcall_jump_fields] >>
     irule extcall_default_operand_frame >>
     goal_assum (drule_at Any) >> simp[extcall_jump_fields]) >>
  `consumed.gas_obs = ee.gas_obs` by
    (drule vyperCallOutcomeTheory.take_call_outcome_frame >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `(SND (adopt_call_outcome rq oc consumed)).gas_obs = []` by
    (Cases_on `rq.cr_static` >> simp[vyperCallOutcomeTheory.adopt_call_outcome_equation]) >>
  `consumed.scopes = ee.scopes` by
    (drule vyperCallOutcomeTheory.take_call_outcome_frame >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `(SND (adopt_call_outcome rq oc consumed)).scopes = consumed.scopes` by
    (Cases_on `rq.cr_static` >> simp[vyperCallOutcomeTheory.adopt_call_outcome_equation]) >>
  `extcall_returned ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap target
      has_default default_op default_ty default_opt oc.co_returnData
      (SND (adopt_call_outcome rq oc consumed)) (jump_to sr.cs_current_bb u')` by
    (simp[extcall_returned_def, stmt_state_rel_jump_to, extcall_jump_wb_frame,
          extcall_jump_fields] >>
     fs[ci_mono_def] >>
     `sp.cs_next_id <= sr.cs_next_id /\ sp.cs_next_var <= sr.cs_next_var` by
       (fs[cs_extends_def] >> decide_tac) >>
     rpt conj_tac
     >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) 
     >- metis_tac[exprSafeOperandTheory.safe_operand_mono]
     >- metis_tac[exprSafeOperandTheory.safe_operand_mono]
     >- metis_tac[exprSafeOperandTheory.safe_operand_mono]
     >- (qexistsl [`live`, `buf_size`] >> simp[] >> decide_tac) >>
     metis_tac[]) >>
  `gas_path ctx func t (n + (n' + n'')) (OK (jump_to sr.cs_current_bb u'))` by
    (irule gas_path_then >> qexists `pre` >> conj_tac >- metis_tac[] >>
     irule gas_path_then >> qexists `u'` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!tail. _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_all extcall_marked_prefix >> strip_tac >>
  `?marks. gas_summary_at F (ctx,func) marks
    (vyperState$bind
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          amount' <- frame_call_value cx value_opt;
          eval_ext_call_effects cx target calldata amount' gas accounts od) k)
    (ee,t) Q (\res ee r. expr_exit res r)` suffices_by
      simp[vyperStateTheory.bind_assoc, vyperStateTheory.ignore_bind_def, SF ETA_ss] >>
  irule extcall_summary_bind_normal >>
  goal_assum (drule_at Any) >> simp[] >>
  first_x_assum irule >>
  `SND (adopt_call_outcome rq oc consumed) with gas_obs := [] =
     SND (adopt_call_outcome rq oc consumed)` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  asm_rewrite_tac[]
QED

Resume extcall_call_step[call_failure]:
  `gas_path ctx func t (n + (n' + n'')) (Abort Revert_abort t')` by
    (irule gas_path_then >> qexists `pre` >> conj_tac >- metis_tac[] >>
     irule gas_path_then >> qexists `u'` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!tail. _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_all extcall_marked_prefix >> strip_tac >>
  `?marks. gas_summary_at F (ctx,func) marks
    (vyperState$bind
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          amount' <- frame_call_value cx value_opt;
          eval_ext_call_effects cx target calldata amount' gas accounts od) k)
    (ee,t) Q (\res ee r. expr_exit res r)` suffices_by
      simp[vyperStateTheory.bind_assoc, vyperStateTheory.ignore_bind_def, SF ETA_ss] >>
  qexists `REPLICATE (n + (n' + n'')) F` >>
  irule extcall_summary_bind_exception >>
  goal_assum (drule_at Any) >> simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume extcall_call_step[precheck_fail]:
  qpat_x_assum `!tail. _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_all extcall_marked_prefix >> strip_tac >>
  `?marks. gas_summary_at F (ctx,func) marks
    (vyperState$bind
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          amount' <- frame_call_value cx value_opt;
          eval_ext_call_effects cx target calldata amount' gas accounts od) k)
    (ee,t) Q (\res ee r. expr_exit res r)` suffices_by
      simp[vyperStateTheory.bind_assoc, vyperStateTheory.ignore_bind_def, SF ETA_ss] >>
  qexists `REPLICATE n F` >> irule extcall_summary_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise extcall_call_step


(* (3) Return handling.  From sr after a successful call: void, the
   default on empty returndata (with the code recheck) and the bounded
   memory decode, whose rejection of returndata the source's
   evaluate_abi_decode_return rejects aborts. *)
Theorem extcall_return_values:
  !ctx func cenv cx env es ann is_static skip fname arg_types ret_type opts
   args dflt sa sb s0 sr result_op vv addr_op buf_op cap target
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
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    local_ptrs_reserved cenv sa /\
    extcall_returned ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap target
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
      (\res ee' t'. ?tv. res = INL tv /\
         vv_post ctx func cenv cx
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
    (!lbl bb. lookup_block lbl func.fn_blocks = SOME bb ==>
              phi_prefix_length bb.bb_instructions = 0) /\
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       results_case nocalls ctx func cenv cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args))) /\
    (!s target t s' results t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_expr_results cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 args)) s' =
         (INL results, t') ==>
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
                `dflt`, `ty`, `es`, `sa`, `sb`, `vv`, `s0`]
    MATCH_MP_TAC extcall_request_setup >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, ALL_TAC] >>
  rpt strip_tac >>
  `stat <=> value_opt = NONE` by fs[extcall_request_ready_def] >>
  drule_all eval_ext_call_request >>
  disch_then (qspecl_then [`skip`, `ret_type`] SUBST1_TAC) >>
  ho_match_mp_tac extcall_call_step >>
  qpat_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `comp_ignore_bind _ _ _ = _` (irule_at Any) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  irule extcall_return_values >>
  qpat_assum `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qexists_tac `result_op` >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, REFL_TAC,
         DISJ2_TAC >> rpt strip_tac >> res_tac]
QED
