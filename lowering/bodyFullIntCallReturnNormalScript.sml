(* Completed internal-call return, preserving the selected joint endpoint. *)
Theory bodyFullIntCallReturnNormal
Ancestors context[qualified,ignore_grammar]
  bodyFullIntCallDefs bodyIntCallSeams gasOutcomeFull
  fragGasOriginPtrInvoke intCallResultFull bodyFullIntCallReturnFrame
  bodyFullIntCallReturnSource bodyFullIntCallReturnHalt bodyFullForControl
  vyperInterpreter vyperState vyperAST vyperTyping bodyFullIntCallReturnTyping
  bodyFullIntCallReturnValue bodyFullHashKeccakFixed stateRelProj
  valueEncodingProofs valueCopyBytes bodyFullIntCallReturnMetadata
  exprLoweringProps exprSimDefs bodyFullIntCallNativeReturn bodyFullIntCallReturnWitness

Libs
  monadsyntax

Theorem intcall_return_source[local]:
  !cx name mut nr ss st v ee out prev rtv.
    intcall_callee_src cx name mut nr ss st = (INL v,ee) /\
    unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) ==>
    intcall_rest cx name mut nr ss prev rtv st =
      case safe_cast rtv v of
        NONE => (INR (Error (TypeError "IntCall cast ret")),out with scopes := prev)
      | SOME cv => (INL (Value cv),out with scopes := prev)
Proof
  rpt gen_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  Cases_on `q` >>
  simp[intcall_callee_src_def, ignore_bind_def, bind_def] >>
  strip_tac >>
  gvs[intcall_rest_def, ignore_bind_def, bind_def,
      finally_def, finally_unless_halt_def,
      pop_function_def, set_scopes_def,
      lift_option_type_def, lift_option_def, return_def] >>
  Cases_on `nr /\ ~is_view_mut mut` >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[unlock_if_nr_def, release_nonreentrant_lock_def,
      record_storage_event_def, get_transient_storage_def,
      update_transient_def, ignore_bind_def, bind_def, return_def,
      AllCaseEqs()] >>
  Cases_on `safe_cast rtv v` >>
  gvs[lift_option_type_def, lift_option_def, return_def, raise_def]
QED

(* All certificates below refer to the already selected INVOKE/store run. *)
(* Caller frame at the already selected result-store endpoint. *)
Theorem intcall_return_invoke_setup[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv ==>
  ?setup. ~t.vs_halted /\ inst.inst_opcode = INVOKE /\
    lookup_function lbl ctx.ctx_functions = SOME callee /\
    setup_callee callee argv t = SOME setup /\
    enters_block callee setup entered
Proof
  simp_tac bool_ss [fragGasFocusTheory.gas_invoke_entry_def] >>
  strip_tac >> gvs[] >>
  simp[contextCodegenRelTheory.enters_block_def] >> metis_tac[]
QED

Theorem intcall_return_caller_frame[local]:
 !tops ctx func cenv cx tenv name es sa sm vv s0 es0 DF lo d H G0 tn0
  mut nr args ret ss rr prev penv rtv es1 t G tn rc rb v ee Gc tc ir cs
  out outs returned.
 body_inv tops ctx cenv cx /\
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
   s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 local_ptrs_reserved cenv sa /\
 intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc rb
   sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
 unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\
 bind_outputs outs ir.iret_values
   (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned /\
 (!x. MEM x outs ==> ~not_fresh_at sa x) ==>
 storage_well_formed_on cx (out with scopes := prev) (FST H) /\
 (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
   lookup_var x returned = SOME w) /\
 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
   FLOOKUP returned.vs_allocas aid = SOME b) /\
 (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
   (!n lb lsz. local_region cenv es0.scopes s0 n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) ==>
   mem_bytes_at b sz returned.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
 locals_kept cenv es0 (out with scopes := prev) s0 returned
Proof
 rpt gen_tac >> strip_tac >>
 drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
 conj_tac >- suspend "storage" >>
 conj_tac >- suspend "vars" >>
 conj_tac >- suspend "allocas" >>
 conj_tac >- suspend "bytes" >>
 suspend "locals"
QED
Resume intcall_return_caller_frame[storage]:
 qhdtm_assum `intcall_callee_exit_full` mp_tac >>
 pure_rewrite_tac[intcall_callee_exit_full_def] >> strip_tac >>
 first_x_assum (qspecl_then [`v`,`ir`,`cs`] mp_tac) >>
 simp[] >> strip_tac >> gvs[] >>
 gvs[vyperStorageFootprintTheory.storage_well_formed_on_def,
     vyperStorageBackendTheory.get_storage_def] >>
 rpt strip_tac >>
 qpat_x_assum `!b slot tv. MEM (b,slot,tv) _ ==> _`
   (qspecl_then [`b`,`slot`,`tv`] mp_tac) >>
 Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED
Resume intcall_return_caller_frame[vars]:
 qhdtm_assum `intcall_entry_full` mp_tac >>
 pure_rewrite_tac[intcall_entry_full_def] >> metis_tac[]
QED
Resume intcall_return_caller_frame[allocas]:
 qhdtm_assum `intcall_entry_full` mp_tac >>
 pure_rewrite_tac[intcall_entry_full_def] >> metis_tac[]
QED
Resume intcall_return_caller_frame[bytes]:
 rpt strip_tac >>
 Cases_on `sz = 0` >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
 `stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
  expr_sim_inv cenv cx tenv (es1 with scopes := prev) /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> metis_tac[]) >>
 `alloca_inv t /\
  immutable_decl_sep cenv cx prev t.vs_vars t.vs_allocas t.vs_alloca_next` by
   (drule stmt_state_rel_local_ptrs_alloca >>
    drule return_stmt_immutable_sep >>
    simp[immutable_alloca_sep_def]) >>
 `cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b` by
   (strip_tac >> `b <= b /\ b < b + sz` by simp[] >>
    drule_all bodyFullIntCallReturnFrameTheory.intcall_alloca_immutable_prefix_disjoint >> simp[]) >>
 `b + sz <= t.vs_alloca_next` by
   metis_tac[allocaSiteResourceTheory.alloca_site_registered_below] >>
 `!id a len. FLOOKUP t.vs_allocas id = SOME (a,len) /\
   sa.cs_next_id <= id /\ id < sm.cs_next_id ==>
   regions_disjoint b sz a len` by
   (rpt strip_tac >>
    `aid <> id` by decide_tac >>
    qpat_assum `alloca_inv t` mp_tac >>
    pure_rewrite_tac[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def] >> strip_tac >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
 `mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory` by
   (qhdtm_assum `intcall_callee_exit_full` mp_tac >>
    pure_rewrite_tac[intcall_callee_exit_full_def,intcall_callee_exit_def] >>
    simp[exprSimDefsTheory.expr_exit_def] >> strip_tac >>
    qpat_x_assum `!b sz. _ ==> mem_bytes_at b sz cs.vs_memory = _`
      (qspecl_then [`b`,`sz`] mp_tac) >> simp[] >> metis_tac[]) >>
 simp[]
QED
Resume intcall_return_caller_frame[locals]:
 `stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
  expr_sim_inv cenv cx tenv (es1 with scopes := prev) /\
  locals_kept cenv es0 (es1 with scopes := prev) s0 t /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x t = SOME w)` by
   (fs[intcall_entry_full_def] >> metis_tac[]) >>
 `!x. not_fresh_at sa x ==> lookup_var x returned = lookup_var x t` by metis_tac[] >>
 irule exprBopSimPropsTheory.locals_kept_trans >>
 qexistsl_tac [`es1 with scopes := prev`,`sa`,`t`] >> simp[] >>
 irule exprSimPropsTheory.locals_kept_regions_tail >>
 qexists_tac `t` >> simp[] >>
 rpt gen_tac >> strip_tac >>
 `local_ptrs_rel func cenv prev t /\
  immutable_decl_sep cenv cx prev t.vs_vars t.vs_allocas t.vs_alloca_next` by
   (drule stmt_state_rel_local_ptrs_alloca >>
    drule return_stmt_immutable_sep >>
    simp[immutable_alloca_sep_def]) >>
 `b + sz <= t.vs_alloca_next` by
   (qpat_assum `local_region cenv prev t n b sz` mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.local_region_def] >>
    strip_tac >>
    qpat_assum `local_ptrs_rel func cenv prev t` mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
    strip_tac >>
    qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
    strip_tac >> gvs[]) >>
 Cases_on `sz = 0` >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
 `cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b` by
   (strip_tac >>
    `b <= b /\ b < b + sz` by simp[] >>
    drule_all bodyFullIntCallReturnFrameTheory.intcall_local_immutable_prefix_disjoint >>
    simp[]) >>
 `mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory` by
   (qhdtm_assum `intcall_callee_exit_full` mp_tac >>
    pure_rewrite_tac[intcall_callee_exit_full_def,intcall_callee_exit_def] >>
    simp[exprSimDefsTheory.expr_exit_def] >> strip_tac >>
    first_x_assum irule >> simp[] >> rpt strip_tac >>
    fs[intcall_entry_full_def] >> metis_tac[]) >>
 simp[]
QED
Finalise intcall_return_caller_frame

Theorem intcall_return_register_frame_certificate:
 !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sm vv s0
  DF lo d H G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn
  rc rbs pvs v ee Gc tc ir cs returned out outs rbuf root off st4 stored Gs ts.
 body_inv tops ctx cenv cx /\
 expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
 compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
 local_ptrs_reserved cenv sa /\ dead_lo_ok H (DF H) lo cenv cx /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
   s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\ 0 < rc /\
 intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc NONE
   sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
 unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\ safe_cast rtv v = SOME v /\
 bind_outputs outs ir.iret_values
   (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned /\
 ALL_DISTINCT outs /\ LENGTH outs = rc /\
 (!x. MEM x outs ==> ~not_fresh_at sa x) /\
 stmt_state_rel H ctx func cenv cx (out with scopes := prev) returned /\
 ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev)
   (DRESTRICT G (COMPL (set outs)))
   (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) returned /\
 rbuf.buf_operand = Var root /\ rbuf.buf_size = 32 * rc /\
 vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rbuf) /\
 eval_operand rbuf.buf_operand t = SOME (n2w off) /\
 FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size) /\
 sa.cs_next_id < sm.cs_next_id /\ lo <= off /\
 off + rbuf.buf_size <= t.vs_alloca_next /\ off + rbuf.buf_size < dimword (:256) /\
 not_fresh_at st4 root /\ ~MEM root outs /\
 (!x. MEM x outs ==> not_fresh_at st4 x) /\
 (stored with <|vs_vars := (returned with vs_inst_idx := SUC t.vs_inst_idx).vs_vars;
               vs_memory := returned.vs_memory|>) =
   (returned with vs_inst_idx := SUC t.vs_inst_idx) /\
 LENGTH returned.vs_memory <= LENGTH stored.vs_memory /\
 (!x. not_fresh_at st4 x ==>
   lookup_var x stored = lookup_var x returned /\
   FLOOKUP Gs x = FLOOKUP (DRESTRICT G (COMPL (set outs))) x /\
   op_taint ts (Var x) = op_taint
     (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) (Var x)) /\
 ts.t_mem = tc.t_mem DIFF {i | off <= i /\ i < off + 32 * rc} /\
 ts.t_stor = tc.t_stor /\ ts.t_trans = tc.t_trans /\ ts.t_imm = tc.t_imm /\
 (!a len. a + len <= off \/ off + 32 * rc <= a ==>
   mem_bytes_at a len stored.vs_memory = mem_bytes_at a len returned.vs_memory) ==>
 stmt_state_rel H ctx func cenv cx (out with scopes := prev)
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
 storage_well_formed_on cx (out with scopes := prev) (FST H) /\
 vv_at cenv cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
   sa sm (out with scopes := prev) (Value v) vv
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
 vv_own cenv cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
   sa sm (out with scopes := prev) (Value v) vv
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
 (~expr_has_effect (Call ann (IntCall (NONE,name)) es dflt) ==>
  vv_storage_live H cx vv (out with scopes := prev)
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
 (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
   lookup_var x (stored with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME w) /\
 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
   FLOOKUP stored.vs_allocas aid = SOME b) /\
 (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
   (!n lb lsz. local_region cenv es0.scopes s0 n lb lsz ==>
      b + sz <= lb \/ lb + lsz <= b) ==>
   mem_bytes_at b sz stored.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
 locals_kept cenv es0 (out with scopes := prev) s0
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
 (~expr_has_effect (Call ann (IntCall (NONE,name)) es dflt) ==>
  pure_frame cenv func es0 sa s0
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
 ghost_inv_at (DF H) lo d cenv cx (out with scopes := prev) Gs ts
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
 rpt gen_tac >> strip_tac >>
 `sa.cs_next_var <= st4.cs_next_var` by
   (`?x. MEM x outs` by (Cases_on `outs` >> gvs[] >> metis_tac[]) >>
    `~not_fresh_at sa x /\ not_fresh_at st4 x` by metis_tac[] >>
    qpat_x_assum `~not_fresh_at sa x` mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
    simp_tac bool_ss [] >> strip_tac >>
    qpat_x_assum `not_fresh_at st4 x` mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
    disch_then (qspec_then `n` mp_tac) >> simp[] >> decide_tac) >>
 `!x. not_fresh_at sa x ==> not_fresh_at st4 x` by
   metis_tac[freshWritesTheory.not_fresh_at_mono] >>
 drule_all intcall_return_caller_frame >> strip_tac >>
 drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
 `!p. not_fresh_at sa p ==> lookup_var p returned = lookup_var p t` by
   metis_tac[] >>
 `!name entry p sz. lookup_scopes name prev = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sa p` by
   (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
 `!name b sz. local_region cenv prev returned name b sz <=>
              local_region cenv prev t name b sz` by
   (irule loweringStateRelDefsTheory.local_region_lookup_cong >> metis_tac[]) >>
 `!name b sz. local_region cenv prev returned name b sz ==>
    b + sz <= off \/ off + rbuf.buf_size <= b` by
   (map_every qx_gen_tac [`nm`,`b`,`sz`] >> strip_tac >>
    `local_region cenv prev t nm b sz` by metis_tac[] >>
    qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> strip_tac >>
    qpat_x_assum `!n lo sz aid off asz. _` drule >>
    disch_then (drule_at Any) >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
 drule_all intcall_return_register_type_facts >> strip_tac >>
 `val_wf rtv v` by
   metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
 `val_footprint rtv v <= rbuf.buf_size` by
   metis_tac[exprSimPropsTheory.val_footprint_le] >>
 `eval_operand rbuf.buf_operand stored = SOME (n2w off)` by
   (`lookup_var root t = SOME (n2w off)` by
      (qpat_x_assum `eval_operand rbuf.buf_operand t = _` mp_tac >>
       simp[venomStateTheory.eval_operand_def]) >>
    simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
 `stored.vs_allocas = t.vs_allocas` by
   (qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
     (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_allocas`) >> simp[]) >>
 `!name b sz. local_region cenv prev stored name b sz ==>
    b + sz <= off \/ off + rbuf.buf_size <= b` by
   (rpt strip_tac >>
    `local_region cenv prev returned name' b sz` by
      (fs[loweringStateRelDefsTheory.local_region_def,
          venomStateTheory.lookup_var_def] >> metis_tac[]) >> metis_tac[]) >>
 conj_tac >- suspend "state" >>
 conj_tac >- suspend "storage" >>
 conj_tac >- suspend "at" >>
 conj_tac >- suspend "own" >>
 conj_tac >- simp[contextTheory.base_ptr_def] >>
 conj_tac >- suspend "vars" >>
 conj_tac >- suspend "allocas" >>
 conj_tac >- suspend "bytes" >>
 conj_tac >- suspend "locals" >>
 conj_tac >- simp[supportedExprTraverseTheory.expr_has_effect_def] >>
 suspend "ghost"
QED
Resume intcall_return_register_frame_certificate[state]:
 simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
 `stored.vs_data_section = returned.vs_data_section /\
  stored.vs_allocas = returned.vs_allocas` by
   (qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
     (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_data_section,s.vs_allocas)`) >>
    simp[]) >>
 `?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
       ai.inst_id = sa.cs_next_id` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >>
    strip_tac >>
    qpat_x_assum `0 < _ \/ 0 < _ ==> _` mp_tac >>
    (impl_tac >- metis_tac[pairTheory.PAIR_EQ]) >>
    strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
 `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
    (out with scopes := prev) stored` by suspend "state_imm" >>
 irule intCallResultTheory.result_state_memory_frame >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexists_tac `returned with vs_inst_idx := SUC t.vs_inst_idx` >>
 simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
 conj_tac >- (rpt strip_tac >>
   `local_region cenv prev returned name' b sz` by
     (fs[loweringStateRelDefsTheory.local_region_def,
         venomStateTheory.lookup_var_def]) >>
   qpat_x_assum `!a len. _ ==> mem_bytes_at a len stored.vs_memory = _` (qspecl_then [`b`,`sz`] mp_tac) >>
   impl_tac >- metis_tac[] >> simp[]) >>
 conj_tac >- (rpt strip_tac >>
   `not_fresh_at st4 p` by metis_tac[] >>
   qpat_x_assum `!x. not_fresh_at st4 x ==> _` (qspec_then `p` mp_tac) >>
   simp[venomStateTheory.lookup_var_def]) >>
 reverse conj_tac >-
   (qpat_assum `returned.vs_memory = cs.vs_memory` (fn eq =>
      qpat_assum `LENGTH returned.vs_memory <= LENGTH stored.vs_memory`
        (assume_tac o PURE_REWRITE_RULE [eq])) >>
    fs[venomStateTheory.venom_state_fupdcanon]) >> rpt strip_tac >>
 `not_fresh_at sa x` by
   (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
 `not_fresh_at st4 x` by metis_tac[] >>
 qpat_x_assum `!x. not_fresh_at st4 x ==> _` (qspec_then `x` mp_tac) >>
 simp[venomStateTheory.lookup_var_def] >>
 qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `x` mp_tac) >>
 simp[venomStateTheory.lookup_var_def]
QED
Resume intcall_return_register_frame_certificate[state_imm]:
 `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
    (out with scopes := prev) returned /\
  immutable_alloca_sep func cenv cx (out with scopes := prev) returned` by
   (drule return_stmt_immutable_sep >>
    drule stmt_state_rel_state_rel >>
    disch_then (mp_tac o MATCH_MP state_rel_immutables_rel) >> simp[]) >>
 reverse (Cases_on `cenv.ce_is_ctor`)
 >- (fs[loweringStateRelDefsTheory.immutables_rel_def] >> metis_tac[]) >>
 qhdtm_x_assum `immutables_rel` mp_tac >>
 pure_rewrite_tac[loweringStateRelDefsTheory.immutables_rel_def] >>
 asm_simp_tac (srw_ss()) [LET_THM] >> strip_tac >> rpt gen_tac >> strip_tac >>
 qpat_x_assum `!name tv v byte_offset. _` drule_all >> strip_tac >>
 `mem_bytes_at byte_offset (type_memory_size tv) stored.vs_memory =
  mem_bytes_at byte_offset (type_memory_size tv) returned.vs_memory` by
   (qhdtm_x_assum `immutable_alloca_sep` mp_tac >>
    pure_rewrite_tac[exprLoweringPropsTheory.immutable_alloca_sep_def] >>
    strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` mp_tac >>
    asm_simp_tac (srw_ss()) [] >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    `regions_disjoint byte_offset (type_memory_size tv) off rbuf.buf_size` by
      metis_tac[] >>
    fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
 simp[] >> irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
 conj_tac >- metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
 qexistsl_tac [`type_memory_size tv`,`returned.vs_memory`] >>
 simp[]
QED
Resume intcall_return_register_frame_certificate[storage]:
 qhdtm_assum `intcall_callee_exit_full` mp_tac >>
 pure_rewrite_tac[intcall_callee_exit_full_def] >> strip_tac >>
 first_x_assum (qspecl_then [`v`,`ir`,`cs`] mp_tac) >>
 simp[] >> strip_tac >> gvs[] >>
 gvs[vyperStorageFootprintTheory.storage_well_formed_on_def,
     vyperStorageBackendTheory.get_storage_def] >>
 rpt strip_tac >>
 qpat_x_assum `!b slot tv. MEM (b,slot,tv) _ ==> _`
   (qspecl_then [`b`,`slot`,`tv`] mp_tac) >>
 Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED
Resume intcall_return_register_frame_certificate[at]:
 simp[loweringPostsTheory.vv_at_def,contextTheory.base_ptr_def,
      vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
 rpt strip_tac >> gvs[] >>
 disj1_tac >>
 qexistsl_tac [`sa.cs_next_id`,`off`,`32 * LENGTH outs`] >>
 `off < dimword (:256)` by decide_tac >>
 simp[] >> rpt strip_tac >>
 `local_region cenv prev stored n lb lsz` by
   (qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
    simp[loweringStateRelDefsTheory.local_region_def,venomStateTheory.lookup_var_def]) >>
 qpat_x_assum `!name b sz. local_region cenv prev stored name b sz ==> _`
   (qspecl_then [`n`,`lb`,`lsz`] mp_tac) >> simp[]
QED
Resume intcall_return_register_frame_certificate[own]:
 simp[loweringPostsTheory.vv_own_def,contextTheory.base_ptr_def,
      vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
 rpt strip_tac >> gvs[] >> disj1_tac >>
 qexistsl_tac [`sa.cs_next_id`,`off`,`32 * LENGTH outs`] >>
 `off < dimword (:256)` by decide_tac >>
 simp[] >> rpt strip_tac >>
 `local_region cenv prev stored n lb lsz` by
   (qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
    simp[loweringStateRelDefsTheory.local_region_def,venomStateTheory.lookup_var_def]) >>
 qpat_x_assum `!name b sz. local_region cenv prev stored name b sz ==> _`
   (qspecl_then [`n`,`lb`,`lsz`] mp_tac) >> simp[]
QED
Resume intcall_return_register_frame_certificate[vars]:
 rpt strip_tac >>
 `lookup_var x returned = SOME w` by metis_tac[] >>
 `not_fresh_at st4 x` by metis_tac[] >>
 `lookup_var x stored = lookup_var x returned` by metis_tac[] >>
 fs[venomStateTheory.lookup_var_def]
QED
Resume intcall_return_register_frame_certificate[allocas]:
 qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
   (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_allocas`) >> simp[] >>
 metis_tac[]
QED
Resume intcall_return_register_frame_certificate[bytes]:
 rpt strip_tac >>
 `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
 `alloca_inv t` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >>
    disch_then (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca o cj 7) >>
    simp[]) >>
 `regions_disjoint b sz off rbuf.buf_size` by
   (qpat_assum `alloca_inv t` mp_tac >>
    pure_rewrite_tac[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def] >> strip_tac >>
    `aid <> sa.cs_next_id` by decide_tac >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
 fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED
Resume intcall_return_register_frame_certificate[locals]:
 irule exprBopSimPropsTheory.locals_kept_trans >>
 qexistsl_tac [`out with scopes := prev`,`sa`,`returned`] >> simp[] >>
 irule exprSimPropsTheory.locals_kept_regions_tail >>
 qexists_tac `returned` >> simp[] >> rpt strip_tac >>
 `local_region cenv prev returned n b sz` by simp[] >>
 metis_tac[]
QED
Resume intcall_return_register_frame_certificate[ghost]:
 simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
 conj_tac >- suspend "ghost_locals" >>
 conj_tac >- suspend "ghost_buffer" >>
 conj_tac >- suspend "ghost_pc" >>
 qhdtm_assum `ghost_inv_at` mp_tac >>
 pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >> strip_tac >>
 conj_tac >- suspend "ghost_stor" >>
 conj_tac >- (rpt strip_tac >>
   qpat_x_assum `!i. i < lo /\ _ ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
 conj_tac >- suspend "ghost_imm" >>
 qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
   (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_allocas,s.vs_alloca_next)`) >>
 simp[] >> strip_tac >>
 fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED
Resume intcall_return_register_frame_certificate[ghost_locals]:
 rpt gen_tac >> strip_tac >>
 `not_fresh_at sa p` by
   (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
 `not_fresh_at st4 p` by metis_tac[] >>
 `ptr_covers (DRESTRICT G (COMPL (set outs)))
   (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) p returned sz /\
  !w mem. lookup_var p returned = SOME w /\
    mem_agree_outside tc.t_mem returned.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem` by
   (fs[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
 conj_tac
 >- (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
 rpt strip_tac >>
 `lookup_var p returned = SOME w` by
   (fs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
 `local_region cenv prev returned name' (w2n w) sz` by
   (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
 `mem_bytes_at (w2n w) sz stored.vs_memory =
  mem_bytes_at (w2n w) sz returned.vs_memory` by metis_tac[] >>
 `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
   (drule stmt_state_rel_local_ptrs_alloca >>
    simp[loweringStateRelDefsTheory.local_ptrs_rel_def] >> strip_tac >>
    qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
    strip_tac >> gvs[]) >>
 irule bodyPtrMakeArrayMemoryFrameTheory.robust_val_in_memory_shrinking_frame >>
 conj_tac >- simp[] >>
 qexistsl_tac [`tc.t_mem`,`ts.t_mem`,`returned.vs_memory`,`stored.vs_memory`,`sz`] >>
 simp[] >> metis_tac[exprSimPropsTheory.val_footprint_le,arithmeticTheory.LESS_EQ_TRANS]
QED
Resume intcall_return_register_frame_certificate[ghost_buffer]:
 qhdtm_assum `ghost_inv_at` mp_tac >>
 pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >> strip_tac >>
 Cases_on `d` >- simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
 rename1 `return_buf_ptr (SOME pair) _ _ _ _` >> PairCases_on `pair` >>
 fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
 `not_fresh_at st4 x` by metis_tac[] >>
 simp[bodyPtrDefsTheory.return_buf_ptr_def,bodyPtrDefsTheory.ptr_covers_def] >>
 fs[bodyPtrDefsTheory.ptr_covers_def] >>
 qpat_x_assum `!x. not_fresh_at st4 x ==> _` (qspec_then `x` mp_tac) >>
 simp[venomStateTheory.lookup_var_def] >> gvs[]
QED
Resume intcall_return_register_frame_certificate[ghost_pc]:
 rpt strip_tac >>
 `op_taint (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) (Var x) = {}` by
   (fs[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
 `not_fresh_at st4 x` by metis_tac[] >>
 metis_tac[]
QED
Resume intcall_return_register_frame_certificate[ghost_stor]:
 qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
   (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_accounts,s.vs_transient,s.vs_immutables,s.vs_call_ctx)`) >>
 simp[] >> strip_tac >>
 fs[bodyPtrDefsTheory.stor_taint_ok_at_def]
QED
Resume intcall_return_register_frame_certificate[ghost_imm]:
 rpt strip_tac >>
 `not_fresh_at sa x` by
   (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
 `not_fresh_at st4 x` by metis_tac[] >>
 metis_tac[]
QED
Finalise intcall_return_register_frame_certificate

Theorem intcall_return_register_post:
  !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sm vv s0
   DF lo d H G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn
   rc rbs pvs v ee Gc tc ir cs returned out outs rbuf root off st4 stored Gs ts bb inst dflts.
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ dead_lo_ok H (DF H) lo cenv cx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\ 0 < rc /\
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc NONE
    sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\ safe_cast rtv v = SOME v /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned /\
  ALL_DISTINCT outs /\ LENGTH outs = rc /\ LENGTH ir.iret_values = rc /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  stmt_state_rel H ctx func cenv cx (out with scopes := prev) returned /\
  ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev)
    (DRESTRICT G (COMPL (set outs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) returned /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0
    (DRESTRICT G (COMPL (set outs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) /\
  rbuf.buf_operand = Var root /\ rbuf.buf_size = 32 * rc /\
  vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rbuf) /\
  eval_operand rbuf.buf_operand t = SOME (n2w off) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size) /\
  sa.cs_next_id < sm.cs_next_id /\ lo <= off /\
  off + rbuf.buf_size <= t.vs_alloca_next /\ off + rbuf.buf_size < dimword (:256) /\
  store_multi_results (Var root) (MAP Var outs) 0 st4 = ((),sm) /\
  not_fresh_at st4 root /\ ~MEM root outs /\
  (!x. MEM x outs ==> not_fresh_at st4 x) /\
  st4.cs_current_bb = t.vs_current_bb /\ sm.cs_current_bb = st4.cs_current_bb /\
  LENGTH st4.cs_current_insts = SUC t.vs_inst_idx /\
  fn_has_code st4 sm func /\ inst.inst_opcode = INVOKE /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  run_inst_seq (emitted_insts st4 sm) (returned with vs_inst_idx := SUC t.vs_inst_idx) = OK stored /\
  (stored with <|vs_vars := (returned with vs_inst_idx := SUC t.vs_inst_idx).vs_vars;
                vs_memory := returned.vs_memory|>) =
    (returned with vs_inst_idx := SUC t.vs_inst_idx) /\
  (!x. not_fresh_at st4 x ==>
     lookup_var x stored = lookup_var x returned /\
     FLOOKUP Gs x = FLOOKUP (DRESTRICT G (COMPL (set outs))) x /\
     op_taint ts (Var x) = op_taint
       (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) (Var x)) /\
  ts.t_mem = tc.t_mem DIFF {i | off <= i /\ i < off + 32 * rc} /\
  ts.t_stor = tc.t_stor /\ ts.t_trans = tc.t_trans /\ ts.t_imm = tc.t_imm /\
  (!mem i. mem_agree_outside ts.t_mem stored.vs_memory mem /\ i < LENGTH ir.iret_values ==>
     mem_word_at (off + 32 * i) mem = EL i ir.iret_values) /\
  (!a len. a + len <= off \/ off + 32 * rc <= a ==>
     mem_bytes_at a len stored.vs_memory = mem_bytes_at a len returned.vs_memory) ==>
  vv_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
    es0 sa sm s0 (out with scopes := prev) (Value v) vv
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  vv_store_bound cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
    (lowered_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
    (out with scopes := prev) (Value v) vv
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  (stored with vs_inst_idx := LENGTH sm.cs_current_insts).vs_current_bb = sm.cs_current_bb /\
  alloca_history func (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  s0.vs_alloca_next <= stored.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx (out with scopes := prev) Gs ts
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  ptr_vv_ok cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
    (Value v) vv (out with scopes := prev) Gs ts
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  vv_own cenv cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
    sa sm (out with scopes := prev) (Value v) vv
    (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx (Value v) (out with scopes := prev) = (INL val,out with scopes := prev) /\
     !rt w. evaluate_type (get_tenv cx)
       (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) = SOME rt /\
       eval_operand (vv_operand vv) (stored with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside ts.t_mem stored.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  (!ty' op. vv = StackValue ty' op /\
    ~is_word_type (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
    ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) op Gs
      (stored with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
  (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) p.ptr_operand Gs
      (stored with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 Gs ts
Proof
  rpt gen_tac >> strip_tac >>
  drule run_inst_seq_memory_length >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  conj_tac >- suspend "value_post" >>
  conj_tac >- suspend "store_bound" >>
  conj_tac >- suspend "position" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "frontier" >>
  conj_tac >- suspend "ghost_inv" >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- (drule_all intcall_return_register_frame_certificate >> simp[]) >>
  conj_tac >- simp[contextTheory.vv_location_def, contextTheory.base_ptr_def] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "buffer" >>
  suspend "ghost_kept"
QED
Resume intcall_return_register_post[value_post]:
  drule_all intcall_return_register_value_certificate >> strip_tac >>
  drule_all intcall_return_register_frame_certificate >> strip_tac >>
  drule_all intcall_return_register_type_facts >> strip_tac >>
  qpat_x_assum `!out. _` (qspec_then `out` strip_assume_tac) >>
  pure_rewrite_tac[loweringPostsTheory.vv_post_def] >>
  pure_asm_rewrite_tac[] >>
  simp[] >> conj_tac
  >- (qhdtm_assum `vv_holds` mp_tac >> gvs[]) >>
  rpt strip_tac >> first_assum irule >> metis_tac[]
QED
Resume intcall_return_register_post[store_bound]:
  drule_all intcall_return_register_value_certificate >> simp[]
QED
Resume intcall_return_register_post[position]:
  qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
    (assume_tac o SRULE [] o Q.AP_TERM `\z. z.vs_current_bb`) >>
  drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
  qpat_x_assum `returned = _` SUBST_ALL_TAC >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[venomExecSemanticsTheory.adopt_return_fmp_def,
      venomExecSemanticsTheory.merge_callee_state_def]
QED
Resume intcall_return_register_post[history]:
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `alloca_history func (t with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule allocaHistoryTheory.history_nonalloca_advance >>
     conj_tac >- (qexistsl [`bb`, `inst`] >> simp[]) >>
     fs[intcall_entry_full_def]) >>
  `returned.vs_current_bb = t.vs_current_bb` by
    (drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
     qpat_x_assum `returned = _` SUBST_ALL_TAC >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[venomExecSemanticsTheory.adopt_return_fmp_def,
          venomExecSemanticsTheory.merge_callee_state_def]) >>
  `alloca_history func (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule allocaHistoryTheory.alloca_history_frame >>
     qexists_tac `t with vs_inst_idx := SUC t.vs_inst_idx` >> simp[]) >>
  drule intCallResultTheory.store_multi_results_shape >> strip_tac >>
  `?rest. DROP (SUC t.vs_inst_idx) bb.bb_instructions =
     emitted_insts st4 sm ++ rest` by
    (qpat_assum `fn_has_code st4 sm func` mp_tac >>
     pure_rewrite_tac[fragExecTheory.fn_has_code_def,
          exprLoweringPropsTheory.same_blocks_def,
          fragExecTheory.emitted_blocks_def] >>
     strip_tac >>
     fs[rich_listTheory.IS_PREFIX_APPEND] >>
     gvs[] >> qexists_tac `l` >>
     qpat_x_assum `LENGTH st4.cs_current_insts = _` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, exprLoweringPropsTheory.DROP_PREFIX] >> REFL_TAC) >>
  `LENGTH sm.cs_current_insts =
    (returned with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx +
    LENGTH (emitted_insts st4 sm)` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `alloca_inv (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule venomMemProofsTheory.alloca_inv_set_inst_idx >> simp[]) >>
  irule allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED
Resume intcall_return_register_post[frontier]:
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
    (assume_tac o SRULE [] o Q.AP_TERM `\z. z.vs_alloca_next`) >>
  fs[intcall_entry_full_def]
QED
Resume intcall_return_register_post[ghost_inv]:
  drule_all intcall_return_register_frame_certificate >> simp[]
QED
Resume intcall_return_register_post[pointer]:
  drule_all intcall_return_register_value_certificate >> simp[]
QED
Resume intcall_return_register_post[buffer]:
  drule_all intcall_return_register_type_facts >> strip_tac >>
  `type_memory_bytes cenv ret = type_memory_size rtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
              exprSimHypsDefsTheory.expr_body_pre_def] >>
  `FLOOKUP G root = SOME (off,rbuf.buf_size)` by
    (qhdtm_assum `intcall_entry_full` mp_tac >>
     pure_rewrite_tac[intcall_entry_full_def] >> strip_tac >>
     qpat_x_assum `!ty p buf. _`
       (qspecl_then [`cenv.ce_func_return_type (nsid_to_string (NONE,name))`,
                     `base_ptr rbuf`,`rbuf`] mp_tac) >>
     map_every (fn p => qpat_assum p mp_tac)
       [`vv = LocatedValue (cenv.ce_func_return_type _) (base_ptr rbuf)`,
        `rbuf.buf_operand = Var root`,
        `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size)`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.base_ptr_def] >> rpt strip_tac >> gvs[]) >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `eval_operand (Var root) stored = SOME (n2w off)` by
    (simp[venomStateTheory.eval_operand_def] >>
     qpat_assum `!x. not_fresh_at st4 x ==> _` (qspec_then `root` mp_tac) >>
     simp[] >>
     gvs[venomStateTheory.eval_operand_def]) >>
  gvs[contextTheory.base_ptr_def, bodyPtrDefsTheory.ptr_buf_ok_def,
      exprLoweringTheory.lowered_value_type_def,
      finite_mapTheory.FLOOKUP_DRESTRICT, venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def] >>
  `off < dimword (:256)` by decide_tac >>
  simp[wordsTheory.w2n_n2w] >> metis_tac[]
QED
Resume intcall_return_register_post[ghost_kept]:
 `sa.cs_next_var <= st4.cs_next_var` by
   (`?x. MEM x outs` by (Cases_on `outs` >> gvs[] >> metis_tac[]) >>
    `~not_fresh_at sa x /\ not_fresh_at st4 x` by metis_tac[] >>
    qpat_x_assum `~not_fresh_at sa x` mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
    simp_tac bool_ss [] >> strip_tac >>
    qpat_x_assum `not_fresh_at st4 x` mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
    disch_then (qspec_then `n` mp_tac) >> simp[] >> decide_tac) >>
 `!x. not_fresh_at sa x ==> not_fresh_at st4 x` by
   metis_tac[freshWritesTheory.not_fresh_at_mono] >>
 qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
 simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
 rpt strip_tac >> gvs[] >> metis_tac[]
QED
Finalise intcall_return_register_post

(* The completed child witness is an input, not chosen again from a full
   outcome. The first restored cursor is after INVOKE and before any stores. *)
Theorem intcall_return_selected_edge:
  !DF lo d ctx explicit PG func tops cenv cx tenv name es es0 st0 sa sm vv s0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn rc rbs pvs rb callee entered
   bb inst lbl arg_ops argv v ee marks Gc tc ir cs.
    (!h. valid_horizon cx st0 h es1.storage_trace ==>
       intcall_entry_full (DF,lo,d) h tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
    (!h. valid_horizon cx st0 h ee.storage_trace ==>
         valid_horizon cx st0 h es1.storage_trace) /\
    (!h. dead_lo_ok h (DF h) lo cenv cx) /\
    body_inv tops ctx cenv cx /\ fn_has_code sa sm func /\ local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
    (!tail. intcall_callee_src cx name mut nr ss
       (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
         (INL v,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!h. valid_horizon cx st0 h ee.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
        (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc) /\
      intcall_callee_exit_full (DF,lo) h func cenv cx mut nr rtv rc
        rb sa.cs_next_id sm.cs_next_id t tn
        (INL v) (ee with gas_obs := []) (Gc,tc) (IntRet ir cs)) ==>
    inst.inst_opcode = INVOKE /\
    LENGTH inst.inst_outputs = rc /\
    LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
    (!D. ptr_inst_ok D lo 0 ctx func G tn inst t) /\
    (!setup fuel p depth i s.
      enters_block callee setup entered /\ run_blocks fuel ctx callee setup = IntRet i s ==>
      i = ir /\ s = cs /\
      marks = entryCreateBodyCut$create_cut_marks explicit
        (dftGasFromListTraceDefs$trace_blocks p depth fuel ctx callee setup)) /\
    ?out returned.
      unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) =
         (INL (),out) /\
      safe_cast rtv v = SOME v /\
      (!tail. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := tail) =
         (INL (),out with gas_obs := tail)) /\
      (!tail. intcall_rest cx name mut nr ss prev rtv
         (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
           (INL (Value v),(out with scopes := prev) with gas_obs := tail)) /\
      bind_outputs inst.inst_outputs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned /\
      (!h. valid_horizon cx st0 h ee.storage_trace ==>
        gas_origin_ptr_edge (DF h,lo,explicit,ctx,func,PG) (t,G,tn) marks
          (OK (returned with vs_inst_idx := SUC t.vs_inst_idx),
           DRESTRICT G (COMPL (set inst.inst_outputs)),
           tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))) /\
        ghost_kept_at lo cenv es0 sa G0 tn0 s0
          (DRESTRICT G (COMPL (set inst.inst_outputs)))
          (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))) /\
        ghost_inv_at (DF h) lo d cenv cx (es1 with scopes := prev)
          (DRESTRICT G (COMPL (set inst.inst_outputs)))
          (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))) returned) /\
      (!h. valid_horizon cx st0 h out.storage_trace ==>
         stmt_state_rel h ctx func cenv cx (out with scopes := prev) returned)
Proof
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es1.storage_trace` by
    metis_tac[] >>
  qpat_assum `!h. valid_horizon cx st0 h es1.storage_trace ==> _`
    (drule_then assume_tac) >>
  `?out. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) =
           (INL (),out)` by
    (qhdtm_assum `intcall_callee_exit_full` mp_tac >>
     simp_tac (srw_ss()) [intcall_callee_exit_full_def] >>
     strip_tac >> metis_tac[]) >>
  `gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es1` by
    (qhdtm_assum `intcall_entry_full` mp_tac >>
     pure_rewrite_tac[intcall_entry_full_def] >> metis_tac[]) >>
  qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  drule_all intcall_return_source >>
  disch_then (qspecl_then [`prev`,`rtv`] assume_tac) >>
  `safe_cast rtv v = SOME v` by
    (Cases_on `safe_cast rtv v`
     >- (gvs[] >> drule_all gasContextTheory.gas_admissible_result >>
         simp[exprSimDefsTheory.expr_vv_res_ok_def]) >>
     metis_tac[loweringHaltTheory.safe_cast_some_eq]) >>
  `!tail. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := tail) =
       (INL (),out with gas_obs := tail)` by
    (Cases_on `nr /\ ~is_view_mut mut` >>
     Cases_on `cx.nonreentrant_slot` >>
     gvs[unlock_if_nr_def, release_nonreentrant_lock_def,
         record_storage_event_def, get_transient_storage_def,
         update_transient_def, ignore_bind_def, bind_def, return_def]) >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[fragGasFocusTheory.gas_invoke_entry_readings] >>
  `!tail. intcall_rest cx name mut nr ss prev rtv
      (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
       (INL (Value v),(out with scopes := prev) with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
       (qspec_then `tail` mp_tac) >>
     qpat_assum `!tail. unlock_if_nr _ _ _ _ = _`
       (qspec_then `tail` mp_tac) >>
     disch_tac >> disch_then (mp_then Any mp_tac intcall_return_source) >>
     simp[] >> disch_then (qspecl_then [`prev`,`rtv`] mp_tac) >> simp[]) >>
  `inst.inst_opcode = INVOKE` by
    (fs[fragGasFocusTheory.gas_invoke_entry_def] >> metis_tac[]) >>
  `ptr_inst_ok (DF (storage_trace_horizon ee.storage_trace)) lo 0 ctx func G tn inst t` by
    (drule_all intcall_entry_invoke_ptr >> simp[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn inst t` by
    (qpat_x_assum `ptr_inst_ok _ lo 0 ctx func G tn inst t` mp_tac >>
     asm_simp_tac bool_ss [ptrSafeRunTheory.ptr_inst_ok_def]) >>
  rename1 `cenv.ce_func_info _ = (nret,rbs,pvs)` >>
  drule_all intcall_entry_invoke_continuation >> strip_tac >>
  `LENGTH ir.iret_values = nret /\ ir.iret_adopt_fmp = NONE` by
    (qhdtm_assum `intcall_callee_exit_full` mp_tac >>
     pure_rewrite_tac[intcall_callee_exit_full_def,intcall_callee_exit_def] >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `LENGTH inst.inst_outputs = LENGTH ir.iret_values` by simp[] >>
  `ptr_inst_ok (DF (storage_trace_horizon ee.storage_trace)) lo 0 ctx func G tn inst t` by simp[] >>
  drule_all gas_origin_ptr_invoke_intret >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `bind_outputs _ _ _ = SOME returned` >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> drule_all intcall_completed_child_native >> simp[]) >>
  qexistsl_tac [`out`,`returned`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- suspend "caller_state" >>
  gen_tac >> strip_tac >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 h es1.storage_trace` by metis_tac[] >>
  qpat_assum `!h. valid_horizon cx st0 h es1.storage_trace ==> _`
    (drule_then assume_tac) >>
  `ptr_inst_ok (DF h) lo 0 ctx func G tn inst t` by simp[] >>
  conj_tac
  >- (drule_all gas_origin_ptr_invoke_intret >>
      disch_then (qspec_then `PG` strip_assume_tac) >> gvs[]) >>
  `dead_lo_ok h (DF h) lo cenv cx` by simp[] >>
  conj_tac >- (drule_all intcall_return_ghost_kept >> simp[]) >>
  drule_all intcall_return_ghost_inv >> simp[]
QED

Resume intcall_return_selected_edge[caller_state]:
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 h ee.storage_trace` by
    (`storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
       simp[unlock_if_nr_def,vyperStorageTraceTheory.storage_trace_frame_optional_locks] >>
     drule vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then (qspecl_then [`st0`,`out`,`ee with gas_obs := []`,
       `INL ()`,`cx`,`h`] mp_tac) >> simp[]) >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 h es1.storage_trace` by metis_tac[] >>
  qpat_assum `!h. valid_horizon cx st0 h es1.storage_trace ==> _`
    (drule_then assume_tac) >>
  `dead_lo_ok h (DF h) lo cenv cx` by simp[] >>
  qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  drule_all intcall_return_invoke_setup >>
  disch_then (qx_choose_then `setup` strip_assume_tac) >>
  `exit_result (IntRet ir cs)` by simp[fragExecTheory.exit_result_def] >>
  drule_all setup_terminal_certificate >> strip_tac >>
  `step_inst fuel ctx inst t = OK returned` by
    simp[Once venomExecSemanticsTheory.step_inst_def] >>
  drule_all intcall_return_stmt_state_rel >> simp[]
QED
Finalise intcall_return_selected_edge

Theorem intcall_return_normal_tracked:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs callee entered bb inst lbl arg_ops argv dflts
   bad_scope full_scope.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
    compile_expr (gasShadowCompileBase$gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa = (vv,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
    (?marks res ee r Gc tc.
       (!tail. intcall_callee_src cx name mut nr ss
          (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
            (res,ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       !H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path
           (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
           (entered,FEMPTY,tn with t_var := FEMPTY) marks (r,Gc,tc) /\
         ((?u. r = OK u /\ F) \/
          (exit_result r /\
           intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id sm.cs_next_id t tn res (ee with gas_obs := []) (Gc,tc) r))) ==>
    (fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
     intcall_return_scope_rules (gas_explicit_sites ctx shadow_ctx) ctx func t sm
       bad_scope full_scope ==>
     intcall_return_witness (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
       (\H res ee G tn t'. ?tv. res = INL tv /\
         vv_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
           es0 sa sm s0 ee tv vv t' /\
         vv_store_bound cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
           (lowered_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ee tv vv t' /\
         t'.vs_current_bb = sm.cs_current_bb /\ t'.vs_inst_idx = LENGTH sm.cs_current_insts /\
         alloca_history func t' /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
         ptr_vv_ok cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) tv vv ee G tn t' /\
         (!v. tv = Value v /\
              ~is_word_type
                (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) /\
              ~is_bytestring_type
                (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
              vv_own cenv cx
                (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
                sa sm ee tv vv t' /\
              (!ty' p. vv = LocatedValue ty' p ==> p.ptr_location = LocMemory)) /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee = (INL val,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) = SOME rt /\
              eval_operand (vv_operand vv) t' = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem t'.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
         (!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
            ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) op G t') /\
         (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) p.ptr_operand G t') /\
         ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
       bad_scope full_scope)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> _` (mk_asm "entry") >>
  `storage_trace_frame (intcall_callee_src cx name mut nr ss)` by
    (rewrite_tac[intcall_callee_src_def] >>
     irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
     simp[vyperStorageTraceTheory.storage_trace_frame_optional_locks] >>
     irule vyperStorageTraceTheory.storage_trace_frame_try >>
     simp[vyperStorageTraceTheory.storage_trace_frame_function_handler] >>
     irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_return]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es1.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     drule vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then drule >> simp[]) >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[fragGasFocusTheory.gas_invoke_entry_readings] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                    gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  simp_tac bool_ss [] >> strip_tac >>
  Cases_on `expr_exit res r`
  >- suspend "abort" >>
  `?v ir cs. res = INL v /\ r = IntRet ir cs` by
    (qhdtm_assum `intcall_callee_exit_full` mp_tac >>
     pure_rewrite_tac[intcall_callee_exit_full_def, intcall_callee_exit_def] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[] >> suspend "intret"
QED

Resume intcall_return_normal_tracked[abort]:
  `?ex. res = INR ex` by
    (Cases_on `res` >> Cases_on `r` >>
     gvs[exprSimDefsTheory.expr_exit_def]) >> gvs[] >>
  drule_all intcall_return_source_exit >>
  disch_then (qspecl_then [`prev`,`rtv`] strip_assume_tac) >>
  `inst.inst_opcode = INVOKE` by
    (fs[fragGasFocusTheory.gas_invoke_entry_def] >> metis_tac[]) >>
  `!ret se. r <> IntRet ret se` by
    (Cases_on `r` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
  `!H'. valid_horizon cx st0 H' out.storage_trace ==>
     gas_origin_ptr_edge
       (DF H',lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G,tn) marks (r,G,tn)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H' ee.storage_trace` by metis_tac[] >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H'` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     asm "entry" (qspec_then `H'` mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     strip_tac >>
     `ptr_inst_ok (DF H') lo 0 ctx func G tn inst t` by
       (drule_all intcall_entry_invoke_ptr >> simp[]) >>
     drule_all gas_origin_ptr_invoke_exit >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon out.storage_trace) out.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `full_scope marks r` by
    (qpat_assum `!H'. valid_horizon cx st0 H' out.storage_trace ==> gas_origin_ptr_edge _ _ _ _`
       (drule_then assume_tac) >> drule_all intcall_return_scope_abort >> simp[]) >>
  rewrite_tac[intcall_return_witness_def] >> qexists_tac `marks` >>
  disj2_tac >>
  qexistsl_tac [`INR ex`,`out`,`r`,`G`,`tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "abort_domain" >>
  gen_tac >> strip_tac >>
  `gas_origin_ptr_edge
    (DF H',lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G,tn) marks (r,G,tn)` by metis_tac[] >>
  conj_tac >- simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  simp[] >>
  `expr_exit (INR ex : eval_result + exception) r` by
    (Cases_on `r` >> Cases_on `ex` >> gvs[expr_exit_def] >>
     rename1 `expr_exit (INR (Error err)) _` >>
     Cases_on `err` >> gvs[expr_exit_def]) >>
  simp[] >> conj_tac
  >- (Cases_on `ex = HaltException` >> simp[halt_exit_def] >>
      `valid_horizon cx st0 H' ee.storage_trace` by metis_tac[] >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H'` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (mp_tac o PURE_REWRITE_RULE
        [intcall_callee_exit_full_def, intcall_callee_exit_def] o CONJUNCT2) >>
      qpat_assum `ex = HaltException` (fn th => simp_tac (srw_ss()) [th]) >>
      strip_tac >>
      drule halt_exit_scopes_gas_obs >>
      disch_then (qspecl_then [`prev`,`[]`] mp_tac) >>
      simp[halt_exit_def, vyperStateTheory.evaluation_state_fupdcanon]) >>
  rpt strip_tac >> gvs[] >>
  qpat_assum `!h. _ ==> gas_origin_ptr_edge _ _ _ _`
    (qspec_then `H'` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> drule_all gas_origin_ptr_edge_halt_fmp >> simp[]
QED
Resume intcall_return_normal_tracked[abort_domain]:
  metis_tac[]
QED
Resume intcall_return_normal_tracked[intret]:
  rename1 `cenv.ce_func_info _ = (nret,rbs,pvs)` >>
  `!h. valid_horizon cx st0 h ee.storage_trace ==>
      gas_origin_ptr_path
        (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
        (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc) /\
      intcall_callee_exit_full (DF,lo) h func cenv cx mut nr rtv nret
        (if nret = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
        sa.cs_next_id sm.cs_next_id t tn (INL v) (ee with gas_obs := []) (Gc,tc)
        (IntRet ir cs)` by
    (rpt strip_tac >>
     qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  drule_all intcall_return_selected_edge >>
  disch_then (qspec_then `PG` (strip_assume_tac o
    SIMP_RULE bool_ss [FORALL_AND_THM, IMP_CONJ_THM])) >>
  rpt (qpat_x_assum `!setup fuel i s. enters_block _ _ _ /\ _ ==> _` kall_tac ORELSE
       qpat_x_assum `!setup fuel p depth i s. enters_block _ _ _ /\ _ ==> _` kall_tac) >>
  rename1 `bind_outputs _ _ _ = SOME returned` >>
  asm "entry" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >>
  drule_all intcall_entry_invoke_continuation >> strip_tac >>
  qhdtm_assum `intcall_entry_full` (fn entry =>
    let val th = PURE_REWRITE_RULE [intcall_entry_full_def] entry
    in map_every (assume_tac o (fn i => cj i th)) [17, 18, 20, 22] end) >>
  Cases_on `nret = 0` >- suspend "intret_void" >>
  `0 < nret` by simp[] >>
  qpat_x_assum `0 < nret ==> _` (fn post =>
    qpat_assum `0 < nret` (strip_assume_tac o MATCH_MP post)) >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `op_taint tn (Var root) = {} /\
   FLOOKUP G root = SOME (off,rbuf.buf_size) /\
   lo <= off /\ off + rbuf.buf_size <= t.vs_alloca_next` by
    (qpat_assum `!ty p buf. vv = LocatedValue ty p /\ _ ==> _`
       (qspecl_then [`cenv.ce_func_return_type (nsid_to_string (NONE,name))`,
                     `base_ptr rbuf`,`rbuf`] mp_tac) >>
     map_every (fn p => qpat_assum p mp_tac)
       [`vv = LocatedValue (cenv.ce_func_return_type _) (base_ptr rbuf)`,
        `rbuf.buf_operand = Var root`,
        `FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size)`,
        `aid = sa.cs_next_id`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.base_ptr_def] >> rpt strip_tac >> gvs[]) >>
  `off + rbuf.buf_size < dimword (:256)` by
    (qhdtm_assum `intcall_entry_full` mp_tac >>
     pure_rewrite_tac[intcall_entry_full_def] >>
     disch_then (assume_tac o cj 7) >>
     drule exprSimPropsTheory.stmt_state_rel_region_lt >>
     disch_then (fn th =>
       qpat_assum `FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size)`
         (ACCEPT_TAC o MATCH_MP (SPEC_ALL (cj 1 th))))) >>
  `ptr_covers (DRESTRICT G (COMPL (set inst.inst_outputs)))
      (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
      root returned rbuf.buf_size` by
    (simp[bodyPtrDefsTheory.ptr_covers_def,
          ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_DRESTRICT,
          venomStateTheory.eval_operand_def] >>
     conj_tac >- fs[ptrDisciplineTheory.op_taint_def] >>
     qexists `n2w off` >>
     `off < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_n2w] >>
     qpat_assum `eval_operand rbuf.buf_operand t = SOME (n2w off)` mp_tac >>
     qpat_assum `rbuf.buf_operand = Var root` (fn th => pure_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [venomStateTheory.eval_operand_def]) >>
  `MAP (\op. eval_operand op returned) (MAP Var inst.inst_outputs) =
     MAP SOME ir.iret_values` by
    (drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
     qpat_x_assum `returned = _` kall_tac >>
     irule listTheory.LIST_EQ >>
     simp[listTheory.EL_MAP, venomStateTheory.eval_operand_def]) >>
  `EVERY (\op. op_taint
      (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))) op = {})
      (MAP Var inst.inst_outputs)` by
    (simp[listTheory.EVERY_MEM, listTheory.MEM_MAP,
          ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
     rpt strip_tac >> qpat_x_assum `op = Var y` SUBST1_TAC >> simp[]) >>
  `lookup_var root returned = SOME (n2w off)` by
    (qpat_assum `eval_operand rbuf.buf_operand t = SOME (n2w off)` mp_tac >>
     qpat_assum `rbuf.buf_operand = Var root` (fn th => pure_rewrite_tac[th]) >>
     simp[venomStateTheory.eval_operand_def]) >>
  `~returned.vs_halted /\ returned.vs_current_bb = t.vs_current_bb` by
    (drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
     qpat_x_assum `returned = _` SUBST1_TAC >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[venomExecSemanticsTheory.adopt_return_fmp_def,
          venomExecSemanticsTheory.merge_callee_state_def] >>
     fs[fragGasFocusTheory.gas_invoke_entry_def]) >>
  `allocas_from lo returned` by
    (fs[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  `ptr_covers (DRESTRICT G (COMPL (set inst.inst_outputs)))
      (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
      root (returned with vs_inst_idx := SUC t.vs_inst_idx) rbuf.buf_size` by
    (qpat_assum `ptr_covers _ _ root returned _` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.eval_operand_def,
          venomStateTheory.lookup_var_def]) >>
  `ctx_has_dalloca ctx ==>
     allocas_below_fmp (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (strip_tac >>
     `allocas_below_fmp t` by metis_tac[] >>
     drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
     qpat_x_assum `returned = _` SUBST1_TAC >>
     qpat_x_assum `allocas_below_fmp t` mp_tac >>
     qpat_assum `ir.iret_adopt_fmp = NONE` (fn adopt =>
       simp_tac (srw_ss()) [adopt, venomExecSemanticsTheory.adopt_return_fmp_def,
         venomExecSemanticsTheory.merge_callee_state_def,
         ptrDisciplineTheory.allocas_below_fmp_def]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp returned` by
    (`allocas_below_fmp (returned with vs_inst_idx := SUC t.vs_inst_idx) <=>
        allocas_below_fmp returned` by
       simp[NoAsms, ptrDisciplineTheory.allocas_below_fmp_def] >>
     qpat_assum `allocas_below_fmp _ <=> allocas_below_fmp returned` (fn idx =>
       qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp
           (returned with vs_inst_idx := SUC t.vs_inst_idx)`
         (ACCEPT_TAC o PURE_REWRITE_RULE [idx]))) >>
  drule_at (Pat `ptr_covers _ _ _ _ _`)
    intCallResultFullTheory.store_multi_results_origin_ptr >>
  disch_then drule >>
  disch_then (mp_tac o SRULE [venomStateTheory.lookup_var_def,
                            venomStateTheory.eval_operand_def]) >>
  disch_then (drule_at (Pat `MAP _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (qspecl_then [`lo`,`gas_explicit_sites ctx shadow_ctx`,`n2w off`,`PG`] mp_tac) >>
  (impl_tac >-
    (simp[venomStateTheory.lookup_var_def, ptrDisciplineTheory.allocas_from_def,
          listTheory.MEM_MAP] >>
     `off < dimword (:256)` by decide_tac >>
     fs[venomStateTheory.lookup_var_def, wordsTheory.w2n_n2w] >>
     qpat_assum `allocas_from lo returned`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     qpat_assum `returned.vs_allocas = t.vs_allocas`
       (fn th => rewrite_tac[th]) >>
     simp[])) >>
  disch_then (qx_choose_then `stored` (qx_choose_then `Gs`
    (qx_choose_then `ts` strip_assume_tac))) >>
  `!H'. valid_horizon cx st0 H' ee.storage_trace ==>
     gas_origin_ptr_path
       (DF H',lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G,tn) marks
       (OK (stored with vs_inst_idx := LENGTH sm.cs_current_insts),Gs,ts)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H'` mp_tac) >>
     qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _`
       (qspec_then `H'` mp_tac) >>
     qpat_assum `valid_horizon cx st0 H' ee.storage_trace` mp_tac >>
     qpat_assum `LENGTH st4.cs_current_insts = SUC t.vs_inst_idx` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[] >> rpt strip_tac >>
     metis_tac[listTheory.APPEND_NIL,
       cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `full_scope marks (OK (stored with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     strip_tac >>
     `run_inst_seq (emitted_insts st4 sm)
        (returned with vs_inst_idx := SUC t.vs_inst_idx) = OK stored` by
       (qpat_assum `LENGTH st4.cs_current_insts = SUC t.vs_inst_idx`
          (fn th => qpat_assum `run_inst_seq _ _ = OK stored`
            (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
     `~(returned with vs_inst_idx := SUC t.vs_inst_idx).vs_halted /\
      (returned with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb = st4.cs_current_bb /\
      (returned with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = LENGTH st4.cs_current_insts` by simp[] >>
     drule_all intcall_return_scope_register >> simp[]) >>
  Cases_on `storage_trace_domain cx st0 out.storage_trace`
  >- suspend "register_post" >>
  rewrite_tac[intcall_return_witness_def] >> qexists `marks` >> disj1_tac >>
  conj_tac
  >- (irule gas_bad_storage_at_endpoint >>
      qexistsl [`out with scopes := prev`,`INL (Value v)`] >> simp[]) >>
  conj_tac >- (drule_all intcall_return_scope_bad >> simp[]) >>
  qexistsl [`storage_trace_horizon ee.storage_trace`,`func`,`PG`,`Gs`,`ts`,
    `stored with vs_inst_idx := LENGTH sm.cs_current_insts`] >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es1.storage_trace` irule >>
      gvs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_focus_rules) >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  strip_tac >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _` irule >>
  gvs[vyperStorageFootprintTheory.storage_trace_domain_def]
QED
Resume intcall_return_normal_tracked[register_post]:
  rewrite_tac[intcall_return_witness_def] >> qexists `marks` >> disj2_tac >>
  qexistsl [`INL (Value v)`,`out with scopes := prev`,
    `OK (stored with vs_inst_idx := LENGTH sm.cs_current_insts)`,`Gs`,`ts`] >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H' ee.storage_trace` by
    (`storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
       (simp[unlock_if_nr_def,
         vyperStorageTraceTheory.storage_trace_frame_optional_locks]) >>
     drule vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then (qspecl_then [`st0`,`out`,`ee with gas_obs := []`,
       `INL ()`,`cx`,`H'`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _` irule >> simp[]) >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm "entry" (qspec_then `H'` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `dead_lo_ok H' (DF H') lo cenv cx` by simp[] >>
  qpat_assum `!h. valid_horizon cx st0 h out.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `LENGTH st4.cs_current_insts = SUC t.vs_inst_idx`
    (fn th => qpat_assum `run_inst_seq _ _ = OK stored`
      (assume_tac o REWRITE_RULE [th])) >>
  qpat_assum `nret <> 0` (fn nz =>
    qpat_assum `intcall_callee_exit_full (DF,lo) H' func cenv cx mut nr rtv nret _ _ _ _ _ _ _ _ _`
      (assume_tac o REWRITE_RULE [nz])) >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
    (qspec_then `H'` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> ghost_kept_at _ _ _ _ _ _ _ _ _`
    (qspec_then `H'` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule intCallResultTheory.store_multi_results_shape >>
  simp[exprLoweringPropsTheory.same_blocks_def] >> strip_tac >>
  qpat_assum `LENGTH st4.cs_current_insts = SUC t.vs_inst_idx`
    (fn len => qpat_assum `stored with <|vs_memory := _; vs_vars := _|> = _`
      (assume_tac o SIMP_RULE (srw_ss())
        [len, venomStateTheory.venom_state_fupdcanon])) >>
  qpat_assum `aid = sa.cs_next_id` (fn aid_eq =>
    qpat_assum `FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size)`
      (assume_tac o PURE_REWRITE_RULE [aid_eq])) >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (n2w off : 256 word) = off` by simp[] >>
  mp_tac (let
    val th = SPEC_ALL (INST_TYPE [alpha |-> ``:256``] intcall_return_register_post)
    val rcs = List.filter (fn v => dest_var v = ("rc", ``:num``))
      (free_vars (concl th))
    val rcvar = case rcs of [v] => v | _ => raise Fail "unique rc variable absent"
    in Q.INST [`H` |-> `H'`, `ee` |-> `ee with gas_obs := []`,
      `outs` |-> `inst.inst_outputs`] (INST [rcvar |-> ``nret:num``] th)
    end) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (simp[venomStateTheory.venom_state_fupdcanon] >> NO_TAC) >>
      TRY (qpat_x_assum `stored with <|vs_memory := _; vs_vars := _|> = returned with vs_inst_idx := SUC t.vs_inst_idx` mp_tac >>
        simp_tac (srw_ss()) [venomStateTheory.venom_state_fupdcanon] >> NO_TAC) >>
      TRY (simp[venomStateTheory.lookup_var_def] >> NO_TAC) >>
      TRY (qpat_assum `!mem i. mem_agree_outside _ _ mem /\ i < _ ==> _` mp_tac >>
        simp_tac (srw_ss()) [wordsTheory.w2n_n2w] >>
        simp[] >> NO_TAC) >>
      qpat_assum `!a len. _ ==> mem_bytes_at a len stored.vs_memory = _` mp_tac >>
      simp[]) >>
  disch_then (mk_asm "certificate") >>
  `out with gas_obs := [] = out` by
    (qpat_assum `!tail. unlock_if_nr _ _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_assum `out with gas_obs := [] = out` mp_tac >>
  qpat_assum `vv = LocatedValue _ _` mp_tac >>
  qpat_assum `sm.cs_current_insts = _ ++ _` mp_tac >>
  qpat_assum `LENGTH st4.cs_current_insts = SUC t.vs_inst_idx` mp_tac >>
  qpat_assum `sm.cs_current_bb = t.vs_current_bb` mp_tac >>
  asm "certificate" mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  fs[loweringPostsTheory.post_value_type_def,
     exprSimVVFrameTheory.vv_post_inst_idx, contextTheory.base_ptr_def,
     contextTheory.vv_location_def] >>
  qhdtm_assum `vv_post`
    (assume_tac o cj 1 o PURE_REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
  drule stmt_state_rel_allocas_below_fmp >>
  simp[ptrDisciplineTheory.allocas_below_fmp_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Resume intcall_return_normal_tracked[intret_void]:
  gvs[] >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `~returned.vs_halted` by
    (qpat_assum `bind_outputs [] [] _ = SOME returned`
       (mp_tac o SRULE [venomExecSemanticsTheory.bind_outputs_def]) >>
     disch_then (SUBST1_TAC o SYM) >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[venomExecSemanticsTheory.adopt_return_fmp_def,
          venomExecSemanticsTheory.merge_callee_state_def] >>
     fs[fragGasFocusTheory.gas_invoke_entry_def]) >>
  `!H'. valid_horizon cx st0 H' ee.storage_trace ==>
     gas_origin_ptr_path
       (DF H',lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G,tn) marks
       (OK (returned with vs_inst_idx := SUC t.vs_inst_idx),G,
        tc with t_var := tn.t_var)` by
    (rpt strip_tac >>
     qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _`
       (qspec_then `H'` mp_tac) >>
     qpat_assum `valid_horizon cx st0 H' ee.storage_trace` mp_tac >>
     qpat_assum `~returned.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[finite_mapTheory.DRESTRICT_UNIV] >> rpt strip_tac >>
     GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites
       [GSYM listTheory.APPEND_NIL] >>
     irule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
     goal_assum (drule_at Any) >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `full_scope marks (OK (returned with vs_inst_idx := SUC t.vs_inst_idx))` by
    (qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     strip_tac >>
     `returned.vs_current_bb = t.vs_current_bb` by
       (qpat_assum `bind_outputs [] [] _ = SOME returned`
          (mp_tac o SRULE [venomExecSemanticsTheory.bind_outputs_def]) >>
        disch_then (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_current_bb`) >>
        simp[venomExecSemanticsTheory.adopt_return_fmp_def,
             venomExecSemanticsTheory.merge_callee_state_def]) >>
     irule intcall_return_scope_void >> goal_assum (drule_at Any) >>
     first_assum (irule_at Any) >> simp[]) >>
  Cases_on `storage_trace_domain cx st0 out.storage_trace`
  >- suspend "void_post" >>
  rewrite_tac[intcall_return_witness_def] >> qexists `marks` >> disj1_tac >>
  conj_tac
  >- (irule gas_bad_storage_at_endpoint >>
      qexistsl [`out with scopes := prev`,`INL (Value v)`] >> simp[]) >>
  conj_tac >- (drule_all intcall_return_scope_bad >> simp[]) >>
  qexistsl [`storage_trace_horizon ee.storage_trace`,`func`,`PG`,`G`,
    `tc with t_var := tn.t_var`,`returned with vs_inst_idx := SUC t.vs_inst_idx`] >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es1.storage_trace` irule >>
      gvs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_focus_rules) >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _` irule >>
  gvs[vyperStorageFootprintTheory.storage_trace_domain_def]
QED
Resume intcall_return_normal_tracked[void_post]:
  rewrite_tac[intcall_return_witness_def] >> qexists `marks` >> disj2_tac >>
  qexistsl [`INL (Value v)`,`out with scopes := prev`,
    `OK (returned with vs_inst_idx := SUC t.vs_inst_idx)`,`G`,`tc with t_var := tn.t_var`] >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H' ee.storage_trace` by
    (`storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
       (simp[unlock_if_nr_def,
         vyperStorageTraceTheory.storage_trace_frame_optional_locks]) >>
     drule vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then (qspecl_then [`st0`,`out`,`ee with gas_obs := []`,
       `INL ()`,`cx`,`H'`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _` irule >> simp[]) >>
  qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm "entry" (qspec_then `H'` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `dead_lo_ok H' (DF H') lo cenv cx` by simp[] >>
  `unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) =
      (INL (),out)` by
    (qpat_assum `!tail. (if _ then _ else _) _ = _`
       (qspec_then `[]` mp_tac) >>
     simp[unlock_if_nr_def, is_view_mut_def]) >>
  `bind_outputs [] ir.iret_values
      (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned` by simp[] >>
  `!x:string. MEM x [] ==> ~not_fresh_at sa x` by simp[] >>
  qpat_assum `!h. valid_horizon cx st0 h out.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `stmt_state_rel H' ctx func cenv cx _ returned`
    (assume_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  `ctx_has_dalloca ctx ==>
     allocas_below_fmp (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_assum `stmt_state_rel H' ctx func cenv cx _ returned`
       (mp_tac o MATCH_MP (SPEC_ALL stmt_state_rel_allocas_below_fmp)) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all intcall_return_caller_frame >> strip_tac >>
  drule_all intcall_return_type_facts >> strip_tac >>
  `returned.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `bind_outputs [] [] _ = SOME returned` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomExecSemanticsTheory.bind_outputs_def,
       venomExecSemanticsTheory.adopt_return_fmp_def,
       venomExecSemanticsTheory.merge_callee_state_def] >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[venomExecSemanticsTheory.adopt_return_fmp_def] >>
     disch_then (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_current_bb`) >> simp[]) >>
  `alloca_history func (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (map_every (fn p => qpat_assum p mp_tac)
       [`alloca_history func t`, `get_instruction bb t.vs_inst_idx = SOME inst`,
        `inst.inst_opcode = INVOKE`,
        `lookup_block t.vs_current_bb func.fn_blocks = SOME bb`,
        `bind_outputs [] [] _ = SOME returned`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_x_assum `bind_outputs [] [] _ = SOME returned` mp_tac >>
     simp[venomExecSemanticsTheory.bind_outputs_def] >>
     disch_then (SUBST_ALL_TAC o SYM) >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[venomExecSemanticsTheory.adopt_return_fmp_def,
          venomExecSemanticsTheory.merge_callee_state_def,
          allocaHistoryTheory.alloca_history_def] >>
     fs[allocaHistoryTheory.alloca_history_def] >> rpt strip_tac >>
     Cases_on `k = t.vs_inst_idx` >> gvs[] >>
     metis_tac[prim_recTheory.LESS_THM, optionTheory.SOME_11]) >>
  `ghost_inv_at (DF H') lo d cenv cx (out with scopes := prev) G
     (tc with t_var := tn.t_var) (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
       (qspec_then `H'` mp_tac) >>
     (impl_tac >- simp[]) >>
     rpt (pop_assum kall_tac) >>
     Cases_on `d` >> TRY (PairCases_on `x`) >>
     simp[finite_mapTheory.DRESTRICT_UNIV, bodyPtrDefsTheory.ghost_inv_at_def,
       bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.return_buf_ptr_def,
       bodyPtrDefsTheory.stor_taint_ok_at_def,
       venomStateTheory.lookup_var_def, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  `ghost_kept_at lo cenv es0 sa G0 tn0 s0 G (tc with t_var := tn.t_var)` by
    (qpat_assum `!H'. valid_horizon cx st0 H' ee.storage_trace ==> ghost_kept_at _ _ _ _ _ _ _ _ _`
       (qspec_then `H'` mp_tac) >> simp[finite_mapTheory.DRESTRICT_UNIV]) >>
  Cases_on `rbs = 0`
  >- suspend "void_no_buffer" >>
  suspend "void_buffer"
QED
Resume intcall_return_normal_tracked[void_no_buffer]:
 `vv = StackValue ret (Lit 0w)` by
   (qpat_assum `cenv.ce_func_info _ = _` mp_tac >>
    qpat_assum `cenv.ce_func_return_type _ = _` mp_tac >>
    qpat_assum `rbs = 0` mp_tac >>
    qhdtm_assum `intcall_entry_full` mp_tac >>
    rpt (pop_assum kall_tac) >>
    pure_rewrite_tac[intcall_entry_full_def] >>
    rpt strip_tac >>
    qpat_x_assum `_ = 0 /\ _ = 0 ==> _` mp_tac >>
    qpat_x_assum `cenv.ce_func_info _ = (0,_,_)` mp_tac >>
    qpat_assum `cenv.ce_func_info _ = (_,_,_)` mp_tac >>
    qpat_assum `cenv.ce_func_return_type _ = _` mp_tac >>
    qpat_assum `rbs = 0` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
 `cenv.ce_func_info (nsid_to_string (NONE,name)) = (0,0,pvs)` by simp[] >>
 `ret = NoneT \/ type_memory_bytes cenv ret = 0` by
   (drule_all callable_func_info_in_env >>
    simp[compileEnvTheory.compute_func_info_def] >> Cases_on `ret` >> simp[]) >>
 pop_assum strip_assume_tac
 >- suspend "void_none" >>
 suspend "void_zero_layout"
QED
Resume intcall_return_normal_tracked[void_none]:
 `ret = NoneT` by metis_tac[] >>
 `ann = NoneT` by fs[vyperTypeArgFitsTheory.type_widens_to_NoneT] >>
 `rtv = NoneTV` by fs[vyperValueTheory.evaluate_type_def] >>
 `v = NoneV` by
   (qpat_assum `value_has_type rtv v` mp_tac >>
    qpat_assum `rtv = NoneTV` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[vyperTypeValuesTheory.value_has_type_NoneTV]) >>
 simp[exprLoweringTheory.lowered_value_type_def,
   loweringPostsTheory.post_value_type_def,
   compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
 conj_tac >- suspend "void_none_vv" >>
 conj_tac >- (simp[exprSimMemDefsTheory.vv_store_bound_def,
   compileEnvTheory.is_word_type_def, read_result_def,
   vyperValueTheory.evaluate_type_def,
   exprSimPropsTheory.val_store_size_def,
   valueEncodingTheory.type_memory_size_def,
   vyperTypeValuesTheory.value_has_type_NoneTV,
   venomStateTheory.eval_operand_def, return_def]) >>
 simp[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
   compileEnvTheory.is_word_type_def, contextTheory.vv_location_def,
   read_result_def, return_def, ptrDisciplineTheory.op_taint_def] >>
 simp[bodyPtrDefsTheory.ptr_buf_ok_def,
   exprLoweringTheory.lowered_value_type_def,
   compileEnvTheory.type_memory_bytes_def,
   bodyPtrDefsTheory.ptr_mem_ok_def, read_result_def, return_def,
   vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
   venomStateTheory.eval_operand_def, valueEncodingDefsTheory.val_in_memory_def,
   loweringPostsTheory.val_footprint_def, loweringPostsTheory.vv_own_def,
   loweringPostsTheory.expr_val_own_def]
QED
Resume intcall_return_normal_tracked[void_none_vv]:
 simp[loweringPostsTheory.vv_post_def,
   loweringPostsTheory.post_value_type_def,
   exprLoweringTheory.lowered_value_type_def,
   compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
 simp[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
   contextTheory.vv_operand_def, read_result_def, return_def,
   vyperValueTheory.evaluate_type_def, valueEncodingDefsTheory.val_in_memory_def,
   venomStateTheory.eval_operand_def, valueEncodingTheory.type_memory_size_def,
   vyperASTTheory.expr_type_def,
   loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
   compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
   valueEncodingDefsTheory.val_wf_def] >>
 qpat_assum `!aid b sz. _ ==> mem_bytes_at b sz returned.vs_memory = _` mp_tac >>
 simp[]
QED
Resume intcall_return_normal_tracked[void_zero_layout]:
 `expr_sim_inv cenv cx tenv es0` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
 `type_memory_bytes cenv ret = type_memory_size rtv` by
   metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
 `type_memory_size rtv = 0` by metis_tac[] >>
 `val_wf rtv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
 `!p mem. val_in_memory rtv v p mem` by
   metis_tac[valueEncodingProofsTheory.return_zero_wf_memory] >>
 `val_footprint rtv v = 0` by (drule exprSimPropsTheory.val_footprint_le >> simp[]) >>
 `type_memory_bytes cenv ret = 0` by metis_tac[] >>
 `~is_word_type ret /\ ~is_bytestring_type ret` by
   (qpat_assum `type_memory_bytes cenv ret = 0` mp_tac >>
    rpt (pop_assum kall_tac) >> Cases_on `ret` >>
    simp[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def,
        compileEnvTheory.type_memory_bytes_def] >>
    Cases_on `b` >> gvs[compileEnvTheory.is_word_type_def,
      compileEnvTheory.is_bytestring_type_def, compileEnvTheory.type_memory_bytes_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >>
    gvs[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def,
        compileEnvTheory.type_memory_bytes_def]) >>
 `~is_word_type ann /\ ~is_bytestring_type ann` by
   metis_tac[compileEnvTheory.type_widens_to_word,
     vyperTypeSystemTheory.type_widens_to_def,
     compileEnvTheory.arg_type_fits_bytestring_source] >>
 conj_tac >- suspend "void_zero_vv" >>
 conj_tac >- suspend "void_zero_bound" >>
 suspend "void_zero_frame"
QED
Resume intcall_return_normal_tracked[void_zero_vv]:
 simp[loweringPostsTheory.vv_post_def,
   loweringPostsTheory.post_value_type_def,
   exprLoweringTheory.lowered_value_type_def] >>
 simp[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
   contextTheory.vv_operand_def, read_result_def, return_def,
   loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
   venomStateTheory.eval_operand_def,
   loweringPostsTheory.vv_own_def, loweringPostsTheory.expr_val_own_def] >>
 qpat_assum `!aid b sz. _ ==> mem_bytes_at b sz returned.vs_memory = _` mp_tac >>
 simp[]
QED
Resume intcall_return_normal_tracked[void_zero_bound]:
 `val_store_size rtv v = 0` by
   (drule exprSimPropsTheory.val_store_size_le >> simp[]) >>
 simp[exprSimMemDefsTheory.vv_store_bound_def,
   exprLoweringTheory.lowered_value_type_def, read_result_def, return_def,
   venomStateTheory.eval_operand_def]
QED
Resume intcall_return_normal_tracked[void_zero_frame]:
 simp[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
   exprLoweringTheory.lowered_value_type_def, loweringPostsTheory.post_value_type_def,
   contextTheory.vv_location_def, read_result_def, return_def,
   ptrDisciplineTheory.op_taint_def] >>
 conj_tac >-
   simp[bodyPtrDefsTheory.ptr_mem_ok_def, venomStateTheory.eval_operand_def] >>
 simp[bodyPtrDefsTheory.ptr_buf_ok_def, exprLoweringTheory.lowered_value_type_def,
   loweringPostsTheory.vv_own_def, loweringPostsTheory.expr_val_own_def,
   read_result_def, return_def, venomStateTheory.eval_operand_def]
QED
Resume intcall_return_normal_tracked[void_buffer]:
 `?rbuf off.
    vv = LocatedValue ret (base_ptr rbuf) /\
    eval_operand rbuf.buf_operand t = SOME (n2w off) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size) /\
    HD argv = n2w off /\ type_memory_size rtv <= rbuf.buf_size /\
    w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    map_every (fn p => qpat_assum p mp_tac)
      [`cenv.ce_func_info _ = (0,rbs,pvs)`, `rbs <> 0`,
       `cenv.ce_func_return_type _ = ret`,
       `lookup_block t.vs_current_bb func.fn_blocks = SOME bb`,
       `get_instruction bb t.vs_inst_idx = SOME inst`,
       `decode_invoke inst = SOME (lbl,arg_ops)`,
       `eval_operands arg_ops t = SOME argv`] >>
    rpt (pop_assum kall_tac) >> rpt disch_tac >>
    qhdtm_x_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> strip_tac >>
    map_every (fn p => qpat_assum p mp_tac)
      [`0 < _ \/ 0 < _ ==> _`,
       `cenv.ce_func_info _ = (rc',rbs',pvs')`,
       `cenv.ce_func_info _ = (0,rbs,pvs)`, `rbs <> 0`,
       `cenv.ce_func_return_type _ = ret`,
       `lookup_block t.vs_current_bb func.fn_blocks = SOME bb'`,
       `get_instruction bb' t.vs_inst_idx = SOME inst'`,
       `decode_invoke inst' = SOME (lbl',arg_ops')`,
       `eval_operands arg_ops' t = SOME argv'`,
       `lookup_block t.vs_current_bb func.fn_blocks = SOME bb`,
       `get_instruction bb t.vs_inst_idx = SOME inst`,
       `decode_invoke inst = SOME (lbl,arg_ops)`,
       `eval_operands arg_ops t = SOME argv`] >>
    rpt (pop_assum kall_tac) >> rpt disch_tac >>
    gvs[] >> metis_tac[]) >>
 `?x b. rbuf.buf_operand = Var x /\ op_taint tn (Var x) = {} /\
    FLOOKUP G x = SOME (b,rbuf.buf_size) /\
    eval_operand rbuf.buf_operand t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,rbuf.buf_size) /\
    sa.cs_next_id < sm.cs_next_id /\ lo <= b /\
    b + rbuf.buf_size <= t.vs_alloca_next` by
   (qpat_assum `!ty' p buf. vv = LocatedValue ty' p /\ p.ptr_buf = SOME buf ==> _` mp_tac >>
    qpat_assum `vv = LocatedValue ret (base_ptr rbuf)` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[contextTheory.base_ptr_def] >>
    metis_tac[]) >>
 `!mem. mem_agree_outside tc.t_mem returned.vs_memory mem ==>
    val_in_memory rtv v (w2n (HD argv)) mem` by
   (qpat_assum `intcall_callee_exit_full _ H' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    qpat_assum `rbs <> 0` mp_tac >>
    qpat_assum `returned.vs_memory = cs.vs_memory` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[intcall_callee_exit_full_def] >> metis_tac[]) >>
 `b = off` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
 `eval_operand rbuf.buf_operand returned = SOME (n2w off)` by
   (qpat_assum `eval_operand rbuf.buf_operand t = SOME (n2w off)` mp_tac >>
    qpat_assum `rbuf.buf_operand = Var x` mp_tac >>
    qpat_assum `!x. ~MEM x [] ==> lookup_var x returned = lookup_var x t` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[venomStateTheory.eval_operand_def]) >>
 `!name entry p sz. lookup_scopes name prev = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sa p` by
   (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
 `!name b sz. local_region cenv prev returned name b sz <=>
              local_region cenv prev t name b sz` by
   (irule loweringStateRelDefsTheory.local_region_lookup_cong >> metis_tac[]) >>
 `!name b sz. local_region cenv prev returned name b sz ==>
    b + sz <= off \/ off + rbuf.buf_size <= b` by
   (map_every qx_gen_tac [`nm`,`lb`,`sz`] >> strip_tac >>
    `local_region cenv prev t nm lb sz` by metis_tac[] >>
    qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> strip_tac >>
    qpat_x_assum `!n lo sz aid off asz. _` drule >>
    disch_then (drule_at Any) >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
 `off + rbuf.buf_size < dimword (:256)` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >>
    disch_then (assume_tac o cj 7) >>
    drule exprSimPropsTheory.stmt_state_rel_region_lt >>
    disch_then (mp_tac o cj 1) >>
    disch_then (qspecl_then [`sa.cs_next_id`,`off`,`rbuf.buf_size`] mp_tac) >> simp[]) >>
 `off < dimword (:256)` by decide_tac >>
 `!tvt. evaluate_type (get_tenv cx)
    (if is_word_type ann \/ is_bytestring_type ann then ann else ret) = SOME tvt ==>
    val_store_size tvt v = val_store_size rtv v` by
   (map_every (fn p => qpat_assum p mp_tac)
      [`evaluate_type (get_tenv cx) ret = SOME rtv`, `value_has_type rtv v`,
       `type_widens_to (get_tenv cx) ret ann`] >>
    rpt (pop_assum kall_tac) >> rpt disch_tac >>
    Cases_on `is_word_type ann` >-
      (`ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[]) >>
    Cases_on `is_bytestring_type ann` >> gvs[] >> rpt strip_tac >>
    `is_bytestring_type ret` by
      metis_tac[compileEnvTheory.arg_type_fits_bytestring_source,
        vyperTypeSystemTheory.type_widens_to_def] >>
    `value_has_type tvt v` by
      metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type,
        optionTheory.SOME_11] >>
    irule valueCopyBytesTheory.bytestring_val_store_size_eq >>
    reverse conj_tac >- simp[] >>
    qexistsl [`ann`,`ret`,`get_tenv cx`] >> simp[]) >>
 `!i n b sz. local_region cenv prev (returned with vs_inst_idx := i) n b sz <=>
             local_region cenv prev returned n b sz` by
   simp_tac (srw_ss())
     [loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def] >>
 `~(is_word_type ann \/ is_bytestring_type ann) ==>
     vv_own cenv cx ret sa sm (out with scopes := prev)
       (Value v) vv (returned with vs_inst_idx := LENGTH sm.cs_current_insts)` by
   suspend "buffer_own" >>
 conj_tac >- suspend "buffer_vv" >>
 conj_tac >- suspend "buffer_bound" >>
 suspend "buffer_frame"
QED
Resume intcall_return_normal_tracked[buffer_bound]:
 `val_wf rtv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
 `val_store_size rtv v <= type_memory_size rtv` by
   metis_tac[exprSimPropsTheory.val_store_size_le] >>
 pure_rewrite_tac[exprSimMemDefsTheory.vv_store_bound_def] >>
 simp[loweringPostsTheory.post_value_type_def, exprLoweringTheory.lowered_value_type_def,
   contextTheory.base_ptr_def, read_result_def, return_def] >>
 rpt conj_tac >> rpt strip_tac >>
 `eval_operand (Var x) returned = SOME (n2w off)` by metis_tac[] >>
 `w = n2w off` by metis_tac[optionTheory.SOME_11] >>
 simp[] >>
 qpat_assum `w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next` mp_tac >>
 qpat_assum `HD argv = n2w off` mp_tac >>
 qpat_assum `val_store_size rtv v <= type_memory_size rtv` mp_tac >>
 rpt (pop_assum kall_tac) >> simp[]
QED
Resume intcall_return_normal_tracked[buffer_vv]:
 pure_rewrite_tac[loweringPostsTheory.vv_post_def] >>
 simp[] >>
 conj_tac >- suspend "buffer_holds" >>
 conj_tac >- suspend "buffer_at" >>
 conj_tac >-
   (simp[loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def,
      exprLoweringTheory.lowered_value_type_def] >>
    Cases_on `is_word_type ann` >> Cases_on `is_bytestring_type ann` >> simp[] >>
    qpat_x_assum `vv = LocatedValue ret (base_ptr rbuf)` SUBST_ALL_TAC >>
    qpat_x_assum `_ ==> vv_own cenv cx ret sa sm _ _ _ _` mp_tac >>
    simp[loweringPostsTheory.vv_own_def, contextTheory.base_ptr_def,
         venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
 qpat_assum `!aid b sz. _ ==> mem_bytes_at b sz returned.vs_memory = _` mp_tac >>
 simp[]
QED
Resume intcall_return_normal_tracked[buffer_holds]:
 `!mem. mem_agree_outside tc.t_mem returned.vs_memory mem ==>
    val_in_memory rtv v (w2n (n2w off : bytes32)) mem` by metis_tac[] >>
 map_every (fn p => qpat_assum p mp_tac)
   [`evaluate_type (get_tenv cx) ret = SOME rtv`, `value_has_type rtv v`,
    `type_widens_to (get_tenv cx) ret ann`,
    `cenv.ce_func_return_type _ = ret`,
    `eval_operand rbuf.buf_operand returned = SOME (n2w off)`,
    `!mem. mem_agree_outside tc.t_mem returned.vs_memory mem ==> val_in_memory rtv v (w2n (n2w off : bytes32)) mem`] >>
 rpt (pop_assum kall_tac) >> rpt disch_tac >>
 simp[loweringPostsTheory.vv_holds_def, exprLoweringTheory.lowered_value_type_def,
   contextTheory.base_ptr_def, read_result_def, return_def] >>
 Cases_on `is_word_type ann` >-
   (`ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >>
    gvs[] >> metis_tac[exprSimPropsTheory.val_in_memory_word_type,
      bodyPtrDefsTheory.mem_agree_outside_def]) >>
 Cases_on `is_bytestring_type ann` >> simp[] >-
   (`is_bytestring_type ret` by
      metis_tac[compileEnvTheory.arg_type_fits_bytestring_source,
        vyperTypeSystemTheory.type_widens_to_def] >>
    `?atv. evaluate_type (get_tenv cx) ann = SOME atv /\ value_has_type atv v` by
      metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type] >>
    simp[] >> rpt strip_tac >>
    irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
    conj_tac >- simp[] >>
    qexistsl [`ret`, `ann`, `get_tenv cx`, `rtv`] >>
    simp[] >>
    qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _` (qspec_then `returned.vs_memory` mp_tac) >>
    simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
 qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _`
   (qspec_then `returned.vs_memory` mp_tac) >>
 simp[bodyPtrDefsTheory.mem_agree_outside_def] >> strip_tac >>
 strip_tac >> metis_tac[exprSimPropsTheory.val_in_memory_word_type]
QED
Resume intcall_return_normal_tracked[buffer_at]:
 simp[loweringPostsTheory.vv_at_def, contextTheory.base_ptr_def,
   read_result_def, return_def, exprLoweringTheory.lowered_value_type_def] >>
 rpt gen_tac >> disch_tac >>
 `value_has_type tvt v` by
   (map_every (fn p => qpat_assum p mp_tac)
      [`evaluate_type (get_tenv cx) ret = SOME rtv`, `value_has_type rtv v`,
       `type_widens_to (get_tenv cx) ret ann`,
       `evaluate_type (get_tenv cx) (if _ then _ else _) = SOME tvt`] >>
    rpt (pop_assum kall_tac) >> rpt disch_tac >>
    Cases_on `is_word_type ann` >-
      (`ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[]) >>
    Cases_on `is_bytestring_type ann` >>
    gvs[] >> metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type,
      optionTheory.SOME_11]) >>
 conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
 `val_footprint tvt v <= type_memory_size rtv` by
   (map_every (fn p => qpat_assum p mp_tac)
      [`evaluate_type (get_tenv cx) ret = SOME rtv`, `value_has_type rtv v`,
       `value_has_type tvt v`, `type_widens_to (get_tenv cx) ret ann`,
       `evaluate_type (get_tenv cx) (if _ then _ else _) = SOME tvt`] >>
    rpt (pop_assum kall_tac) >> rpt disch_tac >>
    Cases_on `is_word_type ann` >-
      (`ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >>
       gvs[] >> metis_tac[exprSimPropsTheory.val_footprint_le,
         valueEncodingTypingTheory.value_has_type_val_wf]) >>
    Cases_on `is_bytestring_type ann` >> gvs[] >-
      (`is_bytestring_type ret` by
         metis_tac[compileEnvTheory.arg_type_fits_bytestring_source,
           vyperTypeSystemTheory.type_widens_to_def] >>
       irule valueCopyBytesTheory.bytestring_val_footprint_le >>
       conj_tac >- (qexistsl [`ann`,`ret`,`get_tenv cx`] >> simp[]) >>
       simp[]) >>
    metis_tac[exprSimPropsTheory.val_footprint_le,
      valueEncodingTypingTheory.value_has_type_val_wf]) >>
 qexists_tac `n2w off` >> conj_tac >- metis_tac[] >>
 disj1_tac >> qexistsl [`sa.cs_next_id`,`off`,`rbuf.buf_size`] >>
 simp[] >> metis_tac[]
QED
Resume intcall_return_normal_tracked[buffer_own]:
 strip_tac >>
 simp[loweringPostsTheory.vv_own_def, contextTheory.base_ptr_def,
   read_result_def, return_def] >>
 `val_footprint rtv v <= type_memory_size rtv` by
   metis_tac[exprSimPropsTheory.val_footprint_le,
     valueEncodingTypingTheory.value_has_type_val_wf] >>
 qexists_tac `n2w off` >> conj_tac >- metis_tac[] >>
 disj1_tac >> qexistsl [`sa.cs_next_id`,`off`,`rbuf.buf_size`] >>
 simp[] >> metis_tac[]
QED
Resume intcall_return_normal_tracked[buffer_frame]:
 simp[contextTheory.base_ptr_def, contextTheory.vv_location_def] >>
 conj_tac >- suspend "buffer_ptr" >>
 conj_tac >-
   (simp[loweringPostsTheory.post_value_type_def, exprLoweringTheory.lowered_value_type_def] >>
    Cases_on `is_word_type ann` >> Cases_on `is_bytestring_type ann` >>
    gvs[contextTheory.base_ptr_def]) >>
 suspend "buffer_buf"
QED
Resume intcall_return_normal_tracked[buffer_ptr]:
 simp[bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.base_ptr_def,
   read_result_def, return_def, ptrDisciplineTheory.op_taint_def] >>
 simp[bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.base_ptr_def,
   read_result_def, return_def, ptrDisciplineTheory.op_taint_def,
   exprLoweringTheory.lowered_value_type_def] >>
 conj_tac >-
   (qpat_assum `op_taint tn (Var x) = {}` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[ptrDisciplineTheory.op_taint_def]) >>
 simp[bodyPtrDefsTheory.ptr_mem_ok_def] >>
 map_every qx_gen_tac [`tvt`,`w`] >> strip_tac >>
 `w = n2w off` by
   (qpat_assum `eval_operand rbuf.buf_operand returned = SOME (n2w off)` mp_tac >>
    qpat_assum `rbuf.buf_operand = Var x` mp_tac >>
    qpat_assum `eval_operand (Var x) _ = SOME w` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[]) >>
 conj_tac >- suspend "buffer_ptr_bytes" >>
 suspend "buffer_ptr_extent"
QED
Resume intcall_return_normal_tracked[buffer_buf]:
 simp[bodyPtrDefsTheory.ptr_buf_ok_def, contextTheory.base_ptr_def] >>
 `expr_sim_inv cenv cx tenv es0` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
 `type_memory_bytes cenv ret = type_memory_size rtv` by
   metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
 simp[exprLoweringTheory.lowered_value_type_def] >>
 rpt strip_tac >>
 `w = n2w off` by
   (qpat_assum `eval_operand rbuf.buf_operand returned = SOME (n2w off)` mp_tac >>
    qpat_assum `rbuf.buf_operand = Var x` mp_tac >>
    qpat_assum `eval_operand (Var x) _ = SOME w` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[]) >>
 simp[]
QED
Resume intcall_return_normal_tracked[buffer_ptr_bytes]:
 map_every (fn p => qpat_assum p mp_tac)
   [`evaluate_type (get_tenv cx) ret = SOME rtv`, `value_has_type rtv v`,
    `type_widens_to (get_tenv cx) ret ann`,
    `evaluate_type (get_tenv cx) (if _ then _ else _) = SOME tvt`,
    `w = n2w off`, `HD argv = n2w off`,
    `returned.vs_memory = cs.vs_memory`,
    `!mem. mem_agree_outside tc.t_mem returned.vs_memory mem ==> _`] >>
 rpt (pop_assum kall_tac) >> rpt disch_tac >> simp[] >>
 Cases_on `is_word_type ann` >-
   (`ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[]) >>
 Cases_on `is_bytestring_type ann` >> gvs[] >>
 `is_bytestring_type ret` by
   metis_tac[compileEnvTheory.arg_type_fits_bytestring_source,
     vyperTypeSystemTheory.type_widens_to_def] >>
 `value_has_type tvt v` by
   metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type,
     optionTheory.SOME_11] >>
 rpt strip_tac >>
 irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
 conj_tac >- simp[] >>
 qexistsl [`ret`, `ann`, `get_tenv cx`, `rtv`] >> simp[]
QED
Resume intcall_return_normal_tracked[buffer_ptr_extent]:
 `val_wf rtv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
 `val_store_size rtv v <= type_memory_size rtv` by
   metis_tac[exprSimPropsTheory.val_store_size_le] >>
 map_every (fn p => qpat_assum p mp_tac)
   [`w = n2w off`, `off < dimword (:256)`,
    `type_memory_size rtv <= rbuf.buf_size`,
    `val_store_size rtv v <= type_memory_size rtv`] >>
 rpt (pop_assum kall_tac) >> simp[]
QED
Finalise intcall_return_normal_tracked

Theorem intcall_return_normal_owned:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs callee entered bb inst lbl arg_ops argv dflts.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
    compile_expr (gasShadowCompileBase$gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa = (vv,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
    (?marks res ee r Gc tc.
       (!tail. intcall_callee_src cx name mut nr ss
          (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
            (res,ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       !H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path
           (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
           (entered,FEMPTY,tn with t_var := FEMPTY) marks (r,Gc,tc) /\
         ((?u. r = OK u /\ F) \/
          (exit_result r /\
           intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id sm.cs_next_id t tn res (ee with gas_obs := []) (Gc,tc) r))) ==>
    (fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func ==>
     gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
       (\H res ee G tn t'. ?tv. res = INL tv /\
         vv_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
           es0 sa sm s0 ee tv vv t' /\
         vv_store_bound cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
           (lowered_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ee tv vv t' /\
         t'.vs_current_bb = sm.cs_current_bb /\ t'.vs_inst_idx = LENGTH sm.cs_current_insts /\
         alloca_history func t' /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
         ptr_vv_ok cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) tv vv ee G tn t' /\
         (!v. tv = Value v /\
              ~is_word_type
                (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) /\
              ~is_bytestring_type
                (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
              vv_own cenv cx
                (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
                sa sm ee tv vv t' /\
              (!ty' p. vv = LocatedValue ty' p ==> p.ptr_location = LocMemory)) /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee = (INL val,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) = SOME rt /\
              eval_operand (vv_operand vv) t' = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem t'.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
         (!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
            ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) op G t') /\
         (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) p.ptr_operand G t') /\
         ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  rpt gen_tac >>
  disch_then (mp_tac o MATCH_MP
    (Q.INST [`bad_scope` |-> `\marks. T`, `full_scope` |-> `\marks r. T`]
      (SPEC_ALL intcall_return_normal_tracked))) >>
  simp[intcall_return_scope_rules_def] >>
  metis_tac[intcall_return_witness_full]
QED
