(* The full reason head's compiler interval and shared unwrap input. *)
Theory bodyFullRaiseReasonHeadFrame
Ancestors
  bodyFullRaiseReasonHeadValue bodyFullRaiseReasonHeadGhost bodyFullRaiseReasonHead
  bodyFullUnwrap revertReasonLayout stmtReasonLitFragMemory allocaHistoryFragment
  stmtReasonMemory revertReasonPrefixPtr vyperStorageFootprint abiPathAllocInv
  exprSimVVFrame exprLoweringProps freshWrites loweringPosts loweringStateRelDefs
  fragExec venomExecSemantics venomInst venomState list rich_list arithmetic

Theorem reason_head_compiler_frame:
  sb = sm with <|cs_next_var := sm.cs_next_var + 3;
    cs_next_id := sm.cs_next_id + 4;
    cs_current_insts := sm.cs_current_insts ++
      revert_reason_prefix sm.cs_next_id sm.cs_next_var M|> /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (reason_head sm.cs_next_id sm.cs_next_var M) s = OK t ==>
  ?bb.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (reason_head sm.cs_next_id sm.cs_next_var M)
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    (!i. MEM i (reason_head sm.cs_next_id sm.cs_next_var M) ==>
      MEM i (fn_insts func)) /\
    alloca_history func (t with vs_inst_idx := s.vs_inst_idx + 4) /\
    ~(t with vs_inst_idx := s.vs_inst_idx + 4).vs_halted /\
    (t with vs_inst_idx := s.vs_inst_idx + 4).vs_current_bb = sb.cs_current_bb /\
    (t with vs_inst_idx := s.vs_inst_idx + 4).vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     reason_head sm.cs_next_id sm.cs_next_var M` by
    simp[reason_head_def, revert_reason_prefix_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  `LENGTH (reason_head sm.cs_next_id sm.cs_next_var M) = 4` by
    simp[reason_head_def] >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted` by
    (qpat_assum `run_inst_seq _ _ = _` mp_tac >>
     pure_rewrite_tac [reason_head_def] >>
     strip_tac >> drule run_inst_seq_four_endpoint >> strip_tac >>
     gvs[step_alloca_eq, step_add_eq, step_mstore_eq, AllCaseEqs(),
        update_var_def, mstore_def]) >>
  simp[] >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx +
     LENGTH (reason_head sm.cs_next_id sm.cs_next_var M))` suffices_by simp[] >>
  irule alloca_history_run_inst_seq >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  simp[reason_head_def, mk_inst_def, is_terminator_def]
QED

Theorem reason_head_unwrap_inputs:
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sb = sm with <|cs_next_var := sm.cs_next_var + 3;
    cs_next_id := sm.cs_next_id + 4;
    cs_current_insts := sm.cs_current_insts ++
      revert_reason_prefix sm.cs_next_id sm.cs_next_var M|> /\
  fn_has_code sm sb func /\ 64+M < dimword (:256) /\
  z = t with vs_inst_idx := s.vs_inst_idx + 4 /\
  run_inst_seq (reason_head sm.cs_next_id sm.cs_next_var M) s = OK t /\
  (!D. inst_seq_ptr D lo ctx func PG G tn
      (reason_head sm.cs_next_id sm.cs_next_var M) s Gf tnf /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) ==>
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gf tnf z) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv z /\
  alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gf tnf z /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 Gf z) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gf z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) z = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >> strip_tac >>
  `alloca_inv s` by fs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  drule_all reason_head_compiler_frame >> strip_tac >>
  `alloca_inv t` by metis_tac[run_inst_seq_alloca_inv] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
    (reason_head sm.cs_next_id sm.cs_next_var M) s Gf tnf` by metis_tac[] >>
  `!k. k < 3 ==> not_local_ptr cenv ee.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sm` >> simp[]) >>
  `!x k. not_fresh_at sa x /\ k < 3 ==>
    x <> STRING #"%" (toString (sm.cs_next_var+k))` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> first_x_assum irule >> decide_tac) >>
  `!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (sm.cs_next_var+k))` by
    (rpt strip_tac >>
     qpat_x_assum `!x. vv_operand vv = Var x ==> _` drule >>
     simp[not_fresh_at_def]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func) /\
   MEM (mk_inst (sm.cs_next_id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (sm.cs_next_var+2))]) (fn_insts func)` by
    (conj_tac >> first_x_assum irule >> simp[reason_head_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s /\
   vv_at cenv cx (post_value_type cenv e) sa sm ee tv vv s` by fs[vv_post_def] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gf tnf t /\
   (!vt op0. vv = StackValue vt op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 Gf t) /\
   (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand Gf t) /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
         eval_operand (vv_operand vv) t = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory rt val (w2n w) mem))` by
    (irule (INST_TYPE [alpha |-> ``:256``] reason_head_unwrap_value_resources) >>
     conj_tac >- simp[] >>
     conj_tac >- (qexists_tac `rty` >> simp[]) >>
     qexistsl_tac [`ARB`, `G`, `storage_trace_horizon ee.storage_trace`,
       `M`, `PG`, `ctx`, `func`, `sm.cs_next_id`, `s`, `sa`, `sm`, `tn`, `sm.cs_next_var`] >>
     simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!x k. vv_operand vv = Var x /\ _ ==> _`
       (qspecl_then [`STRING #"%" (toString (k + sm.cs_next_var))`, `k`] mp_tac) >>
     simp[ADD_COMM]) >>
  simp[] >>
  conj_tac >- suspend "family" >>
  conj_tac >- suspend "store" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "frontier" >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- suspend "stack" >>
  conj_tac >- suspend "located" >>
  suspend "kept"
QED

Resume reason_head_unwrap_inputs[store]:
  gvs[exprSimMemDefsTheory.vv_store_bound_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Resume reason_head_unwrap_inputs[pointer]:
  gvs[bodyPtrIfExpAllocSourceTheory.ptr_vv_ok_inst_idx]
QED

Resume reason_head_unwrap_inputs[stack]:
  gvs[bodyPtrIfExpAllocSourceTheory.ptr_buf_ok_inst_idx]
QED

Resume reason_head_unwrap_inputs[located]:
  gvs[bodyPtrIfExpAllocSourceTheory.ptr_buf_ok_inst_idx]
QED

Resume reason_head_unwrap_inputs[history]:
  gvs[]
QED

Resume reason_head_unwrap_inputs[frontier]:
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  pure_rewrite_tac [reason_head_def] >> strip_tac >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  gvs[step_alloca_eq, step_add_eq, step_mstore_eq, AllCaseEqs(),
    update_var_def, mstore_def] >> decide_tac
QED

Resume reason_head_unwrap_inputs[family]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  conj_tac
  >- (irule reason_head_vv_post >>
      conj_tac >- (rpt strip_tac >> gvs[]) >>
      simp[] >>
      qexistsl_tac [`ARB`, `G`, `Gf`, `M`, `PG`, `sm.cs_next_id`, `lo`, `s`, `tn`, `tnf`, `sm.cs_next_var`] >>
      gvs[ADD_COMM] >> metis_tac[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gf tnf t` suffices_by
    (Cases_on `d`
     >- (simp[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.return_buf_ptr_def,
          bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
          ptrDisciplineTheory.allocas_from_def, lookup_var_def] >> metis_tac[]) >>
     PairCases_on `x` >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.return_buf_ptr_def,
       bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
       ptrDisciplineTheory.allocas_from_def, lookup_var_def] >> metis_tac[]) >>
  irule (INST_TYPE [alpha |-> ``:256``] reason_head_ghost_inv_at) >>
  qexistsl_tac [`G`, `H`, `M`, `PG`, `ctx`, `func`, `sm.cs_next_id`, `s`, `tn`, `sm.cs_next_var`] >>
  gvs[ADD_COMM] >> rpt strip_tac >>
  gvs[local_ptrs_reserved_imm_base, not_fresh_at_def] >>
  `not_fresh_at sm (STRING #"%" (toString (k + sm.cs_next_var)))` by
    (irule local_ptrs_reserved_imm_base >> qexists_tac `cenv` >> simp[]) >>
  fs[not_fresh_at_def]
QED

Resume reason_head_unwrap_inputs[kept]:
  `!n b sz. local_region cenv es.scopes s0 n b sz <=>
    local_region cenv ee.scopes s0 n b sz` by
    metis_tac[tupleMemoryFrameTheory.local_region_scopes_domain] >>
  `!G' tn'. ghost_kept_at lo cenv es sa Gi ti s0 G' tn' <=>
    ghost_kept_at lo cenv ee sa Gi ti s0 G' tn'` by
    simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
  `ghost_kept_at lo cenv ee sa Gi ti s0 G tn` by metis_tac[] >>
  `ghost_kept_at lo cenv ee sa Gi ti s0 Gf tnf` suffices_by metis_tac[] >>
  irule (INST_TYPE [alpha |-> ``:256``] reason_head_ghost_kept_at) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`ARB`, `G`, `storage_trace_horizon ee.storage_trace`, `M`, `PG`,
    `ctx`, `cx`, `func`, `sm.cs_next_id`, `s`, `t`, `tn`, `sm.cs_next_var`] >>
  gvs[ADD_COMM, vv_post_def]
QED

Finalise reason_head_unwrap_inputs

