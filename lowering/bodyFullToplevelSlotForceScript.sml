(* Aggregate TopLevelName forcing at one framed joint endpoint. *)
Theory bodyFullToplevelSlotForce
Ancestors
  bodyFullToplevelSlotSingle bodyFullToplevelSlotEntry
  bodyFullToplevelSlotLoopFrame bodyFullToplevelSlotLoopPost
  bodyMemBopRestWordPath fragGasOriginPtr fragGasPathPtr
  exprPtrUnwrapRuntimeFrame exprPtrUnwrapLoopInvariant createSourceCallback
  exprPtrUnwrapEndpointFrames slotCopyExecution venomState valueEncodingDefs valueEncodingProps
  exprPtrUnwrapStorageSource exprSimStorageCopy exprPtrUnwrapStoragePost
  loweringPosts exprLoweringProps bodyPtrDefs vyperInterpreter vyperState
  exprLowering vyperAST context words compileEnv freshWrites copyExecution
  exprPtrUnwrapAllocSemantic exprSimProps exprPtrUnwrapStorage exprPtrUnwrapAllocation

Theorem toplevel_slot_loop_path_history:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  alloca_history func z /\ alloca_inv z
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_path_ptr_erase >> strip_tac >>
  drule rest_word_path_alloca >> simp[]
QED

Theorem toplevel_slot_loop_common_run:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,sa) /\
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ n < 2**256 /\ 32*n <= nb /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 mid buf u z Gf tnf lab.
    compile_alloc_buffer nb sa = (buf,mid) /\ op = Var root /\ buf.buf_operand = Var root /\
    compile_slot_to_memory src (Var root) n loc mid = (lab,sb) /\
    fn_has_code sa mid func /\ fn_has_code mid sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    z.vs_current_bb = slot_copy_exit mid /\ z.vs_inst_idx = 0 /\
    slot_copy_inv mid (if loc=LocStorage then SLOAD else TLOAD) a p d n [] n z /\
    slot_copy_ghost_inv mid (if loc=LocStorage then SLOAD else TLOAD) p d root n G0 tn0 n Gf tnf z /\
    slot_copy_runtime_frame mid d n a z /\ allocas_from lo z /\
    slot_copy_external mid src /\ slot_copy_external mid (Var root) /\
    eval_operand src a = SOME p /\ lookup_var root a = SOME d /\
    ptr_covers G0 tn0 root a nb /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `create_memory_snapshot [] s` by simp[create_memory_snapshot_def] >>
  `EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n (n2w (buffer_allocation_base s sa.cs_next_id):bytes32) \/
     w2n (n2w (buffer_allocation_base s sa.cs_next_id):bytes32)+32*n <= off)) []` by simp[] >>
  mp_tac (Q.INST [`regions` |-> `[]`] (SPEC_ALL toplevel_slot_copy_entry_joint)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `slot_copy_runtime_frame sm d 0 a h` by
    metis_tac[slot_copy_runtime_frame_initial] >>
  `?t Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (h,Gh,tnh) [] (OK t,Gf,tnf)) /\
    t.vs_current_bb = slot_copy_exit sm /\ t.vs_inst_idx = 0 /\
    slot_copy_inv sm (if loc=LocStorage then SLOAD else TLOAD) a p d n [] n t /\
    slot_copy_ghost_inv sm (if loc=LocStorage then SLOAD else TLOAD) p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_alloca_next = h.vs_alloca_next /\ slot_copy_runtime_frame sm d n a t` by
    (irule toplevel_slot_copy_joint_finish_framed >>
     simp[SF SFY_ss] >>
     Cases_on `loc=LocStorage` >> gvs[] >>
     (conj_tac >- (qexists `src` >> simp[])) >>
     qexists `0:num` >> simp[]) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `sm`, `buf`, `u`, `t`, `Gf`, `tnf`, `lab`] >>
  simp[] >> rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  disch_then (mp_then Any (qspecl_then [`a`, `G0`, `tn0`, `[]`] mp_tac) gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (a,G0,tn0) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  disch_then (mp_then Any (qspecl_then [`h`, `Gh`, `tnh`, `[]`] mp_tac) gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> gvs[]
QED

Theorem toplevel_slot_loop_copy_projections:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,sa) /\
  slot_copy_inv mid load a p d n [] n z /\
  slot_copy_ghost_inv mid load p d root n G0 tn0 n Gf tnf z /\
  slot_copy_runtime_frame mid d n a z /\
  slot_copy_external mid (Var root) /\ lookup_var root a = SOME d /\
  a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
  a.vs_call_ctx = s.vs_call_ctx /\
  tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm ==>
  (!j. j < n ==> mem_word_at (w2n d+32*j) z.vs_memory = slot_copy_word load s (p+n2w j)) /\
  eval_operand (Var root) z = SOME d /\ ptr_covers Gf tnf root z (32*n) /\
  (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tnf.t_mem ==>
    b IN key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (p+n2w j)) /\
  (!j. j < w2n d \/ w2n d+32*n <= j ==> (j IN tnf.t_mem <=> j IN tn0.t_mem)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!x. slot_copy_external mid (Var x) ==>
    FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
  z.vs_allocas = a.vs_allocas /\ z.vs_alloca_next = a.vs_alloca_next /\
  copy_static z = copy_static a
Proof
  strip_tac >>
  `slot_copy_prefix load a p (w2n d) n z` by fs[slot_copy_inv_def] >>
  fs[slot_copy_inv_def, slot_copy_ghost_inv_def, slot_copy_runtime_frame_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `slot_copy_prefix _ _ _ _ _ _` mp_tac >>
      simp[slot_copy_prefix_def] >> disch_then (qspec_then `j` mp_tac) >>
      simp[] >> strip_tac >>
      `32 <= LENGTH (DROP (w2n d+32*j) z.vs_memory)` by simp[] >>
      simp[mem_word_at_def, listTheory.TAKE_APPEND1] >>
      metis_tac[slot_copy_word_sources])
  >- metis_tac[eval_operand_def] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem toplevel_located_compile_at:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) ==>
  !sb. compile_expr cenv ty (TopLevelName ann nsid) sb = (LocatedValue t p,sb)
Proof
  simp[Once compile_expr_def, expr_type_def] >>
  Cases_on `FLOOKUP cenv.ce_module_vars nsid`
  >- (pairarg_tac >> simp[]) >>
  Cases_on `x` >> simp[Once compile_expr_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `(\(_9,st'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[]
QED

Theorem toplevel_slot_loop_prepared_run:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  local_ptrs_reserved cenv sm /\ fn_has_code sb sc func /\ ~ctx_has_dalloca ctx /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  type_slot_size rty <> 1 /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv (LocatedValue t p) s /\
    ghost_inv_at (DF H) lo ret cenv cx ee G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv (LocatedValue t p) ee G tn s ==>
  ?tr key.
    p.ptr_location = slot_loc tr /\ t = post_value_type cenv (TopLevelName ann nsid) /\
    storage_holds cx tr t tv key ee s /\ eval_operand p.ptr_operand s = SOME key /\
    type_memory_bytes cenv t = 32*type_slot_size rty /\
    type_memory_size rty = 32*type_slot_size rty /\ type_memory_size rty < 2**64 /\
    ?root d a G0 tn0 mid buf u z Gf tnf lab.
    compile_alloc_buffer (32*type_slot_size rty) sb = (buf,mid) /\ op = Var root /\ buf.buf_operand = Var root /\
    compile_slot_to_memory p.ptr_operand (Var root) (type_slot_size rty) p.ptr_location mid = (lab,sc) /\
    fn_has_code sb mid func /\ fn_has_code mid sc func /\
    u = update_var root d (buffer_allocation_fields s sb.cs_next_id (32*type_slot_size rty)) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (32*type_slot_size rty))] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (32*type_slot_size rty))] [root]) u /\
    tn0 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (32*type_slot_size rty))] [root]) s u tn /\
    d = n2w (buffer_allocation_base s sb.cs_next_id) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    z.vs_current_bb = slot_copy_exit mid /\ z.vs_inst_idx = 0 /\
    slot_copy_inv mid (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key d (type_slot_size rty) [] (type_slot_size rty) z /\
    slot_copy_ghost_inv mid (if p.ptr_location=LocStorage then SLOAD else TLOAD) key d root (type_slot_size rty) G0 tn0 (type_slot_size rty) Gf tnf z /\
    slot_copy_runtime_frame mid d (type_slot_size rty) a z /\ allocas_from lo z /\
    slot_copy_external mid p.ptr_operand /\ slot_copy_external mid (Var root) /\
    eval_operand p.ptr_operand a = SOME key /\ lookup_var root a = SOME d /\
    ptr_covers G0 tn0 root a (32*type_slot_size rty) /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\ a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     (TopLevelName ann nsid) es sa sm s0 ee tv (LocatedValue t p) s /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo ret cenv cx ee G tn s` by metis_tac[] >>
  `?tr. p.ptr_location = slot_loc tr` by
    (Cases_on `p.ptr_location = LocTransient` >> metis_tac[slot_loc_def]) >>
  drule_all vv_post_storage_source >> strip_tac >>
  `storage_holds cx tr t tv a ee s` by fs[storage_holds_def, read_result_def, return_def] >>
  `t = ann /\ type_memory_bytes cenv t = 32*type_slot_size rty /\
   type_memory_size rty = 32*type_slot_size rty /\ type_memory_size rty < 2**64` by
    (gvs[post_value_type_def, lowered_value_type_def, expr_type_def] >>
     simp[valueEncodingPropsTheory.type_memory_size_slots]) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location (32*type_slot_size rty)
     (type_slot_size rty) cenv.ce_is_ctor cenv.ce_imm_alloca sb = (op,sc)` by
    (gvs[unwrap_value_def] >> Cases_on `p.ptr_location` >> gvs[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `op_taint tn p.ptr_operand = {}` by
    (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >> simp[ptr_vv_ok_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by fs[vv_post_def] >>
  `compile_expr cenv ty (TopLevelName ann nsid) sb = (LocatedValue t p,sb)` by
    metis_tac[toplevel_located_compile_at] >>
  `32*type_slot_size rty < dimword (:256) /\ type_slot_size rty < 2**256` by
    (fs[dimword_def] >> decide_tac) >>
  qexistsl [`tr`, `a`] >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [alpha |-> ``:256``] toplevel_slot_loop_common_run) >>
  simp[SF SFY_ss] >>
  conj_tac >- metis_tac[] >>
  (Cases_on `tr` >> simp[slot_loc_def]) >>
  qexistsl [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`] >> gvs[slot_loc_def]
QED

Theorem toplevel_slot_loop_copy_full:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  (is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    is_word_type (expr_type (TopLevelName ann nsid))) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  type_slot_size rty <> 1 /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo ret cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
      ghost_inv_at (DF H) lo ret cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
        (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op G' tn' z /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      ptr_buf_ok cenv (TopLevelName ann nsid) op G' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand op z = SOME w ==> type_memory_size rt = 0 \/
        w2n w+type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by fs[vv_operand_def] >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  mp_tac (SPEC_ALL toplevel_slot_loop_prepared_run) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     (TopLevelName ann nsid) es sa sm s0 ee tv (LocatedValue t p) s /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo ret cenv cx ee G tn s` by metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by fs[vv_post_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `32*type_slot_size rty < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  `a = u with vs_inst_idx := LENGTH mid.cs_current_insts` by
    (drule unwrap_alloc_generated_code >> simp[arithmeticTheory.ADD1]) >>
  drule_all toplevel_slot_single_allocation_bounds >> strip_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all toplevel_slot_single_allocation_separation >> strip_tac >>
  drule_all toplevel_slot_loop_copy_projections >> strip_tac >>
  `32*type_slot_size rty <= 32*type_slot_size rty` by simp[] >>
  drule_all unwrap_copy_exterior_frames >> strip_tac >>
  `sb.cs_next_var <= mid.cs_next_var /\ sb.cs_next_id <= mid.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `sb.cs_next_var <= sb.cs_next_var` by simp[] >>
     drule_all (Q.INST [`sa` |-> `sb`, `sm` |-> `sb`] unwrap_copy_old_variable_frames) >>
     simp[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  suspend "endpoint_frames"
QED

Resume toplevel_slot_loop_copy_full[endpoint_frames]:
  markerLib.RESUME_TAC >>
  `alloca_inv s` by fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `alloca_history func z /\ alloca_inv z` by
    (irule toplevel_slot_loop_path_history >> simp[SF SFY_ss] >>
     qexists `{}:num set` >> simp[]) >>
  `z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_call_ctx = s.vs_call_ctx /\ z.vs_requests = s.vs_requests /\ z.vs_immutables = s.vs_immutables` by
    (fs[slot_copy_runtime_frame_def] >>
     qpat_x_assum `copy_static z = copy_static a` (fn th =>
       mp_tac (AP_TERM ``\s. s.vs_requests`` th) >>
       mp_tac (AP_TERM ``\s. s.vs_immutables`` th)) >>
     simp[copy_static_def, NoAsms] >> rpt disch_tac >>
     simp[venomStateTheory.update_var_def,
          bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[]) >>
  `z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
   sb.cs_next_id < sc.cs_next_id` by
    (drule_at (Pat `compile_slot_to_memory _ _ _ _ _ = _`) compile_slot_to_memory_boundary >>
     (impl_tac >- metis_tac[]) >> strip_tac >> fs[] >> decide_tac) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next` by
    fs[slot_copy_runtime_frame_def] >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
    w2n d+32*type_slot_size rty <= b \/ b+len <= w2n d` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name b len` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >> metis_tac[]) >>
  suspend "posts"
QED

Resume toplevel_slot_loop_copy_full[posts]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `t = post_value_type _ _`
    (SUBST_ALL_TAC o REWRITE_RULE [post_value_type_def, lowered_value_type_def, expr_type_def]) >>
  rule_assum_tac (PURE_REWRITE_RULE [post_value_type_def, lowered_value_type_def, expr_type_def]) >>
  ` (if p.ptr_location = LocStorage then SLOAD else TLOAD) =
    (if tr then TLOAD else SLOAD)` by
    (qpat_x_assum `p.ptr_location = slot_loc tr` mp_tac >> Cases_on `tr` >> simp[slot_loc_def]) >>
  pop_assum (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  mp_tac (Q.INST [`t` |-> `ann`, `n` |-> `type_slot_size rty`, `nb` |-> `32*type_slot_size rty`,
                 `k` |-> `LENGTH mid.cs_current_insts`] (SPEC_ALL toplevel_slot_loop_posts)) >>
  (impl_tac >- ((rpt conj_tac >> simp[post_value_type_def, lowered_value_type_def, expr_type_def])
    >- (qpat_x_assum `!j b. _ ==> b IN key_taint _ _` mp_tac >>
        Cases_on `tr` >> simp[])
    >- (qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _` mp_tac >> simp[])
    >- (qpat_x_assum `!j. _ ==> (j IN tnf.t_mem <=> j IN tn.t_mem)` mp_tac >> simp[])
    >- (qpat_x_assum `!id entry. _ ==> FLOOKUP u.vs_allocas _ = _` mp_tac >> simp[venomStateTheory.update_var_def])
    >- (qpat_x_assum `FLOOKUP u.vs_allocas sb.cs_next_id = _` mp_tac >> simp[venomStateTheory.update_var_def, wordsTheory.w2n_n2w])
    >- (qpat_x_assum `s.vs_alloca_next <= a.vs_alloca_next` mp_tac >> simp[venomStateTheory.update_var_def])
    >- (qpat_x_assum `w2n d + _ <= a.vs_alloca_next` mp_tac >> simp[venomStateTheory.update_var_def, wordsTheory.w2n_n2w])
    >- (qpat_x_assum `!name b len. local_region cenv ee.scopes s name b len ==> _` mp_tac >> simp[wordsTheory.w2n_n2w])
    >- (qpat_x_assum `!name b len. local_region cenv ee.scopes z name b len ==> _` mp_tac >> simp[wordsTheory.w2n_n2w])
    >- (qpat_x_assum `!aid off sz. FLOOKUP s.vs_allocas aid = _ /\ aid < sb.cs_next_id ==> _` mp_tac >> simp[wordsTheory.w2n_n2w] >> metis_tac[])
    >- (qpat_x_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _` mp_tac >> simp[wordsTheory.w2n_n2w]) >>
    (qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ aid < sa.cs_next_id ==> _` mp_tac >> simp[wordsTheory.w2n_n2w] >> metis_tac[]))) >>
  strip_tac >> qexistsl [`v`, `z`, `Gf`, `tnf`] >> simp[] >> metis_tac[]
QED

Finalise toplevel_slot_loop_copy_full
