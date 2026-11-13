(* The arm step of a ternary whose arm is an internal call the lowering
   types at the callee's return type, a widening of the ternary's type,
   with a different layout: allocate a buffer of the ternary's type, unwrap
   the arm's value at its lowered type, copy it in with
   compile_store_memory_typed, as one joint path with no GAS site, and give
   the ternary's posts at the arm's end at one horizon H.  Venom steps
   carry no gas; the widening rules out the dynarray ASSERT and the acyclic
   struct metadata the INVALID.  The shared joint unwrap_value, alloc and
   typed-copy lemmas are premises until they land. *)
Theory bodyFullIfExpWidenCall
Ancestors
  vyperStorageFootprint bodySimFull fragGasOriginPtr exprSimIfExp exprSimDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLowering exprLoweringProps fragExec
  emitHelper compileEnv allocaHistory stmtSimDefs vyperAST
  vyperInterpreter vyperState venomState fragGasSeqPtr fragGasEmitCtrl
  instMemFrontier memSafeRun ptrSafeRun ptrDiscipline venomInst
  venomExecSemantics loweringStateRelDefs finite_map typedCopyDomain vyperTypeSystem
  context memoryLayoutSource memoryLayoutDefs typedMemoryCopy robustCopyTransportPtr freshWrites
  exprSimIfExpWidenedPosts valueEncodingProps

Theorem ifexp_widened_call_store_normalize:
  compile_ifexp_arm cenv t sty vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout cenv sty t /\
  type_widens_to tenv sty t ==>
  compile_store_memory cenv src dst t sty =
  compile_store_memory_typed cenv dst t src sty
Proof
  strip_tac >>
  `(!u. punnable cenv u u) /\ (!us. punnable_list cenv us us)` by
    (ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
     simp[punnable_def]) >>
  `sty <> t` by (strip_tac >> gvs[same_memory_layout_def]) >>
  `(!u v. memory_layout_key v = memory_layout_key u ==> punnable cenv v u) /\
   (!us vs. MAP memory_layout_key vs = MAP memory_layout_key us ==>
      punnable_list cenv vs us)` by
    (`(!b u. punnable cenv u (BaseT b)) /\
      (!n u. punnable cenv u (StructT n)) /\
      (!n u. punnable cenv u (FlagT n)) /\
      (!u. punnable cenv u NoneT)` by
       (rpt strip_tac >> Cases_on `u` >> simp[punnable_def]) >>
     ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
     rpt strip_tac >>
     gvs[memory_layout_key_tuple, memory_layout_key_array,
       memory_layout_key_tuple_cases, memory_layout_key_array_cases,
       listTheory.MAP_EQ_CONS, punnable_def] >>
     metis_tac[memory_layout_key_bytes]) >>
  `~tuple_memory_layout_eq t sty` by
    (strip_tac >>
     `type_memory_bytes cenv sty = type_memory_bytes cenv t` by
       metis_tac[tuple_memory_layout_eq_bytes] >>
     `punnable cenv sty t` by
       (Cases_on `t` >> Cases_on `sty` >>
        gvs[tuple_memory_layout_eq_def, punnable_def] >> metis_tac[]) >>
     gvs[same_memory_layout_def]) >>
  Cases_on `is_bytestring_type t`
  >- (drule_all typedMemoryCopyTheory.typed_copy_bytestring_source >>
      strip_tac >>
      rewrite_tac[compile_store_memory_def] >>
      simp[] >>
      once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      simp[]) >>
  simp[compile_store_memory_def]
QED

Theorem ifexp_widened_call_copy_ghost_frame:
  compile_ifexp_arm cenv t sty vv sm = (Var xd,sb) /\
  typed_copy_state_frame k B N s q /\
  (!p. not_fresh_at k p ==> FLOOKUP Gq p = FLOOKUP G p /\
    op_taint tq (Var p) = op_taint tn (Var p)) /\
  tq.t_imm = tn.t_imm /\ tq.t_stor = tn.t_stor /\ tq.t_trans = tn.t_trans /\
  (!i. ~(B <= i /\ i < B+N) ==> (i IN tq.t_mem <=> i IN tn.t_mem)) /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  sa.cs_next_var <= k.cs_next_var /\ local_ptrs_reserved cenv k /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at k x) /\
  lo <= B /\
  (!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= B \/ B+N <= w2n w)) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= B \/ B+N <= off) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    b+sz <= B \/ B+N <= b) /\
  evaluate_type (get_tenv cx) t = SOME rty /\ ~is_word_type t /\
  N = type_memory_size rty /\ type_memory_bytes cenv t = N /\
  lookup_var xd s = SOME w /\ B = w2n w /\ not_fresh_at k xd /\
  FLOOKUP G xd = SOME (B,N) /\ op_taint tn (Var xd) = {} /\
  B+N <= s.vs_alloca_next /\ val_wf rty v /\
  (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==> val_in_memory rty v B mem) ==>
  ghost_inv_at D lo d cenv cx ee Gq tq q /\
  ghost_kept_at lo cenv es sa Gi ti s0 Gq tq /\
  ptr_val_ok cx t v (Var xd) Gq tq q /\
  (!e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' (Var xd) Gq q) /\
  (!rt w'. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand (Var xd) q = SOME w' ==>
    type_memory_size rt = 0 \/ w2n w' + type_memory_size rt <= q.vs_alloca_next)
Proof
  strip_tac >>
  `q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient /\ q.vs_immutables = s.vs_immutables /\
   q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!p. not_fresh_at k p ==> lookup_var p q = lookup_var p s` by
    gvs[typed_copy_state_frame_def] >>
  `!i. ~(B <= i /\ i < B+N) ==>
    mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     first_x_assum irule >> decide_tac) >>
  `!p sz. not_fresh_at k p /\ ptr_covers G tn p s sz ==>
    ptr_covers Gq tq p q sz` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- suspend "inv" >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "value" >>
  conj_tac >- (rpt strip_tac >> simp[ptr_buf_ok_def, eval_operand_def] >> metis_tac[]) >>
  simp[eval_operand_def] >> metis_tac[]
QED

Resume ifexp_widened_call_copy_ghost_frame[inv]:
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def] >>
  conj_tac >- (rpt strip_tac >> `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Resume ifexp_widened_call_copy_ghost_frame[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at k p` by metis_tac[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w'` by metis_tac[] >>
  `val_wf entry.type entry.value /\
   (w2n w' + val_footprint entry.type entry.value <= B \/ B+N <= w2n w')` by metis_tac[] >>
  `!i. w2n w' <= i /\ i < w2n w' + val_footprint entry.type entry.value ==>
    ~(B <= i /\ i < B+N)` by (rpt strip_tac >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`s.vs_memory`, `q.vs_memory`, `tn.t_mem`, `tq.t_mem`, `{i | B <= i /\ i < B+N}`] >>
  simp[] >> metis_tac[]
QED

Resume ifexp_widened_call_copy_ghost_frame[kept]:
  `!x. not_fresh_at sa x ==> not_fresh_at k x` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >>
    `off+sz <= B \/ B+N <= off` by metis_tac[] >>
    `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `b+sz <= B \/ B+N <= b` by metis_tac[] >>
    `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]
QED

Resume ifexp_widened_call_copy_ghost_frame[value]:
  `lookup_var xd q = SOME w /\ FLOOKUP Gq xd = SOME (B,N) /\
    op_taint tq (Var xd) = {}` by metis_tac[] >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
  (conj_tac >- metis_tac[]) >>
  rpt strip_tac >> metis_tac[exprSimPropsTheory.val_store_size_le]
QED

Finalise ifexp_widened_call_copy_ghost_frame

Theorem ifexp_widened_call_copy_semantic_frame:
  compile_ifexp_arm cenv t sty vv sm = (Var xd,sb) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  expr_post H ctx func cenv cx e es sa sc s0 ee v src s /\
  read_result cx tva ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) t = SOME rty /\ ~is_word_type t /\
  value_has_type rty v /\ val_wf rty v /\
  val_in_memory rty v (w2n w) q.vs_memory /\
  lookup_var xd s = SOME w /\ not_fresh_at k xd /\
  sa.cs_next_var <= k.cs_next_var /\ local_ptrs_reserved cenv k /\
  typed_copy_state_frame k (w2n w) (type_memory_size rty) s q /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size rty) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n w + type_memory_size rty <= s.vs_alloca_next /\
  (!n lb len. local_region cenv ee.scopes s n lb len ==>
    w2n w + type_memory_size rty <= lb \/ lb + len <= w2n w) /\
  (!n lb len. local_region cenv es.scopes s0 n lb len ==>
    local_region cenv ee.scopes s n lb len) /\
  (!old off len. FLOOKUP s0.vs_allocas old = SOME (off,len) /\
    old < sa.cs_next_id ==>
    w2n w + type_memory_size rty <= off \/ off + len <= w2n w) ==>
  expr_post H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee v (Var xd) q /\
  vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr (Var xd) LocMemory)) q /\
  expr_store_bound cx t v (Var xd) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `lookup_var xd q = SOME w` by metis_tac[typed_copy_state_frame_def] >>
  `eval_operand (Var xd) q = SOME w` by simp[eval_operand_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
    metis_tac[typed_copy_state_frame_def, freshWritesTheory.not_fresh_at_mono] >>
  `!n lb len. local_region cenv ee.scopes q n lb len <=>
    local_region cenv ee.scopes s n lb len` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame,
              typed_copy_state_frame_def] >>
  `stmt_state_rel H ctx func cenv cx ee q` by
    (irule exprSimCopyTheory.copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`, `inst`, `s`, `k`, `type_memory_size rty`] >>
     gvs[typed_copy_state_frame_def, typed_copy_frame_def, expr_post_def] >>
     gvs[venom_state_component_equality, exprSimStorageCopyTheory.copy_static_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_footprint rty v <= type_memory_size rty` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  conj_tac >- suspend "post" >>
  conj_tac >- suspend "at" >>
  simp[expr_store_bound_def, eval_operand_def] >> rpt strip_tac >> gvs[] >>
  drule exprSimPropsTheory.val_store_size_le >> decide_tac
QED

Resume ifexp_widened_call_copy_semantic_frame[at]:
  markerLib.RESUME_TAC >>
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  disj1_tac >>
  qexistsl_tac [`inst.inst_id`, `w2n w`, `type_memory_size rty`] >>
  simp[] >> metis_tac[]
QED

Resume ifexp_widened_call_copy_semantic_frame[post]:
  markerLib.RESUME_TAC >>
  drule allocated_result_expr_post_frame >> disch_then irule >>
  simp[vyperASTTheory.expr_type_def, expr_val_rel_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`type_memory_size rty`, `w2n w`, `inst`] >>
  simp[] >>
  rpt strip_tac >>
  gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise ifexp_widened_call_copy_semantic_frame

Theorem ifexp_widened_call_alloc_vv_post_frame:
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
  stmt_state_rel H ctx func cenv cx ee u /\
  u.vs_memory = s.vs_memory /\
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region cenv ee.scopes u n b sz <=>
            local_region cenv ee.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post H ctx func cenv cx e es sa sn s0 ee tv vv u
Proof
  strip_tac >>
  qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee u` by
    (irule exprSimVVFrameTheory.vv_holds_vars_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sn ee tv vv u` by
    (Cases_on `vv` >>
     fs[vv_at_def, vv_operand_def, expr_val_at_def] >>
     rpt strip_tac >> gvs[]
     >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
           disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
           metis_tac[]) >>
     metis_tac[]) >>
  `post_value_type cenv e <> expr_type e ==>
    vv_own cenv cx (post_value_type cenv e) sa sn ee tv vv u` by
    (strip_tac >> Cases_on `vv` >>
     fs[vv_own_def, vv_operand_def, expr_val_own_def] >>
     rpt strip_tac >> gvs[]
     >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
           disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
           metis_tac[]) >>
     metis_tac[]) >>
  `locals_kept cenv es ee s0 u` by
    (irule exprSimPropsTheory.locals_kept_mem_tail >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_storage_live H cx vv ee s ==> vv_storage_live H cx vv ee u` by
    (Cases_on `vv` >> fs[vv_operand_def]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 u` by
    (strip_tac >> irule exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `s` >> simp[]) >>
  simp[vv_post_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem ifexp_widened_call_alloc_resources_frame:
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  ~is_word_type t /\ post_value_type cenv e = lowered_value_type cenv e /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!ty op0. vv = StackValue ty op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tv vv s /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  (!v rt. read_result cx tv ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt ==>
    value_has_type rt v) /\
  q.vs_memory = s.vs_memory /\
  contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s /\
  tnq.t_stor = tn.t_stor /\ tnq.t_trans = tn.t_trans /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
    FLOOKUP Gq x = FLOOKUP G x /\ op_taint tnq (Var x) = op_taint tn (Var x)) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  s.vs_alloca_next <= q.vs_alloca_next /\ lo <= s.vs_alloca_next /\
  (!i. i < s.vs_alloca_next ==> (i IN tnq.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gq tnq q /\
  (!ty op0. vv = StackValue ty op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 Gq q) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gq q) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tv vv q /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) q = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tnq.t_mem q.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem))
Proof
  strip_tac >>
  `!rt v p. val_wf rt v /\
    (!i. p <= i /\ i < p + val_footprint rt v ==> i < s.vs_alloca_next) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v p mem) ==>
    !mem. mem_agree_outside tnq.t_mem q.vs_memory mem ==> val_in_memory rt v p mem` by
    (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
     irule robust_val_in_memory_exterior_frame >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`s.vs_memory`, `q.vs_memory`, `tn.t_mem`, `tnq.t_mem`,
       `{i | s.vs_alloca_next <= i}`] >> simp[] >> metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  `op_taint tnq (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov Gq (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> gvs[op_taint_def, op_prov_def]) >>
  conj_tac >- suspend "ptr" >>
  conj_tac >- suspend "stackbuf" >>
  conj_tac >- suspend "locbuf" >>
  conj_tac >- suspend "bound" >>
  suspend "ctor"
QED

Resume ifexp_widened_call_alloc_resources_frame[stackbuf]:
  rpt strip_tac >> gvs[vv_operand_def] >>
  simp[ptr_buf_ok_def] >> rpt strip_tac >>
  Cases_on `op0` >> gvs[ptr_buf_ok_def] >> metis_tac[]
QED

Resume ifexp_widened_call_alloc_resources_frame[locbuf]:
  rpt strip_tac >> gvs[vv_operand_def] >>
  simp[ptr_buf_ok_def] >> rpt strip_tac >>
  Cases_on `p.ptr_operand` >> gvs[ptr_buf_ok_def] >> metis_tac[]
QED

Resume ifexp_widened_call_alloc_resources_frame[bound]:
  Cases_on `vv` >> gvs[vv_store_bound_def, vv_operand_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Resume ifexp_widened_call_alloc_resources_frame[ctor]:
  strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` drule >> simp[] >>
  strip_tac >> qexists_tac `v` >> simp[] >> rpt gen_tac >> strip_tac >>
  `w2n w + type_memory_size rt <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by metis_tac[arithmeticTheory.ADD_COMM] >>
  gvs[] >> gen_tac >> strip_tac >>
  qpat_x_assum `!rt v p. val_wf rt v /\ _ ==> _` irule >>
  `val_wf rt v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  simp[] >> rpt strip_tac >>
  drule exprSimPropsTheory.val_footprint_le >> decide_tac
QED

Resume ifexp_widened_call_alloc_resources_frame[ptr]:
  `!v. read_result cx tv ee = (INL v,ee) /\
    ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) G tn s /\
    (!rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand vv) s = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) ==>
    ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) Gq tnq q` by
    (rpt gen_tac >> strip_tac >> simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
     `val_wf tv' v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv' v (w2n w) mem) /\
      (val_footprint tv' v <> 0 ==> ?x b sz. vv_operand vv = Var x /\
        FLOOKUP G x = SOME (b,sz) /\ b <= w2n w /\
        w2n w + val_store_size tv' v <= b + sz)` by metis_tac[ptr_mem_ok_def] >>
     conj_tac
     >- (gvs[] >> gen_tac >> strip_tac >>
         qpat_x_assum `!rt v p. val_wf rt v /\ _ ==> _` irule >>
         simp[] >> rpt strip_tac >>
         `val_footprint tv' v <= type_memory_size tv'` by metis_tac[exprSimPropsTheory.val_footprint_le] >>
         `type_memory_size tv' = 0 \/ w2n w + type_memory_size tv' <= s.vs_alloca_next` by decide_tac >>
         decide_tac) >>
     strip_tac >> first_x_assum drule >> strip_tac >>
     qexistsl_tac [`x`, `b`, `sz`] >> metis_tac[]) >>
  Cases_on `vv`
  >- suspend "stackptr" >>
  suspend "locptr"
QED

Resume ifexp_widened_call_alloc_resources_frame[stackptr]:
  gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  strip_tac >> first_x_assum irule >> simp[] >>
  gvs[vv_store_bound_def] >> metis_tac[]
QED

Resume ifexp_widened_call_alloc_resources_frame[locptr]:
  gvs[vv_operand_def, ptr_vv_ok_def] >>
  conj_tac >- (strip_tac >> gvs[] >>
    first_x_assum irule >> simp[] >> gvs[vv_store_bound_def] >> metis_tac[]) >>
  gvs[contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def] >> metis_tac[]
QED

Finalise ifexp_widened_call_alloc_resources_frame

Theorem ifexp_widened_call_arm_step_full:
  (* The shared joint unwrap_value lemma on H (r8, family form), here a
     premise until it lands. *)
  (!ty e sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti st0.
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
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
    (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 G s) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G s) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) s = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ?v z G' tn'.
      read_result cx tv ee = (INL v, ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) [] (OK z, G', tn') /\
         expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
         ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       vv_at cenv cx (post_value_type cenv e) sa sc ee tv
         (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
      expr_store_bound cx (expr_type e) v op z /\
      z.vs_current_bb = sc.cs_current_bb /\
      z.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
              eval_operand op z = SOME w ==>
              type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
      (!x. not_fresh_at sb x ==>
           lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
           op_taint tn' (Var x) = op_taint tn (Var x)) /\
      wb_frame cenv ee ee sb s z /\
      ghost_kept_at lo cenv ee sb G tn s G' tn') /\
  (* ifexp_alloca_origin_ptr_edge *)
  (!s ctx lo fn bb id n p u D explicit PG G tn.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [p]) /\
    step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u,
       step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)) /\
  (* compile_alloc_buffer_ghost_frame_at *)
  (!H D lo ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
      stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s /\
      local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
      buf.buf_operand = Var out /\ n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_inv_at D lo d cenv cx es
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u) /\
  (* compile_alloc_buffer_kept_frame_at *)
  (!H lo ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
      vv_post (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx e es sa sb s0 es' tv vv s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      lo <= s.vs_alloca_next /\
      local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      sa.cs_next_var <= sb.cs_next_var /\
      compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
      n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)) /\
  (* compile_store_memory_typed_origin_ptr_path (r3) *)
  (!cenv xd dty xs sty sa sb tenv stv dtv v s sw dw G tn lo ctx func explicit PG.
    compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    ptr_covers G tn xd s (type_memory_size dtv) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
             val_in_memory dtv v (w2n dw) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))) /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
  post_value_type cenv e = lowered_value_type cenv e /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v) /\
  (!v ptv. read_result cx tva ee = (INL v,ee) /\
          evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv e) tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' Gz tf.
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gz tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!ty e sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti st0.
    compile_expr _ _ _ _ = _ /\ _ ==> _` (mk_asm "unwrap") >>
  qpat_x_assum `!s ctx lo fn bb id n p u D explicit PG G tn.
    ~s.vs_halted /\ _ ==> _` (mk_asm "edge") >>
  qpat_x_assum `!H D lo ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
    stmt_state_rel _ _ _ _ _ _ _ /\ _ ==> _` (mk_asm "alloc_inv") >>
  qpat_x_assum `!H lo ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
    vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ ==> _` (mk_asm "alloc_kept") >>
  qpat_x_assum `!cenv xd dty xs sty sa sb tenv stv dtv v s sw dw G tn lo ctx func explicit PG.
    compile_store_memory_typed _ _ _ _ _ _ = _ /\ _ ==> _` (mk_asm "copy") >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e es1 sa sm u ee tva vv z /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G tn z` by
    simp[] >>
  qpat_assum `compile_ifexp_arm _ _ _ _ _ = _` (mk_asm "arm_compile") >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[comp_bind_def, comp_return_def] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[comp_return_def] >>
  strip_tac >>
  rename1 `compile_alloc_buffer _ sm = (buf,sk)` >>
  rename1 `unwrap_value cenv vv sk = (src,sl)` >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  `ci_mono sm sk` by
    (mp_tac (Q.SPECL [`type_memory_bytes cenv t`, `sm`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono sk sl` by
    (mp_tac (Q.SPECL [`cenv`, `vv`, `sk`] ci_mono_unwrap_value) >> simp[]) >>
  `ci_mono sl sb` by
    (mp_tac (Q.SPECL [`cenv`, `src`, `buf.buf_operand`, `t`, `lowered_value_type cenv e`, `sl`]
       ci_mono_compile_store_memory) >> simp[]) >>
  `fn_has_code sm sk func /\ fn_has_code sk sl func /\ fn_has_code sl sb func` by
    (asm_x "unwrap" kall_tac >> asm_x "edge" kall_tac >>
     asm_x "alloc_inv" kall_tac >> asm_x "alloc_kept" kall_tac >> asm_x "copy" kall_tac >>
     fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `compile_store_memory_typed cenv buf.buf_operand t src (lowered_value_type cenv e) sl = ((),sb)` by
    (asm "arm_compile" assume_tac >>
     drule_all ifexp_widened_call_store_normalize >>
     disch_then (qspecl_then [`src`, `buf.buf_operand`] assume_tac) >>
     gvs[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sk` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> gvs[ci_mono_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee z` by
    gvs[vv_post_def] >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl_tac [`sm`, `sk`] >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size rty /\ type_memory_size rty < dimword (:256)` by
    (simp[] >> `type_memory_size rty < 2 ** 64` by simp[] >>
     gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `type_memory_bytes cenv t < dimword (:256)` by simp[] >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sk) z = OK za` >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv t))]
      [STRING #"%" (toString sm.cs_next_var)]) z = OK za` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def] >>
     gvs[AllCaseEqs()]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base ai z = OK za` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee
      (step_prov PG G ai za) (step_taint ai z za tn) za` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee z /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z` by
       (`vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn z` by simp[] >>
        gvs[vv_post_def]) >>
     asm "alloc_inv" mp_tac >> simp[Abbr `ai`] >>
     disch_then drule_all >> simp[]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    gvs[ghost_inv_at_def] >>
  `ghost_kept_at lo cenv es1 sa G1 tn1 u
      (step_prov PG G ai za) (step_taint ai z za tn)` by
    (asm "alloc_kept" mp_tac >> simp[Abbr `ai`] >>
     disch_then drule_all >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >>
     drule_all (CONJUNCT1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `za.vs_labels = z.vs_labels` by
    (drule_all exprSimAllocTheory.hash_alloc_buffer_labels >> simp[]) >>
  `contract_storage za = contract_storage z /\
   contract_transient za = contract_transient z` by
    (drule_all exprSimAllocTheory.alloc_buffer_storage >> simp[]) >>
  `eval_operand (vv_operand vv) za = eval_operand (vv_operand vv) z` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def]) >>
  `!n b sz. local_region cenv ee.scopes za n b sz <=>
             local_region cenv ee.scopes z n b sz` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sm` >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee za` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z` by simp[] >>
     `stmt_state_rel H ctx func cenv cx ee z` by
       (qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms,vv_post_def]) >>
     fs[Abbr `ai`] >>
     drule_all exprSimAllocTheory.literal_alloc_buffer_run >>
     strip_tac >> gvs[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es1 sa sm u ee tva vv za` by
    (rpt strip_tac >>
     irule ifexp_widened_call_alloc_vv_post_frame >>
     simp[] >> qexistsl_tac [`op`, `z`, `sb`, `sm`, `t`] >>
     asm "arm_compile" assume_tac >> simp[ci_mono_def] >>
     rpt strip_tac >> first_x_assum irule >>
     irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `zk = za with vs_inst_idx := SUC z.vs_inst_idx` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es1 sa sm u ee tva vv zk` by
    simp[Abbr `zk`, exprSimVVFrameTheory.vv_post_inst_idx] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee
      (step_prov PG G ai za) (step_taint ai z za tn) zk` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ za`
       (qspec_then `H` mp_tac) >>
     Cases_on `d` >-
       (simp[NoAsms, Abbr `zk`, ghost_inv_at_def, ptr_covers_def,
          return_buf_ptr_def, stor_taint_ok_at_def, allocas_from_def, lookup_var_def] >>
        disch_then irule >> simp[]) >>
     rename1 `SOME dp` >> PairCases_on `dp` >>
     simp[NoAsms, Abbr `zk`, ghost_inv_at_def, ptr_covers_def,
       return_buf_ptr_def, stor_taint_ok_at_def, allocas_from_def, lookup_var_def] >>
     disch_then irule >> simp[]) >>
  `za.vs_memory = z.vs_memory /\
   za.vs_halted = z.vs_halted /\ za.vs_current_bb = z.vs_current_bb /\
   z.vs_alloca_next <= za.vs_alloca_next /\
   (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
      lookup_var x za = lookup_var x z /\
      FLOOKUP (step_prov PG G ai za) x = FLOOKUP G x /\
      op_taint (step_taint ai z za tn) (Var x) = op_taint tn (Var x)) /\
   (step_taint ai z za tn).t_stor = tn.t_stor /\
   (step_taint ai z za tn).t_trans = tn.t_trans /\
   (!i. i < z.vs_alloca_next ==>
      (i IN (step_taint ai z za tn).t_mem <=> i IN tn.t_mem))` by
    (qpat_x_assum `step_inst_base ai z = OK za` mp_tac >>
     qpat_x_assum `Abbrev (ai = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >>
     strip_tac >> simp[] >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def, bind_def,
       return_def] >>
     Cases_on `FLOOKUP z.vs_allocas sm.cs_next_id` >>
     gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
     strip_tac >> gvs[] >>
     simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, written_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, imm_taint_def, adopt_reset_def,
       new_site_bytes_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> eq_tac >> simp[] >> strip_tac >> gvs[] >>
     Cases_on `sm.cs_next_id = aid` >> gvs[finite_mapTheory.FLOOKUP_DEF] >> decide_tac) >>
  `!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var)` by
    (asm_x "unwrap" kall_tac >> asm_x "edge" kall_tac >>
     asm_x "alloc_inv" kall_tac >> asm_x "alloc_kept" kall_tac >> asm_x "copy" kall_tac >>
     simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  asm "arm_compile" assume_tac >>
  mp_tac (Q.INST [`q` |-> `zk`, `Gq` |-> `step_prov PG G ai za`,
    `tnq` |-> `step_taint ai z za tn`]
    (ifexp_widened_call_alloc_resources_frame |> Q.INST [`s` |-> `z`, `tv` |-> `tva`])) >>
  (impl_tac >-
    (asm_x "unwrap" kall_tac >> asm_x "edge" kall_tac >>
     asm_x "alloc_inv" kall_tac >> asm_x "alloc_kept" kall_tac >> asm_x "copy" kall_tac >>
     simp[Abbr `zk`] >>
     (conj_tac >-
       (qpat_x_assum `contract_storage za = _` mp_tac >>
        simp[NoAsms, contract_storage_def, vfmStateTheory.lookup_account_def])) >>
     (conj_tac >-
       (qpat_x_assum `contract_transient za = _` mp_tac >>
        simp[NoAsms, contract_transient_def])) >>
     rpt strip_tac >>
     `x <> STRING #"%" (toString sm.cs_next_var)` by simp[] >>
     qpat_x_assum `!x. x <> STRING _ _ ==> _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `x <> STRING _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[lookup_var_def])) >>
  strip_tac >>
  `~zk.vs_halted /\ zk.vs_current_bb = sk.cs_current_bb /\
   zk.vs_inst_idx = LENGTH sk.cs_current_insts /\
   u.vs_alloca_next <= zk.vs_alloca_next` by
    (simp[Abbr `zk`] >> gvs[ci_mono_def] >> decide_tac) >>
  `ghost_kept_at lo cenv es1 sa G1 tn1 u
     (step_prov PG G ai za) (step_taint ai z za tn)` by simp[] >>
  `sm.cs_next_var <= sk.cs_next_var` by gvs[ci_mono_def] >>
  `type_memory_size ptv < 2 ** 64` by
    (`type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv t` by
       (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[type_widens_to_def] >> strip_tac >>
        `(!sty dty. arg_type_fits sty dty ==> !ce.
             type_memory_bytes ce sty <= type_memory_bytes ce dty) /\
         (!sts dts. arg_types_fit sts dts ==> !ce.
             SUM (MAP (type_memory_bytes ce) sts) <= SUM (MAP (type_memory_bytes ce) dts))` by
          (ho_match_mp_tac arg_type_fits_ind >>
           rpt conj_tac >> rpt gen_tac >>
           simp[arg_type_fits_def, type_memory_bytes_def] >>
           rpt strip_tac >> gvs[ETA_THM] >>
           all_tac >>~- ([`(_ + 31) DIV 32 <= _`],
             irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
           metis_tac[arithmeticTheory.LESS_MONO_MULT2, arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
        gvs[] >> first_x_assum irule >> simp[]) >>
     `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ptv` by
       (qpat_x_assum `evaluate_type _ (post_value_type _ _) = _` mp_tac >> simp[]) >>
     `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ptv` by
       (qpat_x_assum `!ty' tvt. evaluate_type _ _ = _ ==> _` irule >> simp[]) >>
     `type_memory_size rty < 2 ** 64` by simp[] >>
     qpat_x_assum `type_memory_bytes cenv (lowered_value_type cenv e) <= _` mp_tac >>
     simp[] >>
     qpat_x_assum `type_memory_size rty < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
  `alloca_history func zk` by
    (`alloca_inv z` by
       (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ z` mp_tac >>
        simp[NoAsms, stmt_state_rel_def]) >>
     `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb z.vs_inst_idx = SOME ai` by
       (mp_tac (Q.SPECL [`sm`, `sk`, `func`, `[ai]`] fn_has_code_same_block) >>
        simp[Abbr `ai`] >> strip_tac >> qexists_tac `bb` >>
        first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     drule_all allocaHistoryTheory.alloca_history_base_step >>
     simp[Abbr `zk`, Abbr `ai`, mk_inst_def, is_terminator_def]) >>
  asm "unwrap" (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `ptv` mp_tac) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  (impl_tac >- (simp[ci_mono_def] >>
     qpat_x_assum `type_memory_size ptv < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[])) >>
  strip_tac >>
  `~is_word_type (post_value_type cenv e)` by
    (qpat_x_assum `is_word_type (post_value_type _ _) ==> _` mp_tac >> simp[]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (qpat_x_assum `~is_word_type (post_value_type _ _)` mp_tac >> simp[]) >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e es1 sa sl u ee v src z'` by simp[] >>
  `val_wf ptv v /\ ?sw. eval_operand src z' = SOME sw` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, expr_post_def] >> strip_tac >>
     qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_val_at_def] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!mem. mem_agree_outside tn'.t_mem z'.vs_memory mem ==>
         val_in_memory ptv v (w2n sw) mem` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ z'` mp_tac >>
     simp[ptr_val_ok_def, ptr_mem_ok_def] >>
     strip_tac >> first_x_assum (qspecl_then [`ptv`, `sw`] mp_tac) >>
     simp[]) >>
  `stv = ptv` by
    (qpat_x_assum `evaluate_type _ (post_value_type _ _) = _` mp_tac >> simp[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ptv` by
    (qpat_x_assum `!ty' tvt. evaluate_type _ _ = _ ==> _`
      (qspecl_then [`lowered_value_type cenv e`, `ptv`] mp_tac) >> simp[]) >>
  `type_memory_size ptv <> 0 ==>
   ?xs b sz. src = Var xs /\ FLOOKUP G' xs = SOME (b,sz) /\
      b <= w2n sw /\ w2n sw + type_memory_size ptv <= b + sz` by
    (strip_tac >>
     qpat_x_assum `~is_word_type (post_value_type _ _) ==> ptr_buf_ok _ _ _ _ _` mp_tac >>
     simp[ptr_buf_ok_def] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!xs. src = Var xs ==> not_fresh_at sl xs` by
    (`!x. vv_operand vv = Var x ==> not_fresh_at sk x` by
       (rpt strip_tac >> irule not_fresh_at_mono >>
        qexists_tac `sm` >> simp[]) >>
     `case vv of StackValue ty0 op0 => (!x. op0 = Var x ==> not_fresh_at sk x)
       | LocatedValue ty0 p0 => (!x. p0.ptr_operand = Var x ==> not_fresh_at sk x)` by
       (qpat_x_assum `!x. vv_operand vv = Var x ==> not_fresh_at sk x` mp_tac >>
        Cases_on `vv` >> simp[vv_operand_def]) >>
     drule_at (Pos hd) exprOperandVarTheory.compiler_unwrap_value_var >> simp[]) >>
  `p = STRING #"%" (toString sm.cs_next_var)` by
    (qpat_x_assum `buf.buf_operand = Var p` mp_tac >> simp[]) >>
  `lookup_var p z' = SOME w` by
    (`lookup_var p zk = SOME w` by
       (qpat_x_assum `eval_operand buf.buf_operand za = _` mp_tac >>
        qpat_assum `buf.buf_operand = Var p` (fn th => pure_rewrite_tac[th]) >>
        simp[NoAsms, Abbr `zk`, eval_operand_def, lookup_var_def]) >>
     qpat_x_assum `!x. not_fresh_at sk x ==> lookup_var x z' = _ /\ _` (qspec_then `p` mp_tac) >>
     simp[]) >>
  `type_memory_size ptv = 0 \/ w2n sw + type_memory_size ptv <= z'.vs_alloca_next` by
    (qpat_x_assum `~is_word_type (post_value_type _ _) ==> !rt w. _` mp_tac >> simp[]) >>
  `FLOOKUP G' p = SOME (w2n w, type_memory_size rty) /\ op_taint tn' (Var p) = {}` by
    (qpat_x_assum `!x. not_fresh_at sk x ==> lookup_var x z' = _ /\ _` (qspec_then `p` mp_tac) >>
     simp[] >> strip_tac >>
     simp[Abbr `ai`, step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, eval_operand_def, mk_inst_def]) >>
  `w2n w + type_memory_size rty < dimword (:256)` by simp[] >>
  `w2n w + type_memory_size rty <= z'.vs_alloca_next` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee za` by simp[] >>
     `alloca_inv za` by
       (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ za` mp_tac >>
        simp[NoAsms, stmt_state_rel_def]) >>
     qpat_x_assum `alloca_inv za` mp_tac >>
     simp[NoAsms, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> strip_tac >>
     `w2n w + type_memory_bytes cenv t <= za.vs_alloca_next` by
       (first_x_assum irule >> qexists_tac `sm.cs_next_id` >> simp[]) >>
     `zk.vs_alloca_next <= z'.vs_alloca_next` by simp[] >>
     qpat_x_assum `w2n w + type_memory_bytes cenv t <= _` mp_tac >>
     qpat_x_assum `zk.vs_alloca_next <= _` mp_tac >>
     simp[Abbr `zk`] >> decide_tac) >>
  `(!u. punnable cenv u u) /\ (!us. punnable_list cenv us us)` by
    (ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
     simp[punnable_def]) >>
  `lowered_value_type cenv e <> t` by
    (strip_tac >> gvs[same_memory_layout_def]) >>
  `(!sty dty. arg_type_fits sty dty ==>
      !tenv stv. evaluate_type tenv sty = SOME stv /\
        type_memory_size stv = 0 ==> sty = dty) /\
   (!stys dtys. arg_types_fit stys dtys ==>
      !tenv stvs. OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
        type_memory_size_list stvs = 0 ==> stys = dtys)` by
    (POP_ASSUM_LIST (K all_tac) >>
     ho_match_mp_tac arg_type_fits_ind >>
     rw[arg_type_fits_def] >>
     gvs[vyperValueTheory.evaluate_type_def, vyperValueTheory.evaluate_types_OPT_MMAP,
         listTheory.OPT_MMAP_def, AllCaseEqs(), valueEncodingTheory.type_memory_size_def] >>
     metis_tac[cj 1 valueEncodingPropsTheory.type_memory_size_pos]) >>
  `0 < type_memory_size ptv` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     qpat_x_assum `evaluate_type _ (lowered_value_type _ _) = _` mp_tac >>
     qpat_x_assum `stv = ptv` mp_tac >>
     qpat_x_assum `lowered_value_type cenv e <> t` mp_tac >>
     qpat_x_assum `!sty dty. arg_type_fits sty dty ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[type_widens_to_def] >> metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO]) >-
    (qpat_x_assum `type_memory_size ptv = 0` mp_tac >>
     qpat_x_assum `0 < type_memory_size ptv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `~is_bytestring_type t` by
    (qpat_x_assum `lowered_value_type cenv e <> t` mp_tac >>
     qpat_x_assum `post_value_type cenv e = _` mp_tac >>
     qpat_x_assum `expr_type e = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[post_value_type_bytestring]) >>
  `~is_bytestring_type (lowered_value_type cenv e)` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     qpat_x_assum `~is_bytestring_type t` mp_tac >>
     qpat_x_assum `~is_word_type t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     qid_spec_tac `t` >>
     qspec_tac (`lowered_value_type cenv e`, `sty`) >>
     Cases >> Cases >>
     simp[type_widens_to_def, arg_type_fits_def, is_word_type_def,
          is_bytestring_type_def] >>
     rename1 `arg_type_fits (BaseT x) (BaseT y)` >>
     Cases_on `x` >> Cases_on `y` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
     Cases_on `b` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def,
         vyperValueTheory.compatible_bound_def] >> metis_tac[]) >>
  `val_footprint ptv v = type_memory_size ptv` by
    (qpat_x_assum `evaluate_type _ (lowered_value_type _ _) = _` mp_tac >>
     qpat_x_assum `stv = ptv` mp_tac >>
     qpat_x_assum `~is_bytestring_type (lowered_value_type _ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     qmatch_goalsub_abbrev_tac `evaluate_type tenv sty` >>
     Cases_on `sty` >>
     simp[is_bytestring_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> Cases_on `v` >>
     gvs[val_footprint_def, is_bytestring_type_def]) >>
  `vv_own cenv cx (post_value_type cenv e) sa sm ee tva vv z` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ sm _ _ _ _ z` mp_tac >>
     simp[NoAsms, vv_post_def] >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    (spose_not_then assume_tac >>
     `post_value_type cenv e = expr_type e` by
       (irule post_value_type_not_int_call >> simp[]) >>
     qpat_x_assum `lowered_value_type cenv e <> t` mp_tac >>
     qpat_x_assum `post_value_type cenv e = expr_type e` mp_tac >>
     qpat_x_assum `post_value_type cenv e = lowered_value_type cenv e` mp_tac >>
     qpat_x_assum `expr_type e = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `?xs bs ss. src = Var xs /\ FLOOKUP G' xs = SOME (bs,ss) /\
      bs <= w2n sw /\ w2n sw + type_memory_size ptv <= bs + ss` by
    (qpat_x_assum `type_memory_size ptv <> 0 ==> _` irule >> decide_tac) >>
  `?rt pp. vv = LocatedValue rt pp /\ pp.ptr_location = LocMemory /\
      src = pp.ptr_operand /\ sl = sk` by
    (qpat_x_assum `e = Call _ (IntCall _) _ _` SUBST_ALL_TAC >>
     qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     qpat_x_assum `unwrap_value cenv vv sk = _` mp_tac >>
     qpat_x_assum `src = Var xs` mp_tac >>
     qpat_x_assum `~is_word_type (lowered_value_type cenv _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[lowered_value_type_def] >> strip_tac >>
     simp[Once compile_expr_raw_def, compile_expr_body_def,
          expr_type_def, compile_call_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >>
     rpt (pairarg_tac >> gvs[]) >>
     Cases_on `return_buf` >> gvs[] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     rpt strip_tac >>
     gvs[unwrap_value_def, base_ptr_def, comp_return_def, mk_ptr_def,
         vv_operand_def]) >>
  `vv_own cenv cx (post_value_type cenv e) sa sm ee tva vv za` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ za`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     qpat_x_assum `lowered_value_type cenv e <> t` mp_tac >>
     qpat_x_assum `post_value_type cenv e = lowered_value_type cenv e` mp_tac >>
     qpat_x_assum `expr_type e = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[vv_post_def]) >>
  `eval_operand src za = SOME sw` by
    (`not_fresh_at sk xs` by
       (qpat_x_assum `!xs. src = Var xs ==> not_fresh_at sl xs` mp_tac >>
        qpat_x_assum `src = Var xs` mp_tac >>
        qpat_x_assum `sl = sk` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     qpat_x_assum `!x. not_fresh_at sk x ==> lookup_var x z' = _ /\ _`
       (qspec_then `xs` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `eval_operand src z' = SOME sw` mp_tac >>
     qpat_x_assum `lookup_var xs z' = lookup_var xs zk` mp_tac >>
     qpat_x_assum `src = Var xs` mp_tac >>
     qpat_x_assum `Abbrev (zk = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def, eval_operand_def, lookup_var_def]) >>
  `?aid ab asz. FLOOKUP za.vs_allocas aid = SOME (ab,asz) /\
      aid < sm.cs_next_id /\ ab <= w2n sw /\
      w2n sw + type_memory_size ptv <= ab + asz` by
    (qpat_x_assum `vv_own _ _ _ _ _ _ _ _ za` mp_tac >>
     qpat_x_assum `vv = LocatedValue rt pp` mp_tac >>
     qpat_x_assum `pp.ptr_location = LocMemory` mp_tac >>
     qpat_x_assum `src = pp.ptr_operand` mp_tac >>
     qpat_x_assum `eval_operand src za = SOME sw` mp_tac >>
     qpat_x_assum `read_result cx tva ee = (INL v,ee)` mp_tac >>
     qpat_x_assum `evaluate_type _ (post_value_type _ _) = SOME ptv` mp_tac >>
     qpat_x_assum `val_footprint ptv v = _` mp_tac >>
     qpat_x_assum `0 < type_memory_size ptv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[vv_own_def] >>
     metis_tac[]) >>
  `alloca_inv za` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee za` by simp[] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ za` mp_tac >>
     simp[NoAsms, stmt_state_rel_def]) >>
  SUBGOAL_THEN
    ``w2n (sw:256 word) + type_memory_size ptv <= w2n (w:256 word) \/
      w2n (w:256 word) + type_memory_size rty <= w2n (sw:256 word)`` assume_tac >-
   (`ab + asz <= w2n w \/ w2n w + type_memory_size rty <= ab` by
    (qpat_x_assum `alloca_inv za` mp_tac >>
     qpat_x_assum `FLOOKUP za.vs_allocas aid = SOME (ab,asz)` mp_tac >>
     qpat_x_assum `FLOOKUP za.vs_allocas sm.cs_next_id = _` mp_tac >>
     qpat_x_assum `aid < sm.cs_next_id` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv t = type_memory_size rty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def] >>
     rpt strip_tac >>
     `aid <> sm.cs_next_id` by decide_tac >>
     metis_tac[arithmeticTheory.ADD_COMM]) >> decide_tac) >>
  `value_has_type ptv v /\ value_has_type rty v /\ val_wf rty v` by
    (`value_has_type ptv v /\ value_has_type rty v` by simp[] >>
     simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  `ptr_covers G' tn' xs z' (type_memory_size ptv)` by
    (qpat_x_assum `src = Var xs` mp_tac >>
     qpat_x_assum `eval_operand src z' = SOME sw` mp_tac >>
     qpat_x_assum `FLOOKUP G' xs = SOME (bs,ss)` mp_tac >>
     qpat_x_assum `bs <= w2n sw` mp_tac >>
     qpat_x_assum `w2n sw + type_memory_size ptv <= bs + ss` mp_tac >>
     qpat_x_assum `ptr_val_ok _ _ _ _ _ _ z'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def,
          eval_operand_def] >> rpt strip_tac >> gvs[eval_operand_def]) >>
  `ptr_covers G' tn' p z' (type_memory_size rty)` by
    (qpat_x_assum `FLOOKUP G' p = SOME _` mp_tac >>
     qpat_x_assum `op_taint tn' (Var p) = {}` mp_tac >>
     qpat_x_assum `lookup_var p z' = SOME w` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptr_covers_def]) >>
  `compile_store_memory_typed cenv (Var p) t (Var xs)
      (lowered_value_type cenv e) sl = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed cenv buf.buf_operand _ _ _ _ = _` mp_tac >>
     qpat_x_assum `buf.buf_operand = Var p` mp_tac >>
     qpat_x_assum `src = Var xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `not_fresh_at sl xs` by
    (qpat_x_assum `!xs. src = Var xs ==> _` mp_tac >>
     qpat_x_assum `src = Var xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `allocas_from lo z' /\ lo <= z'.vs_alloca_next` by
    (`ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G' tn' z'` by simp[] >>
     qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ z'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def]) >>
  `~z'.vs_halted` by
    (`gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace), lo, explicit, ctx, func, PG)
        (zk, step_prov PG G ai za, step_taint ai z za tn) [] (OK z', G', tn')` by simp[] >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_path_ptr_ok_not_halted >> simp[]) >>
  `w2n sw + type_memory_size ptv < dimword (:256)` by
    (`alloca_room ctx func z'` by
       (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms, expr_post_def, stmt_state_rel_def]) >>
     qpat_x_assum `alloca_room ctx func z'` mp_tac >>
     qpat_x_assum `w2n sw + type_memory_size ptv <= z'.vs_alloca_next` mp_tac >>
     qpat_x_assum `0 < type_memory_size ptv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[alloca_room_def] >> decide_tac) >>
  asm "copy" (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ p _ _`)) >>
  `lookup_var xs z' = SOME sw` by
    (qpat_x_assum `eval_operand src z' = SOME sw` mp_tac >>
     qpat_x_assum `src = Var xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[eval_operand_def]) >>
  disch_then (drule_at (Pat `lookup_var xs _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var p _ = _`)) >>
  disch_then (drule_at (Pat `value_has_type rty _`)) >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`lo`, `explicit`, `PG`] mp_tac) >>
  (impl_tac >- (simp[eval_operand_def] >> conj_tac >- asm_rewrite_tac[] >>
    qpat_x_assum `compile_alloc_buffer _ sm = (buf,sk)` mp_tac >>
    qpat_x_assum `buf.buf_operand = Var p` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >>
    simp[compile_alloc_buffer_def, fresh_var_def, emit_inst_def, emit_op_def,
         comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_id_def, emit_def, not_fresh_at_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[])) >>
  strip_tac >>
  `op = Var p` by
    (qpat_x_assum `buf.buf_operand = op` mp_tac >>
     qpat_x_assum `buf.buf_operand = Var p` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (Var p,sb)` by simp[] >>
  `!n lb len. local_region cenv ee.scopes z' n lb len <=>
               local_region cenv ee.scopes za n lb len` by
    (rpt gen_tac >>
     `local_region cenv ee.scopes z' n lb len <=> local_region cenv ee.scopes zk n lb len` by
       (irule exprSimCopyTheory.copy_buffer_local_region_frame >>
        qexists_tac `sk` >> simp[] >> rpt strip_tac >>
        qpat_x_assum `!x. not_fresh_at sk x ==> lookup_var x z' = _ /\ _`
          (qspec_then `x` mp_tac) >> simp[]) >>
     pop_assum mp_tac >> qunabbrev_tac `zk` >>
     POP_ASSUM_LIST (K all_tac) >> simp[local_region_def, lookup_var_def]) >>
  `!n lb len. local_region cenv ee.scopes z' n lb len ==>
      w2n w + type_memory_size rty <= lb \/ lb + len <= w2n w` by
    (qpat_x_assum `!name b len. local_region cenv ee.scopes za name b len ==> _` mp_tac >>
     qpat_x_assum `!n lb len. local_region cenv ee.scopes z' n lb len <=> _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> metis_tac[]) >>
  `!n lb len. local_region cenv es1.scopes u n lb len ==>
      local_region cenv ee.scopes z n lb len` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`u`, `sa`, `es1.scopes`] >> simp[] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z` mp_tac >>
     simp[NoAsms, vv_post_def] >> metis_tac[]) >>
  `!old off len. FLOOKUP u.vs_allocas old = SOME (off,len) /\ old < sa.cs_next_id ==>
      w2n w + type_memory_size rty <= off \/ off + len <= w2n w` by
    (`!old entry. FLOOKUP u.vs_allocas old = SOME entry ==> FLOOKUP z.vs_allocas old = SOME entry` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[vv_post_def]) >>
     qpat_x_assum `!aid b len. aid < sm.cs_next_id /\ FLOOKUP z.vs_allocas aid = _ ==> _` mp_tac >>
     qpat_x_assum `!old entry. FLOOKUP u.vs_allocas old = _ ==> _` mp_tac >>
     qpat_x_assum `sa.cs_next_id <= sm.cs_next_id` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS, arithmeticTheory.ADD_COMM]) >>
  `FLOOKUP z'.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rty)` by
    (qpat_x_assum `wb_frame cenv ee ee sk zk z'` mp_tac >>
     qpat_x_assum `FLOOKUP za.vs_allocas sm.cs_next_id = _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
     qunabbrev_tac `zk` >>
     POP_ASSUM_LIST (K all_tac) >> simp[wb_frame_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v (Var p) t' /\
    vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr (Var p) LocMemory)) t' /\
    expr_store_bound cx t v (Var p) t'` by
    (gen_tac >> disch_tac >>
     `expr_post H ctx func cenv cx e es1 sa sl u ee v src z'` by simp[] >>
     irule ifexp_widened_call_copy_semantic_frame >>
     simp[] >>
     conj_tac >- (qexistsl_tac [`sm`, `lowered_value_type cenv e`, `vv`] >> simp[]) >>
     qexistsl_tac [`e`, `ai`, `sl`, `z'`, `sl`, `src`, `w`] >>
     asm_x "unwrap" kall_tac >> asm_x "edge" kall_tac >>
     asm_x "alloc_inv" kall_tac >> asm_x "alloc_kept" kall_tac >> asm_x "copy" kall_tac >>
     simp[Abbr `ai`, mk_inst_def] >>
     qpat_assum `p = STRING _ _` (SUBST1_TAC o SYM) >>
     conj_tac >- asm_rewrite_tac[] >>
     conj_tac >- (qpat_x_assum `ci_mono sk sl` mp_tac >>
       qpat_x_assum `ci_mono sl sb` mp_tac >>
       qpat_x_assum `sm.cs_next_id < sk.cs_next_id` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >> decide_tac) >>
     conj_tac >- (qpat_x_assum `!name b len. local_region cenv ee.scopes za name b len ==> _` mp_tac >>
       qpat_x_assum `!n b sz. local_region cenv ee.scopes za n b sz <=> _` mp_tac >>
       qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >>
       metis_tac[arithmeticTheory.ADD_COMM]) >>
     conj_tac >- (qpat_x_assum `!old off len. FLOOKUP u.vs_allocas old = _ /\ old < sa.cs_next_id ==> _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee Gf tnf t' /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gf tnf /\
    ptr_val_ok cx t v (Var p) Gf tnf t' /\
    (!e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' (Var p) Gf t') /\
    (!rt w'. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand (Var p) t' = SOME w' ==>
      type_memory_size rt = 0 \/ w2n w' + type_memory_size rt <= t'.vs_alloca_next)` by
    (gen_tac >> disch_tac >> irule ifexp_widened_call_copy_ghost_frame >>
     simp[] >>
     conj_tac >- (qexistsl_tac [`sb`, `sm`, `lowered_value_type cenv e`, `vv`] >> simp[]) >>
     qexistsl_tac [`G'`, `sl`, `z'`, `tn'`, `w`] >>
     asm_x "unwrap" kall_tac >> asm_x "edge" kall_tac >>
     asm_x "alloc_inv" kall_tac >> asm_x "alloc_kept" kall_tac >> asm_x "copy" kall_tac >>
     simp[] >> qpat_assum `p = STRING _ _` (SUBST1_TAC o SYM) >>
     conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >>
       qexists_tac `sa` >> simp[] >>
       qpat_x_assum `ci_mono sm sk` mp_tac >> simp[ci_mono_def]) >>
     conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >>
       qexists_tac `sa` >> simp[] >>
       qpat_x_assum `ci_mono sm sk` mp_tac >> simp[ci_mono_def]) >>
     conj_tac >- metis_tac[local_ptrs_reserved_def] >>
     conj_tac >- (qpat_x_assum `!n lb len. local_region cenv es1.scopes u n lb len ==> _` mp_tac >>
       qpat_x_assum `!n b sz. local_region cenv ee.scopes za n b sz <=> _` mp_tac >>
       qpat_x_assum `!name b len. local_region cenv ee.scopes za name b len ==> _` mp_tac >>
       qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     conj_tac >- (rpt gen_tac >> strip_tac >>
       `local_ptrs_rel func cenv ee.scopes z'` by
         (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ z'` mp_tac >>
          simp[NoAsms, expr_post_def, stmt_state_rel_def, state_rel_def]) >>
       `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
         metis_tac[local_ptrs_rel_def] >>
       `val_footprint entry.type entry.value <= sz` by
         metis_tac[exprSimPropsTheory.val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
       `local_region cenv ee.scopes z' name (w2n w'') sz` by
         (pure_rewrite_tac[local_region_def] >> qexistsl_tac [`entry`, `p'`, `w''`] >> asm_rewrite_tac[]) >>
       qpat_x_assum `!n lb len. local_region cenv ee.scopes z' n lb len ==> _` drule >>
       simp[]) >>
     conj_tac >- (qpat_x_assum `!old off len. FLOOKUP u.vs_allocas old = _ /\ old < sa.cs_next_id ==> _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     conj_tac >- (
       `ghost_inv_at (DF H) lo d cenv cx ee G' tn' z'` by simp[] >>
       qpat_x_assum `ghost_inv_at (DF H) lo d cenv cx ee G' tn' z'` mp_tac >>
       qpat_x_assum `FLOOKUP z'.vs_allocas sm.cs_next_id = _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def, allocas_from_def] >> metis_tac[]) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t',Gf,tnf)` by
    (gen_tac >> disch_tac >>
     `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (zk,step_prov PG G ai za,step_taint ai z za tn) [] (OK z',G',tn')` by simp[] >>
     `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (zk,step_prov PG G ai za,step_taint ai z za tn) [] (OK t',Gf,tnf)` by
       (drule gas_origin_ptr_path_append >> simp[]) >>
     `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (z,G,tn) []
       (OK zk,step_prov PG G ai za,step_taint ai z za tn)` by
       (qunabbrev_tac `zk` >> qunabbrev_tac `ai` >>
        asm "edge" irule >> simp[] >>
        qpat_x_assum `fn_has_code sm sk func` mp_tac >>
        qpat_x_assum `sk.cs_current_bb = sm.cs_current_bb` mp_tac >>
        qpat_x_assum `sk.cs_current_insts = _` mp_tac >>
        qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_all fn_has_code_same_block >> simp[]) >>
     qpat_x_assum `gas_origin_ptr_edge _ (z,G,tn) _ _` mp_tac >>
     qpat_x_assum `gas_origin_ptr_path _ (zk,_,_) _ (OK t',_,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_rules, listTheory.APPEND]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ (IfExp _ _ _ _) _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ Gf tnf t' /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`t'`, `Gf`, `tnf`] >> simp[] >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ (IfExp _ _ _ _) _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `t'.vs_allocas = z'.vs_allocas /\ t'.vs_alloca_next = z'.vs_alloca_next` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ z' t'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[typed_copy_state_frame_def] >>
     strip_tac >>
     qpat_x_assum `_ = z'` (SUBST1_TAC o SYM) >> simp[]) >>
  `!ctx fn s n t. gas_path ctx fn s n (OK t) /\
      fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s ==>
      alloca_history fn t /\ alloca_inv t` by
    (POP_ASSUM_LIST (K all_tac) >>
     `!ctx fn s n t. gas_path_edge ctx fn s n (OK t) /\
        fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s ==>
        alloca_history fn t /\ alloca_inv t` by
       (rpt gen_tac >> simp[fragGasPathTheory.gas_path_edge_def] >> strip_tac >>
        gvs[exit_result_def]
        >- (drule_all alloca_history_step >> simp[] >> strip_tac >>
            drule_all venomMemProofsTheory.alloca_inv_step_inst_proof >>
            simp[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def, venomMemDefsTheory.alloca_next_valid_def])
        >- (drule_all alloca_history_step >> simp[] >> strip_tac >>
            drule_all venomMemProofsTheory.alloca_inv_step_inst_proof >> strip_tac >>
            drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> strip_tac >>
            drule venomExecProofsTheory.eval_phis_preserves_current_bb >> strip_tac >>
            conj_tac
            >- (gvs[alloca_history_def] >> rpt strip_tac >>
                gvs[get_instruction_def] >>
                drule venomExecProofsTheory.phi_prefix_length_el_phi >>
                simp[]) >>
            gvs[venomMemDefsTheory.alloca_inv_def,
                venomMemDefsTheory.allocas_non_overlapping_def,
                venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[])
        >- (drule_all alloca_history_step >> simp[] >> strip_tac >>
            drule_all venomMemProofsTheory.alloca_inv_step_inst_proof >> simp[]) >>
        qpat_x_assum `exit_result _` mp_tac >>
        qpat_x_assum `OK t = _` (fn th => rewrite_tac[GSYM th]) >>
        simp[exit_result_def]) >>
     `!ctx fn s n r. gas_path ctx fn s n r ==>
        !t. r = OK t ==> fn_inst_ids_distinct fn /\
          alloca_history fn s /\ alloca_inv s ==>
          alloca_history fn t /\ alloca_inv t` by
       (ho_match_mp_tac fragGasPathTheory.gas_path_ind >>
        rpt strip_tac >> gvs[exit_result_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `alloca_inv z` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ z` mp_tac >>
     simp[NoAsms,stmt_state_rel_def]) >>
  `alloca_history func t'` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (z,G,tn) _ (OK t',Gf,tnf)`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >> strip_tac >>
     drule fragGasPathPtrTheory.gas_path_ptr_erase >> strip_tac >>
     qpat_x_assum `!ctx fn s n t. gas_path _ _ _ _ _ /\ _ ==> _` drule_all >>
     simp[]) >>
  simp[] >>
  qpat_x_assum `t'.vs_alloca_next = z'.vs_alloca_next` mp_tac >>
  qpat_x_assum `u.vs_alloca_next <= z.vs_alloca_next` mp_tac >>
  qpat_x_assum `z.vs_alloca_next <= z'.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]

QED
