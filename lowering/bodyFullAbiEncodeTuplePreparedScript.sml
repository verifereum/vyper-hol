(* A fixed successful Args endpoint is allocated and staged once. *)
Theory bodyFullAbiEncodeTuplePrepared
Ancestors
  bodyFullAbiEncodeTupleAlloc bodyFullAbiEncodeTupleZero bodyFullAbiEncodePureFrame[qualified]
  bodyFullPathHistory exprSimAbiEncodeArgsSeparation abiEncodeEndpointMetadata
  valueEncodingTyping abiBuiltinAllocation abiTupleEncodePrepare
  emitHelperProps loweringShapeDefs abiArgsLabelBoundary
  exprLoweringProps loweringStateRelDefs exprSimProps tupleMemoryFrame
  abiEncodeArgsSim abiTupleProps compileEnv loweringPosts wordArgsPtr
  bodyFullAllocaFresh fragGasPathFrameMem abiDecodeStaticProps exprSimStorageCopy exprSimCopy exprSimAlloc
  finite_map words list arithmetic venomState venomInst

Theorem abi_encode_args_tuple_prepared_state_frame:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  abi_args_post H0 ctx func ce cx es origin st s0 ee args ops vs initial /\
  LENGTH tvs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2**64 /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      op_taint tn (EL i ops) = {}) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\ 0 < type_memory_size (EL i tvs) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      ?x w. EL i ops = Var x /\ lookup_var x initial = SOME w /\
        ptr_covers G tn x initial (type_memory_size (EL i tvs)) /\
        w2n w + type_memory_size (EL i tvs) < dimword(:256) /\
        w2n w + type_memory_size (EL i tvs) <= initial.vs_alloca_next /\
        (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
          val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
  alloca_history func initial /\ allocas_from lo initial /\ lo <= initial.vs_alloca_next /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  n = abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) /\
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0
    (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_has_code allocated staged func /\
  fn_inst_ids_distinct func ==>
  ?root bw prepared Gp tnp.
    buf.buf_operand = Var root /\ not_fresh_at staged root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (initial,G,tn) [] (OK prepared,Gp,tnp)) /\
    (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem) /\
    lookup_var root prepared = SOME bw /\ ptr_covers Gp tnp root prepared n /\
    w2n bw + n < dimword(:256) /\ lo <= w2n bw /\
    w2n bw + n <= prepared.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
    prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id n initial).vs_allocas /\
    prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id n initial).vs_alloca_next /\
    alloca_history func prepared /\ allocas_from lo prepared /\
    lo <= prepared.vs_alloca_next /\ initial.vs_alloca_next <= prepared.vs_alloca_next /\
    local_ptrs_rel func ce ee.scopes prepared /\
    (!name z k. local_region ce es.scopes s0 name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!name z k. local_region ce ee.scopes initial name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n bw) n z k) /\
    (!D. ghost_inv_at D lo d ce cx ee G tn initial ==>
      ghost_inv_at D lo d ce cx ee Gp tnp prepared) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 Gp tnp) /\
    tnp.t_stor = tn.t_stor /\ tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at st x) ==>
      eval_operand oldop prepared = eval_operand oldop initial /\
      op_taint tnp oldop = op_taint tn oldop /\ op_prov Gp oldop = op_prov G oldop) /\
    FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (w2n bw,n) /\
    (!aid e. FLOOKUP initial.vs_allocas aid = SOME e ==>
      FLOOKUP prepared.vs_allocas aid = SOME e) /\
    (!z k. regions_disjoint (w2n bw) n z k ==>
      mem_bytes_at z k prepared.vs_memory = mem_bytes_at z k initial.vs_memory) /\
    locals_kept ce ee ee initial prepared /\
    copy_static prepared =
      copy_static (abi_builtin_allocate_state st.cs_next_id n initial) /\
    LENGTH initial.vs_memory <= LENGTH prepared.vs_memory /\
    stmt_state_rel H0 ctx func ce cx ee prepared
Proof
  strip_tac >> drule abi_args_post_lengths >> strip_tac >>
  `n < dimword(:256)` by
    (drule_all abi_encode_endpoint_staging_size >>
     simp[abi_tuple_bytes_def, type_memory_bytes_def, MAP_MAP_o,
       combinTheory.o_DEF, MAP_ZIP, dimword_def]) >>
  `stmt_state_rel H0 ctx func ce cx ee initial` by fs[abi_args_post_def] >>
  `!i. i < LENGTH (MAP (lowered_value_type ce) args) ==>
    val_wf (EL i tvs) (EL i vs) /\
    type_memory_size (EL i tvs) = type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) /\
    type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) < dimword(:256) /\
    (if ~is_word_type (EL i (MAP (lowered_value_type ce) args)) /\
      type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) = 0 then T else
      abi_tuple_input ce (EL i (MAP (lowered_value_type ce) args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      (!x. EL i ops = Var x ==> not_fresh_at st x) /\
      (if is_word_type (EL i (MAP (lowered_value_type ce) args)) then op_taint tn (EL i ops) = {} else
        evaluate_type (get_tenv cx) (EL i (MAP (lowered_value_type ce) args)) = SOME (EL i tvs) /\
        expr_val_at ce cx (EL i (MAP (lowered_value_type ce) args)) origin st ee (EL i vs) (EL i ops) initial /\
        ?x w. EL i ops = Var x /\ lookup_var x initial = SOME w /\
          ptr_covers G tn x initial (type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args))) /\
          w2n w + type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) < dimword(:256) /\
          w2n w + type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) <= initial.vs_alloca_next /\
          (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
            val_in_memory (EL i tvs) (EL i vs) (w2n w) mem)))` by suspend "inputs" >>
  `LENGTH ops = LENGTH (MAP (lowered_value_type ce) args) /\
   LENGTH tvs = LENGTH (MAP (lowered_value_type ce) args) /\
   LENGTH vs = LENGTH (MAP (lowered_value_type ce) args)` by simp[] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:'a``] abi_encode_tuple_allocate_origin) >>
  disch_then (qspecl_then [`explicit`, `d`, `PG`] strip_assume_tac) >>
  suspend "continuation"
QED

Resume abi_encode_args_tuple_prepared_state_frame[inputs]:
  gen_tac >> pure_rewrite_tac [LENGTH_MAP] >> strip_tac >>
  qpat_assum `!i. i < LENGTH args ==> evaluate_type _ _ = _ /\ _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `val_wf (EL i tvs) (EL i vs)` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `type_memory_size (EL i tvs) < dimword(:256)` by
    (fs[dimword_def] >> decide_tac) >>
  `!x. EL i ops = Var x ==> not_fresh_at st x` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce (EL i args)) origin st ee
      (EL i vs) (EL i ops) initial` by
    (drule_all abi_encode_args_value_at >> simp[]) >>
  simp[EL_MAP] >>
  Cases_on `is_word_type (lowered_value_type ce (EL i args))` >> gvs[] >>
  Cases_on `type_memory_size (EL i tvs) = 0` >> gvs[]
QED
Resume abi_encode_args_tuple_prepared_state_frame[continuation]:
  `st.cs_next_var <= allocated.cs_next_var` by
    (qspec_then `n` (qspec_then `st` mp_tac) ci_mono_compile_alloc_buffer >>
     simp[ci_mono_def]) >>
  `!x. not_fresh_at origin x ==> not_fresh_at allocated x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, LESS_EQ_TRANS] >>
  `local_ptrs_reserved ce allocated` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_rel func ce ee.scopes t` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at allocated x` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
      not_fresh_at allocated x` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at allocated x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at allocated x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n bw) n z k` by suspend "oldalloc" >>
  `!name z k. local_region ce es.scopes s0 name z k ==>
      regions_disjoint (w2n bw) n z k` by suspend "oldlocal" >>
  `!name z k. local_region ce ee.scopes s0 name z k ==>
      regions_disjoint (w2n bw) n z k` by suspend "oldscopes" >>
  qpat_x_assum `compile_store_abi_tuple _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  (Q.SUBGOAL_THEN `n = 0 \/ w2n bw + n <= t.vs_alloca_next` assume_tac >- simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by simp[] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:'a``] abi_encode_tuple_staging_zero_safe_with_frame) >>
  disch_then (qspecl_then [`explicit`, `PG`, `d`] mp_tac) >>
  disch_then (qspecl_then [`cx`, `G0`, `tn0`] strip_assume_tac) >>
  suspend "assembly"
QED
Resume abi_encode_args_tuple_prepared_state_frame[oldalloc]:
  fs[abi_args_post_def, wb_frame_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED
Resume abi_encode_args_tuple_prepared_state_frame[oldlocal]:
  rpt strip_tac >>
  `local_region ce ee.scopes initial name z k` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s0`, `origin`, `es.scopes`] >>
     fs[abi_args_post_def, wb_frame_def, locals_kept_def]) >>
  metis_tac[]
QED
Resume abi_encode_args_tuple_prepared_state_frame[oldscopes]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    fs[abi_args_post_def, wb_frame_def, locals_kept_def] >>
  metis_tac[tupleMemoryFrameTheory.local_region_scopes_domain]
QED
Resume abi_encode_args_tuple_prepared_state_frame[assembly]:
  `allocated.cs_next_var <= staged.cs_next_var` by
    (drule (cj 1 abi_tuple_encode_store_shape) >> decide_tac) >>
  `not_fresh_at staged root` by metis_tac[not_fresh_at_mono] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (initial,G,tn) [] (OK t',Gf',tnf')` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (initial,G,tn) _ _`
       (qspec_then `D` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tnf) _ _`
       (qspec_then `D` assume_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  `!z k. regions_disjoint (w2n bw) n z k ==>
    mem_bytes_at z k t'.vs_memory = mem_bytes_at z k initial.vs_memory` by
    suspend "exterior" >>
  `locals_kept ce ee ee initial t'` by
    (irule locals_kept_regions >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func ce cx ee t'` by suspend "state_frame" >>
  `copy_static t = copy_static (abi_builtin_allocate_state st.cs_next_id n initial)` by
    (Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` >>
     qpat_assum `t with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _;
                            vs_inst_idx := _|> = initial` mp_tac >>
     simp[copy_static_def, abi_builtin_allocate_state_def,
          venom_state_component_equality] >>
     strip_tac >> fs[abi_builtin_allocate_state_def]) >>
  `copy_static t' = copy_static (abi_builtin_allocate_state st.cs_next_id n initial) /\
   LENGTH initial.vs_memory <= LENGTH t'.vs_memory` by
    (conj_tac >- asm_rewrite_tac[] >>
     qpat_assum `t.vs_memory = initial.vs_memory`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`root`, `bw`, `t'`, `Gf'`, `tnf'`] >>
  simp[] >> qpat_assum `n = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  simp[IgnAsm `n = _`] >> rpt conj_tac
  >- suspend "history"
  >- suspend "floor"
  >- suspend "entrylocal"
  >- suspend "currentlocal"
  >- suspend "ghost"
  >- suspend "kept"
  >- suspend "variables"
  >- suspend "operands"
  >- ((qpat_assum `FLOOKUP t.vs_allocas st.cs_next_id = _` mp_tac >> simp[] >> (metis_tac[])))
  >- (rpt strip_tac >>
      qpat_assum `t.vs_allocas = _` (fn th => pure_rewrite_tac [GSYM th]) >>
      first_assum irule >> first_assum ACCEPT_TAC)
QED
Resume abi_encode_args_tuple_prepared_state_frame[state_frame]:
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `!x. not_fresh_at allocated x ==> lookup_var x t' = lookup_var x t` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at allocated x ==> lookup_var x t' = _ /\ _`
       drule >> simp[]) >>
  `!off len. off + len <= w2n bw \/ w2n bw + n <= off ==>
     mem_bytes_at off len t'.vs_memory = mem_bytes_at off len t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `t.vs_memory = initial.vs_memory` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `!z k. regions_disjoint (w2n bw) n z k ==> _` irule >>
     simp[regions_disjoint_def, IgnAsm `n = _`] >> decide_tac) >>
  qpat_assum `!name z k. local_region ce ee.scopes t name z k ==>
      loweringStateRelDefs$regions_disjoint (w2n bw) n z k`
    (assume_tac o REWRITE_RULE[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  irule exprSimCopyTheory.copy_buffer_state_rel_frame >>
  qexistsl [`w2n bw`, `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]`, `t`, `allocated`, `n`] >>
  asm_rewrite_tac[] >> simp[mk_inst_def, IgnAsm `n = _`] >>
  qpat_assum `n = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `t.vs_allocas = (abi_builtin_allocate_state st.cs_next_id n initial).vs_allocas`
    (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  first_assum ACCEPT_TAC
QED
Resume abi_encode_args_tuple_prepared_state_frame[exterior]:
  rpt strip_tac >> irule mem_bytes_at_bytewise >> rpt strip_tac >>
  qpat_assum `!i. ~(w2n bw <= i /\ _) ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> fs[regions_disjoint_def] >> decide_tac
QED
Resume abi_encode_args_tuple_prepared_state_frame[history]:
  `alloca_inv initial` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  qpat_assum `!D. gas_origin_ptr_path _ (initial,G,tn) _ (OK t',Gf',tnf')`
    (qspec_then `D` assume_tac) >>
  drule_all body_full_path_alloca_history >> simp[]
QED
Resume abi_encode_args_tuple_prepared_state_frame[floor]:
  pure_rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
  qpat_assum `t'.vs_allocas = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `allocas_from lo t`
    (ACCEPT_TAC o PURE_REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])
QED
Resume abi_encode_args_tuple_prepared_state_frame[entrylocal]:
  metis_tac[]
QED
Resume abi_encode_args_tuple_prepared_state_frame[currentlocal]:
  first_assum ACCEPT_TAC
QED
Resume abi_encode_args_tuple_prepared_state_frame[ghost]:
  metis_tac[]
QED
Resume abi_encode_args_tuple_prepared_state_frame[kept]:
  strip_tac >>
  `wb_frame ce es ee origin s0 initial` by fs[abi_args_post_def] >>
  `alloca_inv initial` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off + sz <= initial.vs_alloca_next` by
    (rpt strip_tac >>
     `FLOOKUP initial.vs_allocas aid = SOME (off,sz)` by fs[wb_frame_def] >>
     metis_tac[allocaSiteResourceTheory.alloca_site_registered_below]) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
    b + sz <= initial.vs_alloca_next` by
    (rpt strip_tac >>
     `local_region ce ee.scopes initial name b sz` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`, `origin`, `es.scopes`] >>
        fs[wb_frame_def, locals_kept_def]) >>
     metis_tac[abi_args_local_region_frontier]) >>
  `!x. not_fresh_at origin x ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    metis_tac[not_fresh_at_mono] >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 Gf tnf` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`, `w2n bw + n`, `initial`, `tn`] >>
     simp[IgnAsm `n = _`] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    fs[wb_frame_def, locals_kept_def] >>
  `!Gx tx. ghost_kept_at lo ce es origin G0 tn0 s0 Gx tx <=>
    ghost_kept_at lo ce ee origin G0 tn0 s0 Gx tx` by
    (rpt gen_tac >>
     `!name b sz. local_region ce es.scopes s0 name b sz <=>
       local_region ce ee.scopes s0 name b sz` by
       metis_tac[local_region_scopes_domain] >>
     asm_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  metis_tac[]
QED
Resume abi_encode_args_tuple_prepared_state_frame[variables]:
  metis_tac[not_fresh_at_mono]
QED
Resume abi_encode_args_tuple_prepared_state_frame[operands]:
  gen_tac >> disch_tac >>
  `!x. oldop = Var x ==> not_fresh_at allocated x` by
    metis_tac[not_fresh_at_mono] >>
  qpat_assum `!oldop. _ ==> eval_operand oldop t' = _ /\ _`
    (qspec_then `oldop` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `t.vs_labels = initial.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (initial,G,tn) _ (OK t,Gf,tnf)`
       (qspec_then `D` mp_tac) >> strip_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     disch_then (mp_tac o MATCH_MP fragGasModeTheory.gas_marked_path_exec) >>
     metis_tac[gas_path_code_labels]) >>
  `eval_operand oldop t = eval_operand oldop initial /\
   op_taint tnf oldop = op_taint tn oldop /\
   op_prov Gf oldop = op_prov G oldop` by
    (Cases_on `oldop` >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
          ptrDisciplineTheory.op_prov_def, IgnAsm `n = _`] >>
     metis_tac[ptrDisciplineTheory.op_taint_def]) >>
  metis_tac[]
QED
Finalise abi_encode_args_tuple_prepared_state_frame

Theorem abi_encode_args_tuple_prepared_frame:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  abi_args_post H0 ctx func ce cx es origin st s0 ee args ops vs initial /\
  LENGTH tvs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2**64 /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      op_taint tn (EL i ops) = {}) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\ 0 < type_memory_size (EL i tvs) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      ?x w. EL i ops = Var x /\ lookup_var x initial = SOME w /\
        ptr_covers G tn x initial (type_memory_size (EL i tvs)) /\
        w2n w + type_memory_size (EL i tvs) < dimword(:256) /\
        w2n w + type_memory_size (EL i tvs) <= initial.vs_alloca_next /\
        (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
          val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
  alloca_history func initial /\ allocas_from lo initial /\ lo <= initial.vs_alloca_next /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  n = abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) /\
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0
    (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_has_code allocated staged func /\
  fn_inst_ids_distinct func ==>
  ?root bw prepared Gp tnp.
    buf.buf_operand = Var root /\ not_fresh_at staged root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (initial,G,tn) [] (OK prepared,Gp,tnp)) /\
    (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem) /\
    lookup_var root prepared = SOME bw /\ ptr_covers Gp tnp root prepared n /\
    w2n bw + n < dimword(:256) /\ lo <= w2n bw /\
    w2n bw + n <= prepared.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
    prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id n initial).vs_allocas /\
    prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id n initial).vs_alloca_next /\
    alloca_history func prepared /\ allocas_from lo prepared /\
    lo <= prepared.vs_alloca_next /\ initial.vs_alloca_next <= prepared.vs_alloca_next /\
    local_ptrs_rel func ce ee.scopes prepared /\
    (!name z k. local_region ce es.scopes s0 name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!name z k. local_region ce ee.scopes initial name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n bw) n z k) /\
    (!D. ghost_inv_at D lo d ce cx ee G tn initial ==>
      ghost_inv_at D lo d ce cx ee Gp tnp prepared) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 Gp tnp) /\
    tnp.t_stor = tn.t_stor /\ tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at st x) ==>
      eval_operand oldop prepared = eval_operand oldop initial /\
      op_taint tnp oldop = op_taint tn oldop /\ op_prov Gp oldop = op_prov G oldop) /\
    FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (w2n bw,n) /\
    (!aid e. FLOOKUP initial.vs_allocas aid = SOME e ==>
      FLOOKUP prepared.vs_allocas aid = SOME e) /\
    (!z k. regions_disjoint (w2n bw) n z k ==>
      mem_bytes_at z k prepared.vs_memory = mem_bytes_at z k initial.vs_memory) /\
    locals_kept ce ee ee initial prepared
Proof
  disch_then (strip_assume_tac o MATCH_MP abi_encode_args_tuple_prepared_state_frame) >>
  qexistsl_tac [`root`, `bw`, `prepared`, `Gp`, `tnp`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_args_tuple_prepared:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  abi_args_post H0 ctx func ce cx es origin st s0 ee args ops vs initial /\
  LENGTH tvs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2**64 /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      op_taint tn (EL i ops) = {}) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\ 0 < type_memory_size (EL i tvs) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      ?x w. EL i ops = Var x /\ lookup_var x initial = SOME w /\
        ptr_covers G tn x initial (type_memory_size (EL i tvs)) /\
        w2n w + type_memory_size (EL i tvs) < dimword(:256) /\
        w2n w + type_memory_size (EL i tvs) <= initial.vs_alloca_next /\
        (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
          val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
  alloca_history func initial /\ allocas_from lo initial /\ lo <= initial.vs_alloca_next /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  n = abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) /\
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0
    (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_has_code allocated staged func /\
  fn_inst_ids_distinct func ==>
  ?root bw prepared Gp tnp.
    buf.buf_operand = Var root /\ not_fresh_at staged root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (initial,G,tn) [] (OK prepared,Gp,tnp)) /\
    (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem) /\
    lookup_var root prepared = SOME bw /\ ptr_covers Gp tnp root prepared n /\
    w2n bw + n < dimword(:256) /\ lo <= w2n bw /\
    w2n bw + n <= prepared.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
    prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id n initial).vs_allocas /\
    prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id n initial).vs_alloca_next /\
    alloca_history func prepared /\ allocas_from lo prepared /\
    lo <= prepared.vs_alloca_next /\ initial.vs_alloca_next <= prepared.vs_alloca_next /\
    local_ptrs_rel func ce ee.scopes prepared /\
    (!name z k. local_region ce es.scopes s0 name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!name z k. local_region ce ee.scopes initial name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n bw) n z k) /\
    (!D. ghost_inv_at D lo d ce cx ee G tn initial ==>
      ghost_inv_at D lo d ce cx ee Gp tnp prepared) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 Gp tnp) /\
    tnp.t_stor = tn.t_stor /\ tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at st x) ==>
      eval_operand oldop prepared = eval_operand oldop initial /\
      op_taint tnp oldop = op_taint tn oldop /\ op_prov Gp oldop = op_prov G oldop)
Proof
  disch_then (strip_assume_tac o MATCH_MP abi_encode_args_tuple_prepared_frame) >>
  qexistsl_tac [`root`, `bw`, `prepared`, `Gp`, `tnp`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
