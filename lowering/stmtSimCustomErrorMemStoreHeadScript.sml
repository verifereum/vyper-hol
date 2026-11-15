(* Memory-checked boundaries for the custom-error argument head. *)
Theory stmtSimCustomErrorMemStoreHead
Ancestors
  stmtSimCustomErrorMemUnwrap stmtSimCustomErrorMemTypedCopy
  exprSimAggregateBodyCounted exprSimAggregateChildren exprSimMemUnwrap
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimProps exprLoweringProps
  loweringPosts compileEnv context gasSummary gasSummaryCompose gasOutcome
  fragExec fragGasMode fragGasPathMem stmtSimAssignAttr
  exprSimUnwrapProps exprSimUnwrap fragGasPath typedMemoryCopy vyperTypeArgFits
  aggregateEvaluatedLayout loweringStateRelDefs exprSimDefs
  vyperInterpreter vyperState venomState freshWrites exprOperandVar
  bodyMemAggregateAdd bodyMemAggregateBounds stmtSimCustomErrorMemStoreSlice
  exprSimAggregateBodyHead exprSimAggregateBodySource exprSimAggregateBodyFrames
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom
  exprBopSimProps tupleMemoryFrame valueEncodingProps emitHelper
  exprSimAggregateSource exprSimSource exprSimAggregateLoops
  bodyMemAggregateContinuation bodyMemAggregateUnwrap bodyMemAggregateSide
  vyperAST vyperTypeCallGraph
Libs
  monadsyntax

Theorem unwrap_value_body_rebased_path_mem:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tv vv r /\
  alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path T ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ r.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule vv_post_rebase >> disch_then assume_tac >>
  `vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
     sm r es' (Value v) vv r` by metis_tac[vv_post_read_result] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e)
     es' (Value v) vv r` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ tv _ _` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ es' _ _ _ _ tv _ _` kall_tac >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >>
      qexists_tac `r` >> simp[gas_marked_path_def, gas_path_mem_rules] >>
      drule expr_post_of_vv_post_stack >> simp[]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- suspend "same" >>
  `p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `is_word_type t ==> t = expr_type e /\
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt` by
    (strip_tac >>
     `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
       gvs[expr_body_pre_def] >>
     drule_all post_value_type_widens >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >> strip_tac >>
     `t = post_value_type ce e` by
       (gvs[vv_post_def, vv_holds_def] >>
        Cases_on `t` >> gvs[is_word_type_def, is_bytestring_type_def] >>
        Cases_on `b` >> gvs[is_word_type_def, is_bytestring_type_def] >>
        Cases_on `b'` >> gvs[is_word_type_def, is_bytestring_type_def]) >>
     `is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
     metis_tac[post_value_type_word]) >>
  mp_tac (GEN_ALL unwrap_memory_marked_read_mem) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  (impl_tac >- simp[]) >>
  strip_tac >> gvs[gas_marked_exec_def, read_result_def, return_def] >>
  qexists_tac `u` >> simp[] >>
  metis_tac[gas_marked_path_def, gas_marked_path_exec, gas_path_normal]
QED

Resume unwrap_value_body_rebased_path_mem[same]:
  mp_tac unwrap_value_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  (impl_tac >- (simp[] >> rpt conj_tac
    >- (gvs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[])
    >- metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
    rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[])) >>
  strip_tac >> qexists_tac `u` >> simp[gas_marked_path_def] >>
  metis_tac[gas_marked_path_def, gas_marked_path_exec, gas_path_normal]
QED

Finalise unwrap_value_body_rebased_path_mem

Theorem custom_error_optional_offset_mem[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (if off = 0 then comp_return (Var x)
   else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  eval_operand (Var x) r = SOME w /\
  fn_has_code sm sn func /\ alloca_history func r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path T ctx func r 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func ce cx e es sa sn s0 es' tvv vv q /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    q.vs_memory = r.vs_memory /\ q.vs_allocas = r.vs_allocas /\
    q.vs_alloca_next = r.vs_alloca_next /\
    (!z. not_fresh_at sm z ==> lookup_var z q = lookup_var z r) /\
    alloca_history func q
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[comp_return_def] >> qexists_tac `r` >>
      simp[gas_marked_path_def, fragGasPathMemTheory.gas_path_mem_rules,
           wordsTheory.WORD_ADD_0]) >>
  gvs[] >> drule_all aggregate_tuple_add_marked_mem >> strip_tac >>
  qexists_tac `q` >> simp[]
QED

Theorem custom_error_store_head_path_mem:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  (if off = 0 then comp_return (Var x)
   else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e)
    su = ((),st) /\
  expr_body_pre ce cx env e es /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) mid (OK r) /\
  vv_post ctx func ce cx e es sa sm s0 (mid with gas_obs := []) tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e)
    (mid with gas_obs := []) tvv vv r /\
  alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  fn_has_code sa st func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  inst.inst_id < sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  off + type_memory_size tv <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v q.
    read_result cx tvv (mid with gas_obs := []) =
      (INL v,mid with gas_obs := []) /\
    expr_sim_inv ce cx env (mid with gas_obs := []) /\
    gas_marked_path T ctx func r 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = st.cs_current_bb /\
    q.vs_inst_idx = LENGTH st.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    val_in_memory tv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx (mid with gas_obs := []) q /\
    (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
      aid < sa.cs_next_id /\
      (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
        p+n <= lo \/ lo+sz <= p) /\
      (p+n <= b+off \/ b+off+type_memory_size tv <= p) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    (!p n. b <= p /\ p+n <= b+asz /\
      (p+n <= b+off \/ b+off+type_memory_size tv <= p) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    locals_kept ce es (mid with gas_obs := []) s0 q /\
    (~expr_has_effect e ==>
      (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
        mem_bytes_at lo sz q.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
      (!p n. (p+n <= b \/ b+asz <= p) /\
        (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
          sa.cs_next_id <= i.inst_id /\
          FLOOKUP q.vs_allocas i.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
        mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory))
Proof
  strip_tac >>
  `?v. read_result cx tvv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := [])` by metis_tac[vv_post_materialises] >>
  `expr_body_pre ce cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
   (do res <- eval_expr cx e; read_result cx res od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v,mid with gas_obs := [])` by
    metis_tac[aggregate_body_marked_read_replay] >>
  `expr_sim_inv ce cx env (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_eval] >>
  `value_has_type tv v /\ val_wf tv v` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     metis_tac[aggregate_materialised_child_typed, aggregate_materialised_child_wf,
               expr_body_pre_gas_obs]) >>
  suspend "store"
QED
Resume custom_error_store_head_path_mem[store]:
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by
    (Cases_on `off = 0` >> gvs[comp_return_def] >>
     metis_tac[ci_mono_refl, ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su st` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn st func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `lookup_var x r = SOME (n2w b)` by fs[vv_post_def] >>
  `eval_operand (Var x) r = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_all custom_error_optional_offset_mem >> strip_tac >>
  rename1 `gas_marked_path T ctx func r 0 (OK q)` >>
  `?y. dst = Var y /\ not_fresh_at sn y` by
    (Cases_on `off = 0`
     >- (gvs[comp_return_def] >> metis_tac[not_fresh_at_mono, ci_mono_def]) >>
     gvs[] >> qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_inst_def, emit_def, comp_return_def,
          not_fresh_at_def] >> strip_tac >>
     gvs[ASCIInumbersTheory.toString_11]) >>
  gvs[] >>
  `local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved, ci_mono_def, arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    metis_tac[cj 1 compiler_compile_var, not_fresh_at_mono, ci_mono_def] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    (drule_at (Pos hd) compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def] >> metis_tac[]) >>
  `sa.cs_next_id <= sn.cs_next_id /\ sn.cs_next_var <= su.cs_next_var /\
    cs_extends sn su /\ cs_extends su st` by
    fs[ci_mono_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) q /\
   FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz)` by fs[vv_post_def] >>
  suspend "bounds"
QED
Resume custom_error_store_head_path_mem[bounds]:
  `lookup_var y q = SOME (n2w (b+off))` by
    fs[eval_operand_def, wordsTheory.word_add_n2w] >>
  `stmt_state_rel ctx func ce cx mid q /\ not_local_ptr ce mid.scopes x` by
    (conj_tac
     >- (fs[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >>
         metis_tac[]) >>
     metis_tac[]) >>
  `!name lo sz. local_region ce mid.scopes q name lo sz ==>
    lo+sz <= b+off \/ b+off+type_memory_size tv <= lo` by
    (rpt strip_tac >> irule exprSimAggregateLoopsTheory.aggregate_alloca_slice_excludes_local >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `immutable_metadata_frame es mid` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     drule eval_expr_immutable_metadata_frame >>
     simp[immutable_metadata_frame_def] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)` by
    (rpt strip_tac >>
     fs[immutable_metadata_frame_def] >>
     qpat_x_assum `!addr. IS_SOME _ <=> IS_SOME _`
       (qspec_then `cx.txn.target` mp_tac) >>
     Cases_on `ALOOKUP es.immutables cx.txn.target` >>
     Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[] >>
     rename1 `ALOOKUP es.immutables cx.txn.target = SOME oldimms` >>
     qpat_x_assum `!addr imms imms' src id. _`
       (drule_all_then (qspecl_then [`ce.ce_module`, `name`] mp_tac)) >>
     Cases_on `FLOOKUP (get_source_immutables ce.ce_module oldimms) name` >>
     simp[] >> rename1 `SOME pair` >> Cases_on `pair` >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `w2n (n2w (b+off):256 word) = b+off` by
    (simp[wordsTheory.w2n_n2w] >>
     `b+off < dimword (:256)` by decide_tac >> simp[]) >>
  `fn_has_code sn su func /\ fn_has_code su st func` by
    metis_tac[fn_has_code_split] >>
  suspend "checked_store"
QED
Resume custom_error_store_head_path_mem[checked_store]:
  `?u. gas_marked_path T ctx func q 0 (OK u) /\
    expr_post ctx func ce cx e (mid with gas_obs := [])
      (sa with cs_next_var := sn.cs_next_var) su q (mid with gas_obs := []) v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    (post_value_type ce e <> expr_type e /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (expr_type e) ==>
     !stv sw. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
       eval_operand op u = SOME sw ==>
       type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= u.vs_alloca_next) /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ q.vs_alloca_next <= u.vs_alloca_next` by
    suspend "unwrap_capacity" >>
  `w2n (n2w (b+off):256 word) + type_memory_size tv <= u.vs_alloca_next` by
    (irule bodyMemAggregateSideTheory.aggregate_allocated_slice_capacity >>
     conj_tac >- fs[expr_post_def, stmt_state_rel_def] >>
     qexistsl_tac [`inst.inst_id`, `asz`] >>
     fs[expr_post_def, stmt_state_rel_def, arithmeticTheory.ADD_COMM]) >>

  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (Q.INST [`sa` |-> `sa`, `sm` |-> `sn`]
      (SPEC_ALL aggregate_store_body_rebased_slice_path_mem)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`tv`, `asz`,
    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
    `env`, `inst.inst_id`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[arithmeticTheory.ADD_ASSOC])) >>
  strip_tac >> rename1 `gas_marked_path T ctx func u 0 (OK stored)` >>
  `r.vs_alloca_next <= stored.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  suspend "frames"
QED
Resume custom_error_store_head_path_mem[frames]:
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule_all aggregate_body_marked_replay >>
     disch_then assume_tac >> drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!name lo sz. local_region ce mid.scopes q name lo sz ==>
      local_region ce es.scopes s0 name lo sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `mid.scopes`, `q`] >> simp[] >>
     fs[vv_post_def]) >>
  qexists_tac `stored` >> simp[] >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_marked_path_then))) >>
      qexists_tac `q` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_marked_path_then))) >>
      qexists_tac `u` >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >>
         fs[ci_mono_def] >> decide_tac) >>
      metis_tac[vv_post_def]) >>
  conj_tac >- metis_tac[vv_post_def] >>
  suspend "memory_frames"
QED
Resume custom_error_store_head_path_mem[memory_frames]:
  conj_tac
  >- (rpt strip_tac >> (
      `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (qpat_x_assum `vv_post _ _ _ _ _ _ _ sn _ _ _ _ q`
           (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
         qpat_x_assum `!aid off sz. _` irule >>
         conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
         qexists_tac `aid` >> simp[]) >>
      `mem_bytes_at p n stored.vs_memory = mem_bytes_at p n q.vs_memory` suffices_by simp[] >>
      qpat_x_assum `!aid off' sz a len. _` irule >>
      conj_tac
      >- (qexistsl_tac [`aid`, `p`, `n`] >> simp[] >>
          conj_tac
          >- (rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
          metis_tac[vv_post_def])
      >- (pure_asm_rewrite_tac[] >> decide_tac))) >>
  suspend "allocated_frame"
QED
Resume custom_error_store_head_path_mem[allocated_frame]:
  conj_tac
  >- (`!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          lo+sz <= b \/ b+asz <= lo` by
        (rpt strip_tac >>
         drule_at (Pat `local_region _ _ _ _ _ _`)
           (Q.INST [`off` |-> `0`, `n` |-> `asz`]
             (SPEC_ALL exprSimAggregateLoopsTheory.aggregate_alloca_slice_excludes_local)) >>
         simp[] >> disch_then irule >> simp[] >>
         metis_tac[expr_body_pre_def]) >>
      `mem_bytes_at b asz q.vs_memory = mem_bytes_at b asz s0.vs_memory` by
        (qpat_x_assum `vv_post _ _ _ _ _ _ _ sn _ _ _ _ q`
           (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
         qpat_x_assum `!aid off sz. _` irule >>
         conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
         qexists_tac `inst.inst_id` >> simp[]) >>
      rpt strip_tac >> (
      `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (drule mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`p-b`, `n`] mp_tac) >>
         `b+(p-b) = p /\ p-b+n <= asz` by decide_tac >> simp[]) >>
      `mem_bytes_at p n stored.vs_memory = mem_bytes_at p n q.vs_memory` suffices_by simp[] >>
      qpat_x_assum `!aid off' sz a len. _` irule >>
      conj_tac
      >- (qexistsl_tac [`inst.inst_id`, `b`, `asz`] >> simp[] >>
          rpt strip_tac >>
          metis_tac[arithmeticTheory.ADD_COMM])
      >- (pure_asm_rewrite_tac[] >> decide_tac))) >>
  conj_tac
  >- (irule locals_kept_trans >>
      qexistsl_tac [`mid with gas_obs := []`, `sa`, `q`] >>
      simp[] >> metis_tac[vv_post_def]) >>
  suspend "pure_frame"
QED
Resume custom_error_store_head_path_mem[pure_frame]:
  strip_tac >>
  `pure_frame ce func es sa s0 q` by fs[vv_post_def] >>
  `pure_frame ce func (mid with gas_obs := [])
     (sa with cs_next_var := sn.cs_next_var) q u` by
    (drule exprSimWordArgsTheory.expr_post_pure_frame >> simp[]) >>
  `!aid a. FLOOKUP q.vs_allocas aid = SOME a ==>
      FLOOKUP u.vs_allocas aid = SOME a` by fs[expr_post_def] >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
      lookup_var z q = SOME w` by fs[vv_post_def] >>
  `pure_frame ce func es sa s0 u` by
    (match_mp_tac pure_frame_trans >>
     qexistsl_tac [`mid with gas_obs := []`,
       `sa with cs_next_var := sn.cs_next_var`, `q`] >>
     simp[]) >>
  match_mp_tac (SRULE [arithmeticTheory.ADD_COMM] aggregate_pure_frame_store) >>
  qexistsl_tac [`u`, `b+off`, `type_memory_size tv`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_local_ptr ce es.scopes x` by fs[expr_body_pre_def] >>
      fs[stmt_state_rel_def, state_rel_def] >>
      drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
      simp[regions_disjoint_def]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume custom_error_store_head_path_mem[unwrap_capacity]:
  drule vv_post_rebase >> disch_then assume_tac >>
  `vv_post ctx func ce cx e (mid with gas_obs := [])
     (sa with cs_next_var := sn.cs_next_var) sn q
     (mid with gas_obs := []) (Value v) vv q` by
    metis_tac[vv_post_read_result] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e)
     (mid with gas_obs := []) (Value v) vv q` by
    (qpat_x_assum `vv_store_bound _ _ _ _ tvv _ q` mp_tac >>
     simp[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce (sa with cs_next_var := sn.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved ce sn` mp_tac >>
     simp[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (`!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64` by
        metis_tac[body_post_type_allocation_bound] >>
      `?u. gas_path_mem ctx func q 0 (OK u) /\
        expr_post ctx func ce cx e (mid with gas_obs := [])
          (sa with cs_next_var := sn.cs_next_var) su q
          (mid with gas_obs := []) v op u /\
        expr_store_bound cx (expr_type e) v op u /\
        u.vs_current_bb = su.cs_current_bb /\
        u.vs_inst_idx = LENGTH su.cs_current_insts /\
        alloca_history func u /\ q.vs_alloca_next <= u.vs_alloca_next` by
        (Cases_on `is_word_type (expr_type e)`
         >- (qspecl_then [`ctx`, `func`, `ce`, `cx`, `e`,
               `mid with gas_obs := []`, `sa with cs_next_var := sn.cs_next_var`,
               `sn`, `su`, `q`, `mid with gas_obs := []`, `v`, `vv`, `op`, `q`]
               mp_tac unwrap_value_path_mem >> simp[]) >>
         qspecl_then [`ctx`, `func`, `ce`, `cx`, `e`,
           `mid with gas_obs := []`, `sa with cs_next_var := sn.cs_next_var`,
           `sn`, `su`, `q`, `mid with gas_obs := []`, `v`, `vv`, `op`, `q`]
           mp_tac aggregate_unwrap_value_path_mem_capacity >> simp[] >>
         metis_tac[]) >>
      qexists_tac `u` >> simp[gas_marked_path_def] >>
      metis_tac[fragGasPathMemTheory.gas_path_mem_exec, gas_path_normal]) >>
  `post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rpt IF_CASES_TAC >> gvs[]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (`expr_sim_inv ce cx env es /\ well_typed_expr env e` by
       fs[expr_body_pre_def] >>
     drule_all post_value_type_widens >>
     fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >>
      qexists_tac `q` >> simp[gas_marked_path_def, gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      fs[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
      metis_tac[]) >>
  rename1 `LocatedValue vt place` >>
  `place.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `vt = post_value_type ce e` by
    fs[vv_post_def, vv_holds_def] >>
  `~is_word_type vt` by metis_tac[] >>
  gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >>
  qexists_tac `q` >> simp[gas_marked_path_def, gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  fs[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
  metis_tac[]
QED
Finalise custom_error_store_head_path_mem
