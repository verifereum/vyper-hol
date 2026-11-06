(* Head evaluation and zero-mark physical-layout store for tuple loops. *)
Theory exprSimAggregateBodyHead
Ancestors
  exprSimAggregateBodyCounted exprSimAggregateBodySource stmtSimAssignAttr
  exprSimAggregateChildren exprSimSource exprSimHyps exprSimHypsDefs
  exprSimAggregateSource exprLoweringProps loweringPosts compileEnv
  gasSummary gasSummaryCompose gasOutcome fragGasPath fragGasMode fragExec
  vyperInterpreter vyperState venomState emitHelper exprOperandVar freshWrites
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom
  exprBopSimProps exprSimProps tupleMemoryFrame valueEncodingProps
Libs
  monadsyntax

Theorem aggregate_body_tuple_head_path:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e)
    su = ((),st) /\
  expr_body_pre ce cx env e es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) mid (OK r) /\
  vv_post ctx func ce cx e es sa sm s0 (mid with gas_obs := []) tvv vv r /\
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
    gas_marked_path F ctx func r 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = st.cs_current_bb /\
    q.vs_inst_idx = LENGTH st.cs_current_insts /\
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
    locals_kept ce es s0 q
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
Resume aggregate_body_tuple_head_path[store]:
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su st` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn st func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `lookup_var x r = SOME (n2w b)` by fs[vv_post_def] >>
  `eval_operand (Var x) r = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_all buffer_emit_add_vv_marked_path >> strip_tac >>
  `?y. dst = Var y /\ not_fresh_at sn y` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
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
  drule_all unwrap_value_body_rebased_path >> strip_tac >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (Q.INST [`sa` |-> `sa`, `sm` |-> `sn`]
      (SPEC_ALL aggregate_store_body_rebased_slice_path)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`tv`, `asz`,
    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
    `env`, `inst.inst_id`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[arithmeticTheory.ADD_ASSOC])) >>
  strip_tac >>
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
  qexists_tac `q'` >> simp[] >>
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
  conj_tac
  >- (rpt strip_tac >> (
      `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (qpat_x_assum `vv_post _ _ _ _ _ _ _ sn _ _ _ _ q`
           (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
         qpat_x_assum `!aid off sz. _` irule >>
         conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
         qexists_tac `aid` >> simp[]) >>
      `mem_bytes_at p n q'.vs_memory = mem_bytes_at p n q.vs_memory` suffices_by simp[] >>
      qpat_x_assum `!aid off' sz a len. _` irule >>
      conj_tac
      >- (qexistsl_tac [`aid`, `p`, `n`] >> simp[] >>
          conj_tac
          >- (rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
          metis_tac[vv_post_def])
      >- (pure_asm_rewrite_tac[] >> decide_tac))) >>
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
      `mem_bytes_at p n q'.vs_memory = mem_bytes_at p n q.vs_memory` suffices_by simp[] >>
      qpat_x_assum `!aid off' sz a len. _` irule >>
      conj_tac
      >- (qexistsl_tac [`inst.inst_id`, `b`, `asz`] >> simp[] >>
          rpt strip_tac >>
          metis_tac[arithmeticTheory.ADD_COMM]) 
      >- (pure_asm_rewrite_tac[] >> decide_tac))) >>
  irule locals_kept_trans >>
  qexistsl_tac [`mid with gas_obs := []`, `sa`, `q`] >>
  simp[] >> metis_tac[vv_post_def]
QED
Finalise aggregate_body_tuple_head_path
