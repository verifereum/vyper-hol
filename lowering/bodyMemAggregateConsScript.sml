(* One child, from its successful endpoint through ADD, unwrap and store. *)
Theory bodyMemAggregateCons
Ancestors
  bodyMemAggregateAdd bodyMemAggregateSide exprSimProps freshWrites
  exprOperandVar exprLoweringProps emitHelperProps ASCIInumbers words
  compileEnv loweringStateRelDefs venomState context fragExec exprSimAggregateChildren
  exprSimHypsDefs loweringPosts bodyMemAggregatePath gasSummary
  bodyMemAggregateContinuation fragGasMode bodyMemAggregateConsContinuation
  bodyMemAggregateStore exprSimMemDefs
  exprSimMemUnwrap valueCopyBytes valueCopy bodyDeclMemoryCore exprSimBufferStore valueEncodingProps

Theorem aggregate_tuple_cons_continuation_mem_cursor:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  vv_post H ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (!n lo k. local_region ce es'.scopes r n lo k ==>
    lo + k <= b+off \/ b+off + type_memory_size tv <= lo) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?v q. (~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        b + asz <= lb \/ lb + lsz <= b) ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p + n <= b \/ b + asz <= p) /\
       (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP q.vs_allocas inst.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
       mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory tv v (b+off) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k.
      FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        lo + sz <= b \/ b + len <= lo) /\
      lo <= a /\ a + k <= lo + sz /\
      (a + k <= b+off \/ b+off + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas aid = SOME (b,asz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`P` |-> `\u. T`] (SPEC_ALL aggregate_cons_from_slice_mem_cursor)) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt strip_tac >> gvs[] >> first_x_assum irule >> metis_tac[]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> strip_tac >>
    drule_at (Pat `compile_store_memory _ _ (Var _) _ _ _ = _`)
      aggregate_unwrap_store_slice_mem_cursor >>
    disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
    disch_then (qspecl_then [`n2w (b+off)`, `tv`, `env`] mp_tac) >>
    `w2n (n2w (b+off):bytes32) = b+off` by
      (`b+off < dimword(:256)` by decide_tac >> simp[w2n_n2w]) >>
    (impl_tac >- (simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n lo k. local_region ce es'.scopes u n lo k ==> _`
            (drule_then mp_tac) >> decide_tac) >>
      first_assum ACCEPT_TAC)) >>
    disch_then (qx_choosel_then [`v'`, `q'`] strip_assume_tac) >>
    qpat_assum `w2n (n2w (b+off):bytes32) = b+off`
      (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
    qexistsl [`v'`, `q'`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >~ [`~expr_has_effect e /\ _ ==> _`]
    >- (strip_tac >> qx_genl_tac [`bb`, `bsz`] >> strip_tac >>
    qpat_x_assum `_ /\ local_ptrs_reserved ce sa /\ _ ==> _` mp_tac >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (qspecl_then [`bb`, `bsz`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >- first_assum ACCEPT_TAC
                  >- decide_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (fn th => conj_tac >- ACCEPT_TAC (CONJUNCT1 th) >>
      qx_genl_tac [`pp`, `nn`] >> strip_tac >>
      mp_tac (Q.SPECL [`pp`, `nn`] (CONJUNCT2 th)) >>
      (impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)) >> gvs[])) >> simp[]
QED

Theorem aggregate_tuple_cons_continuation_mem:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  vv_post H ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (!n lo k. local_region ce es'.scopes r n lo k ==>
    lo + k <= b+off \/ b+off + type_memory_size tv <= lo) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory tv v (b+off) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k.
      FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        lo + sz <= b \/ b + len <= lo) /\
      lo <= a /\ a + k <= lo + sz /\
      (a + k <= b+off \/ b+off + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas aid = SOME (b,asz)
Proof
  disch_tac >> mp_tac aggregate_tuple_cons_continuation_mem_cursor >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> qpat_x_assum `~expr_has_effect e /\ _ ==> _` kall_tac >>
  qexistsl_tac [`v`, `q`] >> fs[] >> first_assum ACCEPT_TAC
QED

(* The source read keeps its expression type; only the destination slice is
   measured at the declared member type. *)
Theorem aggregate_tuple_compatible_cons_continuation_mem_cursor:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty (lowered_value_type ce e) su = ((),sb) /\
  (dty = expr_type e \/ is_bytestring_type dty /\ is_bytestring_type (expr_type e)) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (!v. read_result cx tvv (es' with gas_obs := []) =
       (INL v,es' with gas_obs := []) ==> value_has_type dtv v /\ val_wf dtv v) /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  vv_post H ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size dtv <= asz /\ b + asz < dimword (:256) /\
  (!n lo k. local_region ce es'.scopes r n lo k ==>
    lo + k <= b+off \/ b+off + type_memory_size dtv <= lo) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size dtv)) ==>
  ?v q. (~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        b + asz <= lb \/ lb + lsz <= b) ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p + n <= b \/ b + asz <= p) /\
       (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP q.vs_allocas inst.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
       mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory dtv v (b+off) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k.
      FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        lo + sz <= b \/ b + len <= lo) /\
      lo <= a /\ a + k <= lo + sz /\
      (a + k <= b+off \/ b+off + type_memory_size dtv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas aid = SOME (b,asz)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `dty = expr_type e`
  >- (qpat_x_assum `dty = expr_type e` SUBST_ALL_TAC >>
      irule aggregate_tuple_cons_continuation_mem_cursor >>
      fs[] >> metis_tac[]) >>
  `is_bytestring_type dty /\ is_bytestring_type (expr_type e)` by metis_tac[] >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
              ci_mono_unwrap_value, ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `eval_operand (Var x) r = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_at (Pat `emit_op _ _ _ = _`) aggregate_tuple_add_marked_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `n2w b` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "read"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[read]:
  rename1 `gas_marked_path T ctx func r 0 (OK tadd)` >>
  `post_value_type ce e = expr_type e` by
    metis_tac[exprSimHypsTheory.post_value_type_no_calls,
              loweringPostsTheory.post_value_type_lowered] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sm` >> fs[ci_mono_def] >>
     drule (cj 1 compiler_compile_var) >> simp[]) >>
  `sa.cs_next_id <= sn.cs_next_id` by
    (fs[ci_mono_def, cs_extends_def] >> decide_tac) >>
  `type_memory_size tv < 2 ** 64` by
    (drule_all aggregate_child_memory_size_bound >> simp[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_rebased_marked_read_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ sn _ _ _ _ _`)) >>
  (impl_tac >- (simp[] >> gvs[])) >> strip_tac >>
  suspend "copy"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[copy]:
  `~is_word_type (expr_type e) /\ ~is_word_type dty` by
    metis_tac[is_bytestring_word_type] >>
  `stmt_state_rel H ctx func ce cx es' u /\ expr_val_rel cx (expr_type e) v op u` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `?sw. eval_operand op u = SOME sw /\ val_in_memory tv v (w2n sw) u.vs_memory` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  `value_has_type tv v /\ val_wf tv v` by
    (drule_at (Pat `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`)
       aggregate_child_read_typed_mem >>
     disch_then (qspecl_then [`tv`, `env`, `ce`] mp_tac) >>
     simp[] >> strip_tac >> first_x_assum irule >>
     qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `value_has_type dtv v /\ val_wf dtv v` by
    (qpat_x_assum `!v. read_result _ _ _ = _ ==> _` irule >>
     qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `?len. val_store_size tv v = 32 + 32 * word_size len` by
    metis_tac[buffer_typed_bytestring_header] >>
  `w2n sw + val_store_size tv v <= u.vs_alloca_next` by
    (fs[expr_store_bound_def] >>
     qpat_x_assum `!tv'. _` (qspec_then `tv` mp_tac) >> simp[]) >>
  `compile_store_memory ce op dst dty (expr_type e) su = ((),sb)` by
    metis_tac[compile_store_memory_bytestring_src] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    metis_tac[aggregate_child_unwrap_var, ci_mono_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var d) tadd` >>
  `not_fresh_at sn d` by simp[Abbr `d`, not_fresh_at_def, toString_11] >>
  `eval_operand (Var d) u = SOME (n2w (b+off))` by
    (fs[eval_operand_def, word_add_n2w] >>
     metis_tac[expr_post_rebased_lookup]) >>
  `w2n (n2w (b+off) : bytes32) = b+off` by
    (`b+off < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
  `w2n (n2w (b+off) : bytes32) + type_memory_size dtv <= u.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `r.vs_alloca_next` >>
     conj_tac >- (irule aggregate_allocated_slice_capacity >> simp[] >>
       qexistsl_tac [`aid`, `asz`] >> simp[]) >> fs[]) >>
  `compile_store_memory ce op (Var d) (expr_type e) (expr_type e) su = ((),sb) /\
   compile_store_memory ce op (Var d) dty dty su = ((),sb)` by
    fs[compile_store_memory_def] >>
  `!z. Var d = Var z ==> not_fresh_at su z` by
    (simp[] >> irule not_fresh_at_mono >> qexists_tac `sn` >> fs[ci_mono_def]) >>
  `val_store_size tv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `val_store_size tv v <= type_memory_size dtv` by
    metis_tac[val_store_size_le] >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (simp[dimword_def] >> gvs[]) >>
  qpat_assum `compile_store_memory ce op (Var d) (expr_type e) (expr_type e) su = _`
    (mp_then (Pos hd) mp_tac compile_store_memory_run_frame_with_capacity) >>
  disch_then (qspecl_then [`u`, `get_tenv cx`, `tv`, `v`, `sw`,
                            `n2w (b+off)`, `type_memory_size dtv`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `val_in_memory dtv v (w2n sw) u.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `run_inst_seq_mem_ok (emitted_insts su sb) u` by
    (qpat_assum `compile_store_memory ce op (Var d) dty dty su = _`
       (mp_then (Pos hd) mp_tac body_typed_store_memory_mem_ok) >>
     disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     disch_then (qspec_then `n2w (b+off)` mp_tac) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts su sb)` by
    metis_tac[aggregate_store_memory_no_gas] >>
  suspend "lift"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[lift]:
  `alloca_inv u` by
    (irule aggregate_mem_path_alloca_inv >>
     qexistsl_tac [`ctx`, `func`, `0`, `tadd`] >>
     fs[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[aggregate_mem_path_alloca_inv]) >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[fragGasPathMemTheory.gas_path_mem_exec, fragGasPathTheory.gas_path_normal]) >>
  drule_all straight_path_mem >> strip_tac >>
  `val_in_memory dtv v (b+off) t.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  suspend "frames"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[frames]:
  `!z w. not_fresh_at sn z /\ lookup_var z tadd = SOME w ==> lookup_var z u = SOME w` by
    (rpt strip_tac >> drule_all expr_post_rebased_lookup >> simp[]) >>
  `!z w. not_fresh_at sm z /\ lookup_var z r = SOME w ==> lookup_var z u = SOME w` by
    (rpt strip_tac >> `not_fresh_at sn z` by
       (irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
     metis_tac[]) >>
  `!n lo k. local_region ce es'.scopes u n lo k ==>
     local_region ce es'.scopes r n lo k` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sm`, `es'.scopes`, `u`] >> simp[]) >>
  `stmt_state_rel H ctx func ce cx es' t` by
    (irule buffer_store_state_frame >>
     qexistsl_tac [`b+off`, `type_memory_size dtv`, `u`, `su`] >>
     simp[] >> pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
     conj_tac >- (rpt strip_tac >>
       `local_region ce es'.scopes r name b' sz` by metis_tac[] >>
       qpat_x_assum `!n lo k. local_region ce es'.scopes r n lo k ==> _`
         (qspecl_then [`name`, `b'`, `sz`] mp_tac) >> simp[] >> decide_tac) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  suspend "join_frames"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[join_frames]:
  `!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP u.vs_allocas i = SOME a` by
    (rpt strip_tac >> fs[expr_post_def] >> metis_tac[]) >>
  `!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
     lookup_var z t = SOME a` by
    (rpt strip_tac >> `not_fresh_at su z` by
       (irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
     metis_tac[]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!i lo sz a k.
      FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==> lo + sz <= b \/ b + len <= lo) /\
      lo <= a /\ a + k <= lo + sz /\
      (a + k <= b+off \/ b+off + type_memory_size dtv <= a) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k r.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     `FLOOKUP tadd.vs_allocas i = SOME (lo,sz)` by fs[] >>
     drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) expr_post_rebased_store_slice >>
     disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     disch_then (qspecl_then [`t`, `type_memory_size dtv`, `k`, `b+off`, `a`] mp_tac) >>
     (impl_tac >- (simp[] >> conj_tac
       >- (rpt strip_tac >>
           `local_region ce es'.scopes r n b' k'` by
             (irule local_region_frame >> conj_tac
              >- (qexists_tac `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
              qexistsl_tac [`sm`, `es'.scopes`, `tadd`] >> simp[]) >> metis_tac[]) >>
       rpt strip_tac >>
       qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
       simp[] >> decide_tac)) >>
     simp[]) >>
  suspend "locals"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[locals]:
  `locals_kept ce es' es' tadd u` by fs[expr_post_def] >>
  `locals_kept ce es' es' tadd t` by
    (irule locals_kept_regions_tail >> qexists_tac `u` >> simp[] >>
     rpt strip_tac >>
     `local_region ce es'.scopes r n b' sz` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `tadd`] >> simp[]) >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     qpat_x_assum `!n lo k. local_region ce es'.scopes r n lo k ==> _` drule >>
     simp[] >> decide_tac) >>
  `locals_kept ce es' es' r t` by
    (irule exprBopSimPropsTheory.locals_kept_trans >>
     qexistsl_tac [`es'`, `sm`, `tadd`] >> simp[locals_kept_mem]) >>
  suspend "pure"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[pure]:
  `~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        b + asz <= lb \/ lb + lsz <= b) ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz t.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p + n <= b \/ b + asz <= p) /\
       (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP t.vs_allocas inst.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (strip_tac >>
     `pure_frame ce func es sa s0 tadd /\
      (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
         lookup_var z tadd = SOME a)` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ tadd` mp_tac >>
        rewrite_tac[vv_post_def] >> strip_tac >> conj_tac
        >- (qpat_x_assum `~expr_has_effect e ==> _` irule >>
            first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
     qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ u`
       (mp_then (Pos hd) mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `pure_frame ce func es sa s0 u` by
       (match_mp_tac exprSimPropsTheory.pure_frame_trans >>
        qexistsl_tac [`es'`, `sa with cs_next_var := sn.cs_next_var`, `tadd`] >>
        simp[] ) >>
     match_mp_tac aggregate_pure_frame_store >>
     qexistsl_tac [`u`, `b+off`, `type_memory_size dtv`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!n lb lsz. local_region ce es.scopes s0 n lb lsz ==> _` drule >>
         decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     fs[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >> decide_tac) >>
  suspend "assemble"
QED

Resume aggregate_tuple_compatible_cons_continuation_mem_cursor[assemble]:
  `stmt_state_rel H ctx func ce cx es' (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[stmt_state_rel_inst_idx] >>
  `gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
     [] (INL v) es' (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >>
     strip_tac >> simp[gas_marked_exec_def, gas_marked_path_def] >>
     conj_tac
     >- (qpat_x_assum `!tail. read_result _ _ _ = _` mp_tac >> simp[gas_explicit_def]) >>
     `gas_path_mem ctx func r 0 (OK u)` by
       (qpat_x_assum `gas_marked_path T ctx func r 0 (OK tadd)` mp_tac >>
        rewrite_tac[gas_marked_path_def] >> strip_tac >>
        drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]) >>
     qpat_x_assum `!ctx. gas_path_mem _ _ u _ _ /\ _` (qspec_then `ctx` strip_assume_tac) >>
     drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]) >>
  qexistsl_tac [`v`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `~expr_has_effect e /\ MAP FDOM _ = _ /\ _ ==> _` mp_tac >>
      qpat_assum `t.vs_allocas = u.vs_allocas` (fn th =>
        simp[NoAsms, th, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  conj_tac
  >- (qpat_x_assum `!z a. not_fresh_at sm z /\ lookup_var z r = _ ==> lookup_var z t = _` mp_tac >>
      simp[lookup_var_def]) >>
  conj_tac
  >- (qpat_x_assum `!i lo sz a k. _ ==> mem_bytes_at a k t.vs_memory = _` mp_tac >>
      simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!z a. not_fresh_at sm z /\ lookup_var z r = _ ==> lookup_var z t = _`
    (qspecl_then [`x`, `n2w b`] mp_tac) >> simp[lookup_var_def]
QED

Finalise aggregate_tuple_compatible_cons_continuation_mem_cursor
