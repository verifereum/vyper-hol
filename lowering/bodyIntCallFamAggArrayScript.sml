(* Seam 2 joint induction, a family leaf of the agg step: array literals. *)
Theory bodyIntCallFamAggArray
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore exprSimAggregateLayout
  exprSimSource exprSimHyps exprSimHypsDefs exprSimAggregateChildren exprSimAggregateSource
  vyperTypeInvariants stmtSimDeclPath placeMemoryCopyEffect
  compileEnv emitHelper emitHelperProps venomState venomExecSemantics venomMemProps
  valueEncodingProps intCallFrame exprSimProps exprSimAlloc venomInst
  fragGasMode context exprSimAggregateLoops exprSimAggregateEncoding
  exprSimWordArgs gasOutcome gasSummary gasSummaryCompose
  exprLoweringProps fragExec valueEncodingProofs stmtReasonVvMemory
  exprOperandVar bodyIntCallRestoreResults abiStaticAggregateProps

(* Public child typing bridge: no equality between the produced layout and
   the annotation is assumed, including for widened internal-call results. *)
Theorem intcall_array_child_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es /\
  MEM e args /\ expr_sim_inv ce cx env ee ==>
  expr_type e = et /\
  type_widens_to (get_tenv cx) (post_value_type ce e) et /\
  ?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv
Proof
  strip_tac >>
  `expr_body_pre ce cx env e ee` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]) >>
  drule make_array_evaluated_layout >> strip_tac >>
  `expr_type e = et` by fs[listTheory.EVERY_MEM] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  simp[] >> conj_tac
  >- (drule post_value_type_widens >>
      fs[expr_body_pre_def] >> metis_tac[]) >>
  metis_tac[post_type_evaluates]
QED

(* A single header/word write has the same counted effect interface as
   aggregate child copies; it does not allocate or alter any variables. *)
Theorem intcall_mstore_effect:
  emit_void MSTORE [Var p; op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ eval_operand op s = SOME wd ==>
  typed_copy_effect ctx func sa sb s
    (mstore (w2n w) wd s with vs_inst_idx := LENGTH sb.cs_current_insts)
    (w2n w) 32
Proof
  strip_tac >>
  drule_all emit_mstore_marked_path >> disch_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  gvs[typed_copy_effect_def, arithmeticTheory.ADD1,
      mstore_memory_nondecreasing] >>
  conj_tac >- simp[mstore_def, venom_state_component_equality] >>
  conj_tac >- simp[lookup_var_def, mstore_def] >>
  conj_tac >- (rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint]) >>
  simp[mstore_def]
QED

Theorem intcall_owned_mstore_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  emit_void MSTORE [Var p; op] si = ((),sb) /\
  fn_has_code si sb fp.jc_func /\
  lookup_var p s = SOME w /\ eval_operand op s = SOME wd /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sa.cs_next_id <= inst.inst_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_var <= si.cs_next_var /\
  fp.jc_lo <= b /\ b <= w2n w /\ w2n w + 32 <= b+k /\
  (!n a z. local_region ce es.scopes s n a z ==>
     regions_disjoint b k a z) /\
  (!n a z. local_region ce es0.scopes s0 n a z ==>
     regions_disjoint b k a z) ==>
  ?u. intcall_expr_cont fp ce env es0 sa s0 es sb u /\
      typed_copy_effect fp.jc_ctx fp.jc_func si sb s u (w2n w) 32 /\
      u = (mstore (w2n w) wd s with
             vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   ~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\
   s.vs_inst_idx = LENGTH si.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_joint_res_def] >>
  drule_all intcall_mstore_effect >>
  disch_then (qspec_then `fp.jc_ctx` assume_tac) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es
     (mstore (w2n w) wd s)` by
    (irule exprSimAllocTheory.literal_mstore_state_rel >>
     goal_assum (drule_at Any) >> fs[regions_disjoint_def] >> metis_tac[]) >>
  `si.cs_next_var <= sb.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  qexists_tac `mstore (w2n w) wd s with
                 vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  `alloca_inv s` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)
    intcall_owned_store_cont >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem intcall_array_root_alloc:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w inst. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sm u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    MEM inst (fn_insts fp.jc_func) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
    (!name a z. local_region ce es.scopes u name a z ==>
       regions_disjoint (w2n w) sz a z) /\
    (!name a z. local_region ce es.scopes s name a z ==>
       regions_disjoint (w2n w) sz a z) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p)
Proof
  strip_tac >> drule_all intcall_alloc_landing >> strip_tac >>
  drule_all buffer_alloc_code >> disch_tac >>
  `fp.jc_lo <= w2n w` by
    (fs[intcall_expr_cont_def, intcall_joint_res_def, allocas_above_def] >>
     metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
        comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
  qexistsl_tac [`u`, `w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]`] >>
  simp[mk_inst_def] >> rpt strip_tac >>
  qpat_x_assum `!name a z. local_region ce es.scopes u name a z ==> _` irule >>
  fs[intcall_joint_res_def, intcall_expr_cont_def] >>
  metis_tac[local_region_frame_fwd]
QED

(* The actual array prefix: allocation, then the dynamic length header
   when present.  Its root remains fresh relative to the literal entry. *)
Theorem intcall_array_entry:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  (if header then emit_void MSTORE [buf.buf_operand; Lit len] sm = ((),sb)
   else sb = sm) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\ (header ==> 32 <= sz) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w inst. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    MEM inst (fn_insts fp.jc_func) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    (!name a z. local_region ce es.scopes u name a z ==>
       regions_disjoint (w2n w) sz a z) /\
    (!name a z. local_region ce es.scopes s name a z ==>
       regions_disjoint (w2n w) sz a z) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p) /\
    (header ==> mem_word_at (w2n w) u.vs_memory = len)
Proof
  strip_tac >> drule_all intcall_array_root_alloc >> strip_tac >>
  Cases_on `header` >> gvs[]
  >- (`lookup_var p u = SOME w /\ eval_operand (Lit len) u = SOME len` by
        fs[eval_operand_def] >>
      `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
       sa.cs_next_id <= inst.inst_id /\ w2n w + 32 <= w2n w + sz` by simp[] >>
      drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)
        intcall_owned_mstore_landing >>
      disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
      disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
      simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      `gas_marked_path F fp.jc_ctx fp.jc_func s 0
        (OK (mstore (w2n w) len u with
               vs_inst_idx := LENGTH sb.cs_current_insts))` by
        (drule typed_copy_effect_path >>
         metis_tac[gas_marked_path_then, arithmeticTheory.ADD]) >>
      `mem_word_at (w2n w) (mstore (w2n w) len u).vs_memory = len` by
        simp[mstore_mem_word_at_same] >>
      `!name a z. local_region ce es.scopes
          (mstore (w2n w) len u with vs_inst_idx := LENGTH sb.cs_current_insts)
          name a z <=> local_region ce es.scopes u name a z` by
        simp[local_region_def, lookup_var_def, mstore_def] >>
      qexistsl_tac [`mstore (w2n w) len u with
                       vs_inst_idx := LENGTH sb.cs_current_insts`, `w`, `inst`] >>
      simp[not_fresh_at_def] >>
      simp[eval_operand_def, lookup_var_def, mstore_def] >>
      fs[not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* Invert one element without identifying its produced layout with its
   annotation.  compile_store_memory_post_type supplies that boundary. *)
Theorem intcall_array_elems_cons_compile:
  compile_make_array_elems cfn ce (e::es) et sz header buf idx sa = (out,sb) ==>
  ?vv sm dst sn op su st.
    cfn ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w (if header then 32 + idx * sz else idx * sz))]
      sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst et (lowered_value_type ce e) su = ((),st) /\
    compile_make_array_elems cfn ce es et sz header buf (idx+1) st = (out,sb)
Proof
  simp[Once exprLoweringTheory.compile_make_array_elems_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[pairTheory.PAIR]
QED

(* The remaining slice of a literal, with the root owned since s0c. *)
Theorem intcall_array_elems_outcome:
  !args ce env idx header buf sa out sb es fp inst b k bw es0 s0c s0 t dtv et.
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  (!e. MEM e args ==> intcall_expr_producer fp e /\
     supportedExprs$supported_expr fp.jc_tops e /\
     calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
     expr_type e = et) /\
  (!e ee. MEM e args /\ expr_sim_inv ce fp.jc_cx env ee ==>
     expr_body_pre ce fp.jc_cx env e ee /\
     type_widens_to (get_tenv fp.jc_cx) (post_value_type ce e) et /\
     ?stv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME stv) /\
  evaluate_type (get_tenv fp.jc_cx) et = SOME dtv /\
  type_memory_bytes ce et = type_memory_size dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  compile_make_array_elems compile_expr ce args et (type_memory_size dtv)
    header buf idx sa = (out,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_joint_res fp ce env es0 s0c s0 /\
  intcall_expr_cont fp ce env es0 s0c s0 es sa t /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  s0c.cs_next_var <= sa.cs_next_var /\ s0c.cs_next_id <= sa.cs_next_id /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k) /\
  s0c.cs_next_id <= inst.inst_id /\ inst.inst_id < sa.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  eval_operand buf t = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  fp.jc_lo <= b /\ b <= w2n bw /\
  w2n bw + (if header then 32 else 0) +
    (idx + LENGTH args) * type_memory_size dtv <= b+k /\
  b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes t name a n ==> regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==> regions_disjoint b k a n) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,t)
    (\res ee u. ?vs. res = INL vs /\ LENGTH vs = LENGTH args /\
       elems_in_memory vs
         (w2n bw + (if header then 32 else 0) + idx * type_memory_size dtv)
         dtv u.vs_memory /\
       intcall_expr_cont fp ce env es0 s0c s0 ee sb u /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
       eval_operand buf u = SOME bw /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       (!name a n. local_region ce ee.scopes u name a n ==> regions_disjoint b k a n) /\
       (!a n. b <= a /\ a+n <= b+k /\
          (a+n <= w2n bw + (if header then 32 else 0) + idx * type_memory_size dtv \/
           w2n bw + (if header then 32 else 0) +
             (idx + LENGTH args) * type_memory_size dtv <= a) ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory))
    (\res ee r. expr_exit res r)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- suspend "nil"
  >> suspend "cons"
QED

Resume intcall_array_elems_outcome[nil]:
  gvs[exprLoweringTheory.compile_make_array_elems_def, comp_return_def] >>
  irule intcall_gas_transparent_path_outcome >>
  qexistsl_tac [`es`, `OK t`, `INL []`] >>
  simp[eval_exprs_nil, gas_marked_path_def, fragGasPathTheory.gas_path_rules] >>
  gvs[intcall_expr_cont_def, intcall_joint_res_def,
      valueEncodingTheory.val_in_memory_def] >>
  metis_tac[fragGasPathTheory.gas_path_rules]
QED

Resume intcall_array_elems_outcome[cons]:
  rename1 `compile_make_array_elems compile_expr ce (e::args) _ _ _ _ _ _ = _` >>
  drule intcall_array_elems_cons_compile >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_expr_cont_def, intcall_joint_res_def] >>
  `expr_type e = et /\ intcall_expr_producer fp e /\
   supportedExprs$supported_expr fp.jc_tops e /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)` by
    (qpat_x_assum `!e'. MEM e' (e::args) ==> _` (qspec_then `e` mp_tac) >> simp[]) >>
  `expr_body_pre ce fp.jc_cx env e es /\
   type_widens_to (get_tenv fp.jc_cx) (post_value_type ce e) et /\
   ?stv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME stv` by
    (qpat_x_assum `!e' ee. _ ==> _` (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  `ci_mono sa sm /\ ci_mono sn su /\ ci_mono su st` by
    (metis_tac[compile_expr_ci_mono, ci_mono_unwrap_value, ci_mono_compile_store_memory,
               pairTheory.SND]) >>
  `ci_mono sm sn` by
    (metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `EVERY (\e. expr_type e = et) args` by
    (simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.MEM]) >>
  `ci_mono st sb` by
    (`compile_make_tuple compile_expr ce args buf
        ((if header then 32 else 0) + (idx+1) * type_memory_bytes ce et) st = (out,sb)` by
       metis_tac[compile_make_array_elems_as_tuple] >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
   fn_has_code sn su fp.jc_func /\ fn_has_code su st fp.jc_func /\
   fn_has_code st sb fp.jc_func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `compile_store_memory ce op dst et (post_value_type ce e) su = ((),st)` by
    metis_tac[compile_store_memory_post_type] >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_counted_child_store >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (post_value_type _ _) = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ et = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf t = _`)) >>
  (impl_tac >-
    (qpat_x_assum `!ce env idx header buf sa out sb es fp inst b k bw es0 s0c s0 t dtv et. _` kall_tac >>
     simp[] >> reverse (rpt conj_tac) >- metis_tac[] >- metis_tac[] >>
     Cases_on `header` >> fs[listTheory.LENGTH, arithmeticTheory.ADD_CLAUSES,
       arithmeticTheory.MULT_CLAUSES, arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac)) >>
  disch_tac >> suspend "bind_child"
QED

Resume intcall_array_elems_outcome[bind_child]:
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_bind_value >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ marks (INL v) mid (OK u)` >>
  irule aggregate_tuple_values_outcome >>
  qpat_x_assum `!ce env idx header buf sa out sb es fp inst b k bw es0 s0c s0 t dtv et. _`
    (drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ st _`)) >>
  disch_then (drule_at (Pat `FLOOKUP u.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf u = _`)) >>
  (impl_tac >- (simp[] >>
    qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
    qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` kall_tac >>
    conj_tac >- metis_tac[] >>
    `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
      (fs[ci_mono_def] >> decide_tac) >>
    fs[arithmeticTheory.ADD1] >>
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS,
              arithmeticTheory.LESS_LESS_EQ_TRANS])) >>
  disch_then assume_tac >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (Cases >> simp[exprSimDefsTheory.expr_exit_INL]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "cons_post"
QED

Resume intcall_array_elems_outcome[cons_post]:
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `expr_body_pre ce fp.jc_cx env e es` by metis_tac[] >>
  `value_runtime_typed env (expr_type e) v` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     irule memory_rhs_read_annotation_typed >>
     qexistsl [`ce`, `fp.jc_cx`,
       `es with gas_obs := gas_explicit marks t.vs_gas_readings ++ []`,
       `mid with gas_obs := []`] >>
     fs[vyperStateTheory.bind_def, expr_body_pre_gas_obs]) >>
  `env.type_defs = get_tenv fp.jc_cx` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `val_wf dtv v` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  suspend "cons_memory"
QED

Resume intcall_array_elems_outcome[cons_memory]:
  qmatch_goalsub_abbrev_tac `elems_in_memory (v::vs) off dtv _` >>
  `val_in_memory dtv v off r.vs_memory` by
    (irule val_in_memory_mem_agree >> simp[] >>
     qexistsl [`type_memory_size dtv`, `u.vs_memory`] >> simp[] >>
     reverse conj_tac >- (Cases_on `header` >> fs[Abbr `off`]) >>
     qpat_x_assum `!a n. _ ==> mem_bytes_at a n r.vs_memory = _` (qspecl_then [`off`, `type_memory_size dtv`] mp_tac) >>
     (impl_tac >- (Cases_on `header` >> fs[Abbr `off`, arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES] >> decide_tac)) >>
     simp[]) >>
  conj_tac
  >- (simp[valueEncodingTheory.val_in_memory_def] >>
      fs[Abbr `off`, arithmeticTheory.LEFT_ADD_DISTRIB,
         AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `mem_bytes_at a n r.vs_memory = mem_bytes_at a n u.vs_memory` by
    (qpat_x_assum `!a n. _ ==> mem_bytes_at a n r.vs_memory = _` irule >>
     Cases_on `header` >> fs[Abbr `off`, arithmeticTheory.LEFT_ADD_DISTRIB,
        arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory` by
    (qpat_x_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _` irule >>
     Cases_on `header` >> fs[Abbr `off`, arithmeticTheory.LEFT_ADD_DISTRIB,
        arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  simp[]
QED

Finalise intcall_array_elems_outcome

Theorem intcall_array_value_producer:
  (!e. MEM e args ==> intcall_expr_producer fp e) ==>
  intcall_expr_producer fp (Builtin ann (MakeArray (SOME et) bnd) args)
Proof
  strip_tac >> rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  drule make_array_evaluated_layout >> strip_tac >>
  drule compile_array_literal_inv >> strip_tac >>
  suspend "entry"
QED

Resume intcall_array_value_producer[entry]:
  `type_memory_bytes ce ann < 2 ** 64` by
    fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def] >>
  `type_memory_bytes ce ann < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_make_array_cfn,
              compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  qpat_x_assum `compile_make_array _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.compile_make_array_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >>
  pop_assum mp_tac >>
  pure_asm_rewrite_tac [] >> simp[] >> strip_tac >>
  rename1 `compile_make_array_elems _ _ _ _ _ _ _ _ sh = _` >>
  `ci_mono sm sh` by
    (Cases_on `bnd` >> gvs[comp_return_def] >>
     metis_tac[ci_mono_emit_void, pairTheory.SND, ci_mono_refl]) >>
  `ci_mono sh sb` by
    (`compile_make_tuple compile_expr ce args ba.buf_operand
        (if (case bnd of vyperAST$Fixed cap => F | Dynamic cap => T) then 32 else 0) sh = (u,sb)` by
       (qpat_x_assum `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        qpat_x_assum `type_memory_bytes ce et = _` (fn th => pure_rewrite_tac[GSYM th]) >>
        simp[compile_make_array_elems_as_tuple]) >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `fn_has_code sm sh fp.jc_func /\ fn_has_code sh sb fp.jc_func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  drule_at (Pat `intcall_joint_res _ _ _ _ _ _`) intcall_array_entry >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (qspecl_then [`sh`, `n2w (LENGTH args)`,
    `(case bnd of vyperAST$Fixed cap => F | Dynamic cap => T)`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (Cases_on `bnd` >> gvs[comp_return_def]) >>
    Cases_on `bnd` >> gvs[])) >> strip_tac >>
  suspend "loop"
QED

Resume intcall_array_value_producer[loop]:
  drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)
    intcall_array_elems_outcome >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspec_then `w` mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >> conj_tac
        >- (fs[supportedExprsTheory.supported_expr_def,
               supportedExprsTheory.supported_pure_expr_def,
               supportedExprsTheory.supported_effect_expr_def,
               supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM]) >>
        conj_tac
        >- (fs[vyperTypeCallGraphTheory.int_calls_expr_def,
               vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def] >>
            metis_tac[int_calls_exprs_every_mem]) >>
        fs[listTheory.EVERY_MEM]) >>
    conj_tac
    >- (rpt gen_tac >> strip_tac >> conj_tac
        >- (drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]) >>
        drule_all intcall_array_child_layout >> simp[]) >>
    suspend "loop_bounds")) >>
  disch_tac >> suspend "source"
QED

Resume intcall_array_value_producer[loop_bounds]:
  gvs[] >> conj_tac >- suspend "stride_bound" >>
  fs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Resume intcall_array_value_producer[stride_bound]:
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_joint_res_def] >>
  `type_memory_bytes ce (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
    metis_tac[expr_sim_inv_memory_size] >>
  `0 < bound_length bnd` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def] >>
     gvs[AllCaseEqs()]) >>
  Cases_on `bnd` >>
  gvs[vyperASTTheory.bound_length_def, valueEncodingTheory.type_memory_size_def,
      wordsTheory.dimword_def] >>
  `type_memory_size tv <= n * type_memory_size tv` by
    (once_rewrite_tac[GSYM arithmeticTheory.MULT_LEFT_1] >>
     rewrite_tac[arithmeticTheory.LE_MULT_RCANCEL] >> simp[]) >> decide_tac
QED

Resume intcall_array_value_producer[source]:
  irule gas_outcome_zero_prefix_any >>
  goal_assum (drule_at Any) >>
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `!st. eval_expr fp.jc_cx
      (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) st =
      (case eval_exprs fp.jc_cx args st of (rr,ee) =>
        ((case rr of INL vs => INL (Value (ArrayV (make_array_value tv bnd vs)))
                   | INR exc => INR exc),ee))` by
    (gen_tac >> Cases_on `eval_exprs fp.jc_cx args st` >>
     simp[] >> irule aggregate_eval_make_array >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "counted_source"
  >> suspend "exempt_source"
QED

Resume intcall_array_value_producer[counted_source]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >> strip_tac
  >- suspend "normal_source"
  >> suspend "exit_source"
QED

Resume intcall_array_value_producer[exempt_source]:
  `ignore_bind (eval_expr fp.jc_cx
      (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args)) (return ()) =
   ignore_bind (eval_exprs fp.jc_cx args) (return ())` by
    (simp[FUN_EQ_THM, vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def] >>
     gen_tac >> Cases_on `eval_exprs fp.jc_cx args x` >>
     rename1 `eval_exprs _ _ _ = (rr,ee')` >> Cases_on `rr` >>
     simp[vyperStateTheory.return_def]) >>
  qexists_tac `marks` >> disj2_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

Resume intcall_array_value_producer[normal_source]:
  gvs[] >>
  qexistsl [`INL (Value (ArrayV (make_array_value tv bnd vs)))`, `es_end`, `OK t`] >>
  conj_tac
  >- (fs[gas_marked_exec_def] >> simp[]) >>
  `u = Var p` by metis_tac[compiler_make_array_elems_result] >>
  gvs[vyperASTTheory.expr_type_def, contextTheory.mk_ptr_def,
      contextTheory.vv_operand_def] >>
  `val_in_memory (ArrayTV tv bnd)
    (ArrayV (make_array_value tv bnd vs)) (w2n w) t.vs_memory` by
    suspend "array_memory" >>
  suspend "array_endpoint"
QED

Resume intcall_array_value_producer[exit_source]:
  `?exc. res = INR exc` by
    (Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
  gvs[] >> qexistsl [`INR exc`, `es_end`, `r`] >>
  conj_tac >- (fs[gas_marked_exec_def] >> simp[]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `exc` >> Cases_on `r` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def]
QED

Resume intcall_array_value_producer[array_memory]:
  Cases_on `bnd`
  >- (irule fixed_array_from_dense >>
      gvs[vyperValueTheory.compatible_bound_def]) >>
  gvs[vyperValueTheory.make_array_value_def, val_in_memory_dynarray] >>
  rewrite_tac[mem_word_at_bytes] >>
  `mem_bytes_at (w2n w) 32 t.vs_memory =
   mem_bytes_at (w2n w) 32 u'.vs_memory` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  qpat_x_assum `mem_word_at _ _ = _` mp_tac >>
  pure_rewrite_tac[mem_word_at_bytes] >>
  pure_asm_rewrite_tac[] >> simp[]
QED

Resume intcall_array_value_producer[array_endpoint]:
  `type_memory_bytes ce (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
    (irule expr_sim_inv_memory_size >>
     fs[intcall_joint_res_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[loweringPostsTheory.vv_holds_def,
           vyperStateTheory.read_result_def, vyperStateTheory.return_def, is_word_type_def] >>
      qexists_tac `w` >> asm_rewrite_tac[]) >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[compiler_ci_mono_not_fresh] >>
      strip_tac >> qexistsl [`w2n w`, `type_memory_size (ArrayTV tv bnd)`] >>
      gvs[]) >>
  `expr_body_pre ce fp.jc_cx env
    (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args)
    (es with gas_obs := gas_explicit marks u'.vs_gas_readings)` by simp[] >>
  `eval_expr fp.jc_cx
    (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args)
    (es with gas_obs := gas_explicit marks u'.vs_gas_readings) =
    (INL (Value (ArrayV (make_array_value tv bnd vs))),
     es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `value_has_type (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs))` by
    (qpat_x_assum `!tv'. INL _ = _ ==> _`
       (qspec_then `Value (ArrayV (make_array_value tv bnd vs))` mp_tac) >>
     simp[vyperTypeInvariantsTheory.eval_result_typed_def, vyperASTTheory.expr_type_def]) >>
  irule allocated_value_vv_at >>
  qexistsl [`sa.cs_next_id`, `w2n w`, `type_memory_size (ArrayTV tv bnd)`,
            `ArrayTV tv bnd`, `w`] >>
  simp[loweringPostsTheory.val_footprint_def] >>
  conj_tac >- fs[ci_mono_def] >>
  fs[regions_disjoint_def] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >> simp[]
QED

Finalise intcall_array_value_producer

Theorem intcall_array_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a t n args. e = Builtin a (MakeArray (SOME t) n) args) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
