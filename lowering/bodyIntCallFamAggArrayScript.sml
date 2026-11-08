(* Seam 2 joint induction, a family leaf of the agg step: array literals. *)
Theory bodyIntCallFamAggArray
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore exprSimAggregateLayout
  exprSimSource exprSimHyps exprSimHypsDefs exprSimAggregateChildren
  vyperTypeInvariants stmtSimDeclPath placeMemoryCopyEffect
  compileEnv emitHelper emitHelperProps venomState venomExecSemantics venomMemProps
  valueEncodingProps intCallFrame exprSimProps exprSimAlloc venomInst
  fragGasMode context

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

Theorem intcall_array_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a t n args. e = Builtin a (MakeArray (SOME t) n) args) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
