(* Declaration framing for typed copies, whose endpoint may change blocks. *)
Theory bodyDeclWidenedMemory
Ancestors
  bodyDeclCopyMemory bodyWidenedCopyMemory placeMemoryCopyEffect gasPathAllocaHistory
  fragGasMode fragGasPathMem bodyMemoryDefs venomMemDefs
  abiCallerAllocation exprSimOperands exprSimTypedAlloc exprSimAggregateChildren
  abiBuiltinAllocation valueEncodingProps exprOperandVar
  stmtLowering context exprSimMemDefs bodyMemAssignTopCopyFacts
  stmtSimDeclStore localPtrsProps valueTypingMemoryProps
  bodyMemAssignTupleTargetsFacts bodyDeclMemoryCore fragExec
  loweringPosts exprSimDefs stmtSimDefs venomState finite_map
  freshWrites loweringStateRelDefs loweringSlice exprSimHypsDefs compileEnv exprLoweringProps

Theorem typed_copy_declare_memory_frame:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size tyv) /\
  type_memory_size tyv <= sz /\ val_wf tyv v /\
  val_in_memory tyv v (w2n w) t.vs_memory ==>
  stmt_state_rel ctx func cenv cx
    (es with scopes :=
      (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  strip_tac >>
  qpat_assum `typed_copy_effect _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_effect_def]) >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
      vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def, immutable_alloca_sep_def] >>
     rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* A single checked copy endpoint carries both scope and allocation framing. *)
Theorem annassign_typed_copy_endpoint_mem:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
  sa.cs_next_var <= sb.cs_next_var /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size tyv) /\
  gas_marked_path T ctx func s 0 (OK t) /\
  alloca_history func s /\ return_buf_frame d cenv sa s /\
  type_memory_size tyv <= sz /\ val_wf tyv v /\
  val_in_memory tyv v (w2n w) t.vs_memory ==>
  gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel ctx func cenv cx
    (es with scopes :=
      (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  return_buf_frame d cenv sb t /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `gas_path_mem ctx func s 0 (OK t)` by fs[gas_marked_path_def] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func t` by
    (drule gas_path_mem_exec >> strip_tac >>
     metis_tac[gas_path_alloca_history]) >>
  `stmt_state_rel ctx func cenv cx
    (es with scopes :=
      (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (irule typed_copy_declare_memory_frame >> simp[] >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     qexists_tac `inst` >> gvs[]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s`, `sa`] >> simp[] >>
     metis_tac[typed_copy_effect_lookup]) >>
  fs[typed_copy_effect_def]
QED

(* A value window cannot overlap an allocation outside its expression interval. *)
Theorem expression_source_window_outside_disjoint:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty sa sb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\ cap <= val_footprint tv v /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  ~(sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (w2n p,cap) (b,sz)
Proof
  strip_tac >> Cases_on `cap = 0`
  >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >>~- ([`sa.cs_next_id <= aid`, `aid < sb.cs_next_id`],
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     `aid <> inst.inst_id` by decide_tac >>
     drule_all abi_caller_allocation_separate >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  drule_all alloca_clear_of_locals >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem annassign_widened_post_path_mem:
  expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
  post_value_type cenv e = expr_type e /\
  expr_store_bound cx (expr_type e) v op s /\
  (loc = SOME LocMemory ==>
    !sw. eval_operand op s = SOME sw ==>
      type_memory_size stv = 0 \/
      w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  local_ptrs_reserved cenv sa /\
  ~is_word_type dt /\ ~is_bytestring_type dt /\ expr_type e <> dt /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_widens_to (get_tenv cx) (expr_type e) dt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) dt = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  0 < type_memory_size dtv /\ type_memory_size dtv <= sz /\
  type_memory_size stv + 64 < dimword (:256) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  compile_assign_value cenv (Var p) LocMemory op F loc dt (expr_type e)
    info bytes sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ return_buf_frame d cenv sb s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
  lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ inst.inst_id < sa.cs_next_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  w2n w + type_memory_size dtv <= s.vs_alloca_next /\
  (!sp ss se u sw dw.
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv (Var p) dt sp (expr_type e) ss = ((),se) /\
    not_fresh_at ss p /\ (!x. sp = Var x ==> not_fresh_at ss x) /\
    lookup_var p u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code ss se func /\ ~u.vs_halted /\
    u.vs_current_bb = ss.cs_current_bb /\
    u.vs_inst_idx = LENGTH ss.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func ss se u t (w2n dw) (type_memory_size dtv) /\
      gas_marked_path T ctx func u 0 (OK t)) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    stmt_state_rel ctx func cenv cx
      (es1 with scopes :=
        (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d cenv sf t /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> drule_all (GEN_ALL compile_lower_value_var) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `not_fresh_at sb p /\ local_ptrs_reserved cenv sb` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `val_wf stv v /\ val_wf dtv v` by simp[value_has_type_memory_wf] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[bodyMemAssignTopCopySemTheory.topcopy_val_footprint] >>
  `0 < type_memory_size stv` by
    (drule_all widening_zero_memory_size >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   expr_val_at cenv cx (expr_type e) sa sb es1 v op s` by
    fs[expr_post_def] >>
  `?sw. eval_operand op s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  suspend "direct"
QED

Resume annassign_widened_post_path_mem[direct]:
  `compile_store_memory_typed cenv (Var p) dt op (expr_type e) sb = ((),sf)` by
    gvs[compile_assign_value_def, compile_store_memory_def] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def] >>
     `val_store_size stv v = type_memory_size stv` by
       metis_tac[topcopy_val_store_size] >> simp[]) >>
  `venomMemDefs$regions_disjoint
    (w2n sw,type_memory_size stv) (w2n w,sz)` by
    (irule expression_source_window_outside_disjoint >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [`inst`, `stv`, `p`] >> simp[] >> decide_tac) >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   w2n w + type_memory_size dtv < dimword (:256)` by decide_tac >>
  qpat_x_assum `!sp ss se u sw dw. _`
    (qspecl_then [`op`, `sb`, `sf`, `s`] mp_tac) >>
  simp[] >>
  strip_tac >> qexists_tac `t` >>
  `sb.cs_next_var <= sf.cs_next_var` by
    metis_tac[ci_mono_def, pairTheory.SND, cj 1 ci_mono_typed_memory_family] >>
  irule annassign_typed_copy_endpoint_mem >> simp[] >>
  qexists_tac `inst` >> gvs[]
QED

Resume annassign_widened_post_path_mem[staged]:
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, compile_store_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_alloc_buffer (type_memory_size stv) sb` >>
  rename1 `compile_alloc_buffer (type_memory_size stv) sb = (buf,sm)` >>
  Cases_on `compile_copy_memory buf.buf_operand op (type_memory_size stv) sm` >>
  rename1 `compile_copy_memory buf.buf_operand op (type_memory_size stv) sm = (unit,sn)` >>
  Cases_on `unit` >> simp[] >> strip_tac >>
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `cs_extends sb sn` by metis_tac[cs_extends_trans] >>
  `cs_extends sn sf` by
    (qspec_then `cenv` mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`Var p`, `dt`, `buf.buf_operand`, `expr_type e`, `sn`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sb sn func /\ fn_has_code sn sf func` by
    (irule fn_has_code_split >> simp[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (qpat_x_assum `loc = SOME LocMemory ==> _` mp_tac >> simp[]) >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  `val_footprint stv v <= type_memory_size stv` by simp[] >>
  drule_all tuple_scratch_prefix_path_mem >>
  disch_then (qx_choose_then `u` (qx_choose_then `uw` strip_assume_tac)) >>
  `not_fresh_at sn p /\ local_ptrs_reserved cenv sn` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sn x` by
    (drule compiler_alloc_buffer_var >> strip_tac >> rpt strip_tac >>
     `sm.cs_next_var <= sn.cs_next_var` by
       (drule exprSimBufferStoreTheory.buffer_copy_memory_shape >> simp[]) >>
     metis_tac[not_fresh_at_mono]) >>
  `lookup_var p u = SOME w /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz)` by metis_tac[] >>
  `sa.cs_next_id <= sb.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  `inst.inst_id <> sb.cs_next_id` by decide_tac >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `w2n uw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n uw` by
    (fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def] >>
     first_x_assum drule_all >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `w2n uw + type_memory_size stv < dimword (:256) /\
   w2n w + type_memory_size dtv < dimword (:256) /\
   w2n w + type_memory_size dtv <= u.vs_alloca_next` by decide_tac >>
  qpat_x_assum `!sp ss se u sw dw. _`
    (qspecl_then [`buf.buf_operand`, `sn`, `sf`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  `sn.cs_next_var <= sf.cs_next_var` by
    metis_tac[ci_mono_def, pairTheory.SND, cj 1 ci_mono_typed_memory_family] >>
  `gas_path_mem ctx func u 0 (OK t) /\ ~t.vs_halted /\
   t.vs_current_bb = sf.cs_current_bb /\
   t.vs_inst_idx = LENGTH sf.cs_current_insts /\
   stmt_state_rel ctx func cenv cx
     (es1 with scopes :=
       (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
   alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
   return_buf_frame d cenv sf t /\
   (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
   (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b)` by
    (irule annassign_typed_copy_endpoint_mem >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!x. not_fresh_at sb x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sb` >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise annassign_widened_post_path_mem
