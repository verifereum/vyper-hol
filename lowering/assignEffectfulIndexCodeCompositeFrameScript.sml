Theory assignEffectfulIndexCodeCompositeFrame
Ancestors
  exprSimUnwrap exprSimCopy exprSimStorageCopy
  placeStoreStorage placeMemoryStaging exprSimAlloc exprLoweringProps
  stmtSimDefs exprLowering context compileEnv loweringPosts
  freshWrites emitHelper emitHelperProps venomState venomInst
  venomExecSemantics fragGasMode fragGasPath fragExec
  immutableMemoryFrame immutableCopyExecution immutableRelation
  valueEncoding valueEncodingProps entrySinkExtraction exprSimProps loweringStateRelDefs
Libs
  monadsyntax

Theorem snapshot_code_suffix_path[local]:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (ctor ==> !region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\
    z.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory /\
    copy_static z = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?u. copy_runtime_frame sa s sb u /\
       u.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory` by
    (Cases_on `ctor` >> gvs[] >>
     metis_tac[copy_ctor_run, copy_runtime_run]) >>
  `same_blocks sa sb /\ ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
     EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) is` by
    (Cases_on `ctor` >> gvs[]
     >- (drule code_ctor_copy_insts >> strip_tac >> simp[] >>
         fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
     drule code_copy_insts >> strip_tac >> simp[] >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  fs[copy_runtime_frame_def] >>
  `is = emitted_insts sa sb` by metis_tac[listTheory.APPEND_11] >>
  gvs[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (fs[listTheory.EVERY_MEM] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!i. MEM i _ ==> _` drule >>
         strip_tac >> gvs[is_terminator_def]) >>
     simp[listTheory.LENGTH_NIL, listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
     rpt strip_tac >> qpat_x_assum `!i. MEM i _ ==> _` drule >>
     strip_tac >> gvs[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all place_store_emitted_seq_path >> disch_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[copy_static_def, same_blocks_def, lookup_var_def]
QED

Theorem snapshot_code_types[local]:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  p.ptr_location = LocCode /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    type_memory_bytes cenv t = type_memory_size tvt) ==>
  t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s /\
  ?a tv. eval_operand p.ptr_operand s = SOME a /\
    immutable_holds cenv cx t (Value v) a es' s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_bytes cenv t < dimword (:256) /\
    (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >> simp[] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       immutable_holds cenv cx t (Value v) a es' s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     gvs[vv_post_def, vv_holds_def]) >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  drule_all immutable_holds_bounds >> strip_tac >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  qexistsl_tac [`a`, `tv`] >> simp[] >>
  gvs[type_memory_size_slots] >> decide_tac
QED

Theorem snapshot_code_layout[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type t /\ fn_has_code sm sb func ==>
  ?buf mid. compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca
      p.ptr_operand buf.buf_operand ((type_memory_bytes cenv t + 31) DIV 32) 0
      mid = ((),sb) /\
    op = buf.buf_operand /\ ci_mono sm mid /\ ci_mono mid sb /\
    fn_has_code sm mid func /\ fn_has_code mid sb func
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[comp_ignore_bind_def, comp_return_def] >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = ((),sb)` >>
  `ci_mono mid sb` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  simp[] >> fs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem snapshot_runtime_contents_frame[local]:
  stmt_state_rel ctx func cenv cx es u /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  z.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory ==>
  val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
  val_footprint tv v <= type_memory_size tv /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> drule_all copy_runtime_contents >> strip_tac >> simp[] >>
  drule_all immutable_holds_bounds >> strip_tac >>
  Cases_on `type_slot_size tv = 0`
  >- gvs[immutable_transfers_def, type_memory_size_slots] >>
  `immutable_transfers F F a w (type_slot_size tv) 0 u =
    write_memory_with_expansion (w2n w)
      (mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section) u` by
    (qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `u`]
      mp_tac immutable_runtime_transfers_snapshot >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def, type_memory_size_slots] >>
     gvs[type_memory_size_slots]) >>
  gvs[] >> conj_tac >- simp[immutable_write_memory_capacity] >>
  rpt strip_tac >> simp[write_memory_mem_bytes_at_disjoint]
QED

Theorem snapshot_code_contents_frame[local]:
  stmt_state_rel ctx func cenv cx es u /\
  immutable_holds cenv cx t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (cenv.ce_is_ctor ==> regions_disjoint (w2n a) (type_memory_size tv)
    (w2n w) (type_memory_size tv)) /\
  z.vs_memory = (immutable_transfers F cenv.ce_is_ctor a w (type_slot_size tv) 0 u).vs_memory ==>
  val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
  val_footprint tv v <= type_memory_size tv /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> Cases_on `cenv.ce_is_ctor`
  >- (`regions_disjoint (w2n a) (type_memory_size tv)
          (w2n w) (type_memory_size tv)` by metis_tac[] >>
      `z.vs_memory = (immutable_transfers F T a w (type_slot_size tv) 0 u).vs_memory`
        by simp[] >>
      drule_all copy_ctor_contents >> simp[]) >>
  `z.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory`
    by simp[] >>
  drule_all snapshot_runtime_contents_frame >> simp[]
QED

Theorem snapshot_code_composite_frame:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    p.ptr_location = LocCode /\ ~is_word_type t /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
      type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?z. gas_marked_path F ctx func s 0 (OK z) /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op z /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP z.vs_allocas aid = SOME entry) /\
      alloca_frame cenv es' sm s cenv es' z /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all snapshot_code_layout >> strip_tac >>
  drule_all snapshot_code_types >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all compile_alloc_buffer_forward >> strip_tac >>
  rename1 `eval_operand buf.buf_operand u = SOME w` >>
  `sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id` by
    fs[ci_mono_def] >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand p.ptr_operand u = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def]) >>
  `immutable_holds cenv cx t (Value v) a es' u` by
    metis_tac[immutable_holds_memory_cong] >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  `cenv.ce_is_ctor ==> !region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >>
     `immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     `eval_operand region s = SOME 0w` by fs[immutable_base_zero_def] >>
     `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
       metis_tac[local_ptrs_reserved_imm_base] >>
     Cases_on `region` >> gvs[eval_operand_def, copy_old_operand_def] >>
     metis_tac[not_fresh_at_mono]) >>
  drule_all snapshot_code_suffix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "endpoint"
QED

Resume snapshot_code_composite_frame[endpoint]:
  markerLib.RESUME_TAC >>
  `!aid b len. aid < sm.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) (type_memory_bytes cenv t) b len` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
     `alloca_inv u` by fs[stmt_state_rel_def] >>
     qpat_x_assum `alloca_inv u` mp_tac >>
     simp[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        regions_disjoint_def] >> strip_tac >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`sm.cs_next_id`, `aid`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_all buffer_alloc_code >>
  qmatch_abbrev_tac `MEM inst (fn_insts func) ==> _` >> strip_tac >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id` by
    simp[Abbr `inst`, mk_inst_def] >>
  `cenv.ce_is_ctor ==> regions_disjoint (w2n a) (type_memory_size tv)
       (w2n w) (type_memory_size tv)` by
    (strip_tac >> irule immutable_holds_alloca_disjoint >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es'`, `func`] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `inst` >> simp[] >> metis_tac[]) >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
   val_footprint tv v <= type_memory_size tv /\
   LENGTH u.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (`w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
     irule snapshot_code_contents_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `sm.cs_next_id < sb.cs_next_id` by decide_tac >>
  `eval_operand buf.buf_operand z = SOME w` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v op z` by
    (irule copy_buffer_post_transport >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     qexistsl_tac [`mid`, `tv`] >> gvs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at mid x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  `!name b len. local_region cenv es'.scopes z name b len <=>
       local_region cenv es'.scopes s name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sm` >> simp[]) >>
  `alloca_frame cenv es' sm s cenv es' z` by
    (pure_rewrite_tac [alloca_frame_def] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac >-
       (qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
          (qspecl_then [`off`, `sz`] mp_tac) >>
        `regions_disjoint (w2n w) (type_memory_bytes cenv t) off sz` by
          (qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` irule >>
           qexists_tac `aid` >> simp[]) >>
        gvs[regions_disjoint_def]) >>
     metis_tac[]) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_halted = u.vs_halted` by
    (qpat_x_assum `copy_static z = copy_static u` mp_tac >>
     simp[copy_static_def, venom_state_component_equality]) >>
  qexists_tac `z` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Finalise snapshot_code_composite_frame
