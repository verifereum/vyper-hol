(* Typed runtime code aggregates: allocation followed by immutable copying. *)
Theory bodyImmutableUnwrapMemory
Ancestors
  loweringPosts
  valueEncodingProps
  bodyImmutableCopyMemory bodyAllocMemory allocaHistoryFragment abiBuiltinAllocation
  instMemFrontier storageDecodeMemory venomMemDefs
  exprSimCopy exprSimStorageCopy immutableCopyExecution fragExec fragExecMem
  exprSimDefs exprSimOps exprLowering valueEncoding valueEncodingDefs localPtrsProps exprSimAlloc
  context compileEnv loweringStateRelDefs exprLoweringProps emitHelperProps venomExecSemantics
  venomState venomInst words arithmetic list rich_list finite_map

Theorem body_code_copy_history[local]:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >> drule code_copy_insts >> strip_tac >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[same_blocks_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[] >> gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_code_copy_frag_mem:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  copy_old_operand sa src /\ copy_old_operand sa dst ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ eval_operand src s = SOME a /\
      eval_operand dst s = SOME b /\
      w2n b + off + 32 * n <= s.vs_alloca_next /\
      w2n b + off + 32 * n < dimword (:256) /\
      w2n a + off + 32 * n <= LENGTH s.vs_data_section /\
      w2n a + off + 32 * n < dimword (:256) /\
      alloca_history func s /\ alloca_inv s)
    (\t. t.vs_memory = (immutable_transfers F F a b n off s0).vs_memory /\
      copy_static t = copy_static s0 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      t.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func t) R
Proof
  rpt strip_tac >> drule code_copy_insts >> strip_tac >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  qabbrev_tac `P = \s. s = s0 /\ eval_operand src s = SOME a /\
    eval_operand dst s = SOME b /\
    w2n b + off + 32 * n <= s.vs_alloca_next /\
    w2n b + off + 32 * n < dimword (:256) /\
    w2n a + off + 32 * n <= LENGTH s.vs_data_section /\
    w2n a + off + 32 * n < dimword (:256) /\
    alloca_history func s /\ alloca_inv s` >>
  `frag_exec_mem ctx sa sb
    (\s. P s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
         s.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\t. t.vs_memory = (immutable_transfers F F a b n off s0).vs_memory /\
      copy_static t = copy_static s0 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      t.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func t) R` by
    (irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def, IS_PREFIX_APPEND] >>
     rpt strip_tac >> gvs[Abbr `P`]
     >- (drule body_immutable_copy_mem_ok >> disch_then irule >>
         goal_assum (drule_at Any) >> simp[]) >>
     drule_all copy_runtime_run >> strip_tac >>
     `run_inst_seq (emitted_insts sa sb) s = OK s' /\
      copy_static s' = copy_static s /\
      (!x. not_fresh_at sa x ==> lookup_var x s' = lookup_var x s)` by
       fs[copy_runtime_frame_def] >>
     drule_all body_code_copy_history >> strip_tac >>
     drule copy_static_fields >> strip_tac >>
     disj1_tac >> goal_assum (drule_at Any) >>
     gvs[copy_runtime_frame_def, copy_static_def, lookup_var_def]) >>
  fs[frag_exec_mem_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* At runtime an immutable's bytes lie inside the data section. *)
Theorem runtime_immutable_data_section:
  immutable_holds cenv cx t (Value v) a es s /\ ~cenv.ce_is_ctor /\
  stmt_state_rel ctx func cenv cx es u /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  w2n a + type_memory_size tv <= LENGTH u.vs_data_section
Proof
  rw[immutable_holds_def] >> gvs[sub_layout_def] >>
  gvs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem unwrap_runtime_code_copy_sim_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) ==>
    frag_exec_mem ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s /\
           s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
           s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  irule frag_exec_mem_pointwise >> qx_gen_tac `s1` >> simp[] >> strip_tac >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       immutable_holds cenv cx t (Value v) a es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv t < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid cs'' /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= cs''.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func /\ fn_has_code mid cs'' func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s1` by gvs[vv_post_def] >>
  drule_all alloc_buffer_source_frag_mem >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `(type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `w2n a + type_memory_size tv <= LENGTH u.vs_data_section` by
    (irule runtime_immutable_data_section >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
     qpat_x_assum `!aid base sz. _` drule >> simp[]) >>
  qpat_assum `frag_exec_mem ctx sm mid _ _ R`
    (mp_then Any mp_tac frag_exec_mem_then) >>
  disch_then irule >> simp[] >> strip_tac >>
  drule_all body_code_copy_frag_mem >>
  disch_then (qspecl_then [`u`, `ctx`, `w`, `a`, `R`] mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_mem_conseq) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[type_memory_size_slots] >> decide_tac) >>
  gen_tac >> strip_tac >>
  `s.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory` by
    metis_tac[] >>
  `w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all copy_runtime_contents >> strip_tac >>
  suspend "typed_post"
QED

Resume unwrap_runtime_code_copy_sim_mem[typed_post]:
  `LENGTH u.vs_memory <= LENGTH s.vs_memory /\
   (!off len. off + len <= w2n w \/
      w2n w + type_memory_bytes cenv t <= off ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (Cases_on `type_slot_size tv = 0`
     >- gvs[immutable_transfers_def] >>
     `immutable_transfers F F a w (type_slot_size tv) 0 u =
       write_memory_with_expansion (w2n w)
         (mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section) u` by
       (qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `u`] mp_tac
         immutable_runtime_transfers_snapshot >>
        simp[mem_bytes_at_def, type_memory_size_slots] >>
        gvs[type_memory_size_slots]) >>
     gvs[] >> conj_tac
     >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
     rpt strip_tac >>
     simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]) >>
  `eval_operand (Var p') s = SOME w` by
    (qsuff_tac `eval_operand (Var p') s = eval_operand (Var p') u`
     >- gvs[] >>
     irule storage_copy_operand_preserved >> simp[] >>
     qexists `mid` >> simp[]) >>
  irule copy_buffer_post_transport >>
  qpat_assum `t = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, SF SFY_ss] >>
  qexists `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl [`mid`, `s1`, `sm`, `u`, `LocatedValue t p`] >>
  simp[mk_inst_def] >> gnvs[] >> metis_tac[]
QED

Finalise unwrap_runtime_code_copy_sim_mem

