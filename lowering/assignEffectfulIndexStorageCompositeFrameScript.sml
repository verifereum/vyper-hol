Theory assignEffectfulIndexStorageCompositeFrame
Ancestors
  exprSimUnwrap exprSimCopy exprSimStorageCopy storageCopyGasPath
  placeStoreStorage placeMemoryStaging exprSimAlloc exprLoweringProps
  stmtSimDefs exprLowering context compileEnv loweringPosts
  freshWrites emitHelper emitHelperProps venomState venomInst
  venomExecSemantics fragGasMode fragGasPath fragExec
  immutableMemoryFrame valueEncodingProps
Libs
  monadsyntax

(* The optimized one-slot suffix needs the same content/frame interface as
   the general storage-copy loop. *)
Theorem snapshot_storage_word_run[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    copy_prefix loc a b 1 s 1 t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = s.vs_current_bb
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = copy_runtime_word loc s a` >>
  `step_inst_base (mk_inst sa.cs_next_id
    (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
    OK (update_var v w s)` by
    (gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         Abbr `w`, copy_runtime_word_def]) >>
  `eval_operand dst (update_var v w s) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (gvs[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE [dst; Var v] [])
    (update_var v w s) = OK (mstore b w (update_var v w s))` by
    (qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule step_MSTORE >> simp[eval_operand_update_var]) >>
  qexists_tac `mstore b w (update_var v w s)` >>
  simp[run_inst_seq_def, GSYM mk_inst_def] >> conj_tac
  >- (`copy_prefix loc a b 1 s (0+1)
        (mstore (b+32*0) (copy_runtime_word loc s (a+n2w 0))
          (update_var v w s))` by
        (irule copy_prefix_extend >> simp[copy_prefix_update_var, copy_prefix_zero]) >>
      gvs[Abbr `w`, Abbr `v`, wordsTheory.WORD_ADD_0]) >>
  simp[immutable_mstore_capacity, update_var_def] >>
  simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem snapshot_storage_word_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\ copy_prefix loc a b 1 s 1 z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all snapshot_storage_word_run >> strip_tac >>
  drule storage_copy_word_layout >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (gvs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND,
         rich_listTheory.DROP_LENGTH_APPEND]) >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >>
     simp[mk_inst_def, is_terminator_def] >>
     Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[copy_prefix_idx, lookup_var_def]
QED

Theorem snapshot_storage_suffix_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; v] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1`
  >- (fs[] >> irule snapshot_storage_word_content_path >> simp[] >>
      qexistsl_tac [`dst`, `src`] >> gvs[] >> metis_tac[]) >>
  fs[] >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (compile_storage_copy_content_capacity_path
    |> Q.SPEC `F`
    |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
    |> Q.SPEC `(ctx,func)`) >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem snapshot_storage_suffix_value_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\ n = type_slot_size tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  n < 2**256 /\ w2n w + 32*n < 2**256 /\ fn_has_code mid sb func /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_operand dst u = SOME (n2w (w2n w))` by simp[] >>
  drule_all snapshot_storage_suffix_content_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a (w2n w) (type_slot_size tv) u (type_slot_size tv) z` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `copy_static z = copy_static u` by gvs[copy_prefix_def] >>
  `eval_operand dst z = SOME w` by
    (drule storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >> simp[]) >>
  qexists_tac `z` >>
  gvs[copy_prefix_def, type_memory_size_slots] >> metis_tac[]
QED

Theorem snapshot_storage_layout[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\ fn_has_code sm sb func ==>
  ?buf mid.
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    (if (type_memory_bytes cenv t + 31) DIV 32 = 1 then
       do value <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                     [p.ptr_operand]; emit_void MSTORE [buf.buf_operand; value] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               ((type_memory_bytes cenv t + 31) DIV 32) p.ptr_location LocMemory F;
             return () od) mid = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm mid func /\ fn_has_code mid sb func /\
    sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `cs_extends sm mid` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends mid cs''` by
    (irule storage_copy_suffix_extends >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (irule storage_copy_suffix_ci_mono >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  gvs[comp_ignore_bind_def, ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem snapshot_storage_types[local]:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    type_memory_bytes cenv t = type_memory_size tvt /\
    type_memory_size tvt < 2**64) ==>
  t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s /\
  ?a tv. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64 /\
    type_memory_bytes cenv t < dimword (:256) /\
    (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv /\
    type_slot_size tv < 2**256
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >> simp[] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[storage_holds_def] >> metis_tac[]) >>
  `type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64` by metis_tac[] >>
  qexistsl_tac [`a`, `tv`] >> simp[] >>
  gvs[type_memory_size_slots, wordsTheory.dimword_def] >> decide_tac
QED

Theorem snapshot_storage_composite_frame:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
      type_memory_bytes cenv t = type_memory_size tvt /\
      type_memory_size tvt < 2**64) /\
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
  drule_all snapshot_storage_layout >> strip_tac >>
  drule_all snapshot_storage_types >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all compile_alloc_buffer_forward >> strip_tac >>
  rename1 `eval_operand buf.buf_operand u = SOME w` >>
  `contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality, contract_storage_def,
          contract_transient_def] >> metis_tac[]) >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >> simp[storage_holds_def]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand p.ptr_operand u = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
    not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256` by
    (fs[type_memory_size_slots, wordsTheory.dimword_def]) >>
  `?z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    eval_operand buf.buf_operand z = SOME w` by
    (irule snapshot_storage_suffix_value_path >> simp[] >>
     qexistsl_tac [`a`, `cenv`, `cx`, `es'`, `p.ptr_location`,
       `p.ptr_operand`, `t`] >> simp[] >> conj_tac
     >- (qpat_x_assum `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> _`
           mp_tac >> simp[]) >>
     qpat_x_assum `(if _ then _ else _) mid = _` mp_tac >> simp[]) >>
  `!aid b len. aid < sm.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) (type_memory_bytes cenv t) b len` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
     `alloca_inv u` by fs[stmt_state_rel_def] >>
     qpat_x_assum `alloca_inv u` mp_tac >>
     simp[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`sm.cs_next_id`, `aid`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_all buffer_alloc_code >>
  qmatch_abbrev_tac `MEM inst (fn_insts func) ==> _` >> strip_tac >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id` by
    simp[Abbr `inst`, mk_inst_def] >>
  `sm.cs_next_id < sb.cs_next_id` by decide_tac >>
  suspend "package"
QED

Resume snapshot_storage_composite_frame[package]:
  markerLib.RESUME_TAC >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v op z` by
    (irule copy_buffer_post_transport >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     qexists_tac `mid` >> gvs[] >> conj_tac >> first_assum ACCEPT_TAC) >>
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
        gvs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     metis_tac[]) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_halted = u.vs_halted` by
    (qpat_x_assum `copy_static z = copy_static u` mp_tac >>
     simp[copy_static_def, venom_state_component_equality]) >>
  qexists_tac `z` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Finalise snapshot_storage_composite_frame
