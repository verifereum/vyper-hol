(* Fresh storage-layout normalization uses the checked allocator and typed copy. *)
Theory aggregateNormalizePtr
Ancestors
  widenedAssignPtrCopyRecursive assignBasePtrAllocSource assignBasePtrAllocSeparate
  assignBasePtrLiteralOutcome exprSimStorageCopy exprSimPtrLiteralBuffer
  bodyPtrMakeArrayAllocBuffer bodyPtrMakeArrayMaterialiseFrame
  bodyPtrMakeArrayCopyStateFrame bodyPtrIfExpAllocGhost
  typedMemoryCopy exprSimAlloc exprSimProps exprLoweringProps loweringHalt
  context compileEnv loweringStateRelDefs emitHelperProps fragExec fragGasPathPtr
  ghostPcTransportPtr allocationPtr ptrDiscipline bodyPtrDefs
  venomState venomInst venomExecSemantics words finite_map arithmetic list rich_list

Theorem aggregate_normalize_alloc_ptr[local]:
  !ctx fn cenv cx es sa sm buf n s G tn d D PG sty stv v src sw va vb.
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_val_at cenv cx sty va vb es v (Var src) s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  lookup_var src s = SOME sw /\
  ptr_covers G tn src s (type_memory_size stv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m) ==>
  ?root b u H tt.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
    stmt_state_rel ctx fn cenv cx es u /\ ghost_inv d cenv cx es H tt u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
    lookup_var root u = SOME (n2w b) /\ ptr_covers H tt root u n /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\ b+n < dimword (:256) /\
    ptr_covers H tt src u (type_memory_size stv) /\ lookup_var src u = SOME sw /\
    (!m. mem_agree_outside tt.t_mem u.vs_memory m ==>
      val_in_memory stv v (w2n sw) m) /\
    u.vs_memory = s.vs_memory /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!i. i < b \/ b+n <= i ==> (i IN tt.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tt (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid base cap. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (base,cap) ==> regions_disjoint b n base cap) /\
    (!name base cap. local_region cenv es.scopes u name base cap ==>
      regions_disjoint b n base cap) /\
    (!name base cap. local_region cenv es.scopes u name base cap <=>
      local_region cenv es.scopes s name base cap) /\
    not_fresh_at sm root /\ (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts fn)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  qabbrev_tac `root = STRING #"%" (toString sa.cs_next_var)` >>
  `buf.buf_operand = Var root /\ src <> root /\
   not_local_ptr cenv es.scopes root /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> root) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> root)` by
    (simp[Abbr `root`] >> rpt conj_tac >>
     metis_tac[local_ptrs_reserved_fresh,not_fresh_at_def]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts fn)` by
    simp[Abbr `root`] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sa sm fn` mp_tac >>
     simp[fn_has_code_def,IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >> simp[emitted_insts_def,DROP_APPEND1]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all (Q.INST [`PG` |-> `PG`,`G` |-> `G`,`tn` |-> `tn`,`D` |-> `D`]
    (SPEC_ALL literal_alloc_buffer_ptr_run)) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choosel_then [`raw`,`a`,`H`,`tt`]
      (map_every assume_tac o CONJUNCTS))) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) s = OK raw` by
    (drule alloc_buffer_emitted >> strip_tac >>
     gvs[Abbr `root`,run_inst_seq_def,AllCaseEqs()]) >>
  `H = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) raw /\
   tt = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) s raw tn` by
    simp[Abbr `root`] >>
  drule_all literal_alloca_static_frame >> strip_tac >>
  drule_all (Q.INST [`PG` |-> `PG`,`G` |-> `G`,`tn` |-> `tn`]
    (SPEC_ALL literal_alloca_old_ghost)) >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all literal_alloca_exterior_taint >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (qpat_assum `not_local_ptr cenv es.scopes root` mp_tac >> simp[Abbr `root`]) >>
  drule_all (Q.INST [`ix` |-> `SUC s.vs_inst_idx`]
    (SPEC_ALL assign_base_alloc_buffer_run_frames)) >> disch_then (strip_assume_tac o SPEC_ALL) >>
  `eval_operand (Var src) s = SOME sw /\ Var src <> Var root` by
    simp[eval_operand_def] >>
  drule_all assign_base_ptr_alloca_robust_source >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all (Q.INST [`PG` |-> `PG`]
    (SPEC_ALL alloca_step_old_ptr_covers)) >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all (Q.INST [`PG` |-> `PG`]
    (SPEC_ALL alloca_step_ghost_inv_separated)) >> disch_then (strip_assume_tac o SPEC_ALL) >>
  `ghost_inv d cenv cx es H tt (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
    gvs[assign_base_ptr_ghost_index] >>
  `!name base cap.
    local_region cenv es.scopes (raw with vs_inst_idx := SUC s.vs_inst_idx) name base cap <=>
    local_region cenv es.scopes raw name base cap` by
    simp[local_region_def,lookup_var_def] >>
  qexistsl_tac [`root`,`w2n a`,`raw with vs_inst_idx := SUC s.vs_inst_idx`,`H`,`tt`] >>
  gvs[Abbr `root`,lookup_var_def,eval_operand_def,stmt_state_rel_inst_idx] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem aggregate_normalize_fresh_ptr:
  !cenv ctx fn cx es sa sm sb buf s G tn d D PG sty dty stv dtv v
    src sw va vb base cap.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\ ~is_word_type sty /\ ~is_word_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty (Var src) sty sm = ((),sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_val_at cenv cx sty va vb es v (Var src) s /\
  lookup_var src s = SOME sw /\ ptr_covers G tn src s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  type_memory_size dtv < dimword (:256) /\
  base <= w2n sw /\ w2n sw + type_memory_size stv <= base+cap /\
  ((?name. local_region cenv es.scopes s name base cap) \/
   ?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,cap)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root b u H tt t Gf tf.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
    gas_path_ptr D 0 ctx fn PG H tt u 0 Gf tf (OK t) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es Gf tf t /\
    ghost_kept cenv es sa G tn s Gf tf /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var root t = SOME (n2w b) /\
    ptr_covers Gf tf root t (type_memory_size dtv) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,type_memory_size dtv) /\
    b+type_memory_size dtv < dimword (:256) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
      val_in_memory dtv v b m) /\
    typed_copy_state_frame sm b (type_memory_size dtv) u t /\
    (!name lb len. local_region cenv es.scopes t name lb len ==>
      regions_disjoint b (type_memory_size dtv) lb len) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP t.vs_allocas aid = SOME site) /\
    (!aid lb len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (lb,len) ==>
      regions_disjoint b (type_memory_size dtv) lb len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. i < b \/ b+type_memory_size dtv <= i ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `source_base <= w2n sw` >>
  drule_all (Q.INST [`D` |-> `D`,`PG` |-> `PG`]
    (SPEC_ALL aggregate_normalize_alloc_ptr)) >>
  disch_then ((qx_choosel_then [`root`,`b`,`u`,`H`,`tt`]
    (map_every assume_tac o CONJUNCTS)) o SPEC_ALL) >>
  `regions_disjoint b (type_memory_size dtv) source_base cap` by
    (qpat_assum `(?name. local_region _ _ _ _ _ _) \/ _` strip_assume_tac >>
     metis_tac[]) >>
  `b+type_memory_size dtv <= w2n sw \/
   w2n sw+type_memory_size stv <= b` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sm src` by
    (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` irule >>
     first_assum ACCEPT_TAC) >>
  `op_taint tt (Var root) = {} /\ op_taint tt (Var src) = {}` by
    fs[ptr_covers_def] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by asm_simp_tac (srw_ss()) [w2n_n2w] >>
  mp_tac (Q.SPECL [`cenv`,`get_tenv cx`,`ctx`,`D`,`PG`,`dty`,`sty`,`dtv`,`stv`,`v`]
    widened_assign_typed_store_counted_ptr) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`sm`,`sb`,`Var root`,`Var src`,`n2w b`,`sw`,`fn`,`H`,`tt`,`u`] mp_tac) >>
  (impl_tac >- (simp[eval_operand_def] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`Gf`,`tf`,`t`]
    (map_every assume_tac o CONJUNCTS o
      SIMP_RULE (srw_ss()) [ASSUME ``b < dimword (:256)``,w2n_n2w,LESS_MOD])) >>
  `copy_static t = copy_static u /\ LENGTH u.vs_memory <= LENGTH t.vs_memory /\
   t.vs_allocas = u.vs_allocas /\ t.vs_call_ctx = u.vs_call_ctx /\
   t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
   (!off len. off+len <= b \/ b+type_memory_size dtv <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[typed_copy_state_frame_def,typed_copy_frame_def,copy_static_def,
       venom_state_component_equality,ADD_COMM] >> strip_tac >>
     rpt conj_tac >> rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >>
     first_x_assum irule >> simp[ADD_COMM]) >>
  `stmt_state_rel ctx fn cenv cx es t` by
    (irule literal_copy_window_stmt_state_rel >>
     qexistsl_tac [`sa.cs_next_id`,`b`,`type_memory_size dtv`,`root`,`sa`,`sm`,`u`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `!i. i < b \/ b+type_memory_size dtv <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (`i+1 <= b \/ b+type_memory_size dtv <= i` by decide_tac >>
         qpat_assum `!off len. off+len <= b \/ b+type_memory_size dtv <= off ==> _`
           (qspecl_then [`i`,`1`] mp_tac) >>
         asm_simp_tac (srw_ss()) []) >>
     metis_tac[NOT_LESS,LESS_OR_EQ]) >>
  `ghost_inv d cenv cx es Gf tf t /\ ghost_kept cenv es sa G tn s Gf tf` by
    (mp_tac (Q.INST [`func` |-> `fn`,`z` |-> `t`,`H` |-> `Gf`,
       `tm` |-> `tf`,`n` |-> `type_memory_size dtv`]
       literal_allocated_copy_ghost_post) >>
     (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> metis_tac[])) >>
     simp[]) >>
  `lookup_var root t = lookup_var root u /\
   FLOOKUP Gf root = FLOOKUP H root /\
   op_taint tf (Var root) = op_taint tt (Var root)` by
    (qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `root` mp_tac) >> simp[]) >>
  `ptr_covers Gf tf root t (type_memory_size dtv) /\
   lookup_var root t = SOME (n2w b)` by
    (qpat_x_assum `ptr_covers H tt root u _` mp_tac >>
     asm_simp_tac (srw_ss()) [ptr_covers_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[] >>
  `!name lb len. local_region cenv es.scopes t name lb len <=>
    local_region cenv es.scopes s name lb len` by
    (mp_tac (Q.INST [`scopes` |-> `es.scopes`] literal_ptr_local_region_frame) >>
     (impl_tac >- asm_rewrite_tac[]) >> simp[]) >>
  `!name lb len. local_region cenv es.scopes t name lb len ==>
    regions_disjoint b (type_memory_size dtv) lb len` by metis_tac[] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  qexistsl_tac [`root`,`b`,`u`,`H`,`tt`,`t`,`Gf`,`tf`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
