(* Stage an aggregate in a scratch allocation before relayout. *)
Theory bodyFullMemoryStage
Ancestors
  bodyFullMemoryFrames bodyFullMemoryCopy bodyPtrMakeArrayCopyStateFrame
  robustCopyTransportPtr loweringPosts exprLoweringProps exprSimAlloc
  localPtrsProps compileEnv typedMemoryCopy fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs context venomState venomMemDefs venomInst ptrDiscipline
  memSafeRun fragExec emitHelperProps exprSimPtrLiteralBuffer arithmetic
  bodyMemBopRestWordPath fragGasOrigin fragGasMode fragGasPath
  assignTuplePtrCopyLen freshWrites exprSimStorageCopy
  loweringStateRelDefs
  bodyMemAggregatePath

Theorem body_full_memory_stage_path:
  stmt_state_rel H0 ctx func cenv cx es s /\
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand (Var xs) n sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty /\
  type_memory_size tv = n /\ val_wf tv v /\
  expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s n /\ w2n sw+n < dimword (:256) /\
  (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t root b Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    lookup_var root t = SOME (n2w b) /\ ptr_covers Gf tf root t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,n) /\
    lo <= b /\ b+n < dimword (:256) /\ b+n <= t.vs_alloca_next /\
    (!name a len. local_region cenv es.scopes t name a len ==>
      regions_disjoint b n a len) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v b mem) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_full_alloc_buffer_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  `b < dimword (:256)` by decide_tac >>
  `local_ptrs_reserved cenv sm /\ not_fresh_at sm xs` by
    metis_tac[] >>
  `lookup_var xs u = SOME sw` by metis_tac[] >>
  `!name a len. local_region cenv es.scopes u name a len <=>
    local_region cenv es.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem` by suspend "source" >>
  `u.vs_alloca_next >= s.vs_alloca_next` by suspend "frontier" >>
  `b+n <= u.vs_alloca_next` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     `gas_path_mem ctx func s 0 (OK u)` by
       (drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
     `alloca_inv u` by metis_tac[aggregate_mem_path_alloca_inv] >>
     fs[alloca_inv_def,alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) ==> _`
       (qspecl_then [`sa.cs_next_id`,`b`,`n`] mp_tac) >> simp[]) >>
  `compile_copy_memory (Var root) (Var xs) n sm = ((),sb)` by metis_tac[] >>
  `ptr_covers G1 tn1 xs u n` by metis_tac[] >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `w2n sw+n < dimword (:256) /\ w2n ((n2w b):bytes32)+n < dimword (:256)` by simp[] >>
  `n <> 0 ==> w2n sw+n <= u.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`xd` |-> `root`,`xs` |-> `xs`,`n` |-> `n`,
    `sa` |-> `sm`,`sb` |-> `sb`,`tv` |-> `tv`,`v` |-> `v`,
    `s` |-> `u`,`sw` |-> `sw`,`dw` |-> `(n2w b):bytes32`,
    `tn` |-> `tn1`,`G` |-> `G1`,`lo` |-> `lo`,`ctx` |-> `ctx`,
    `func` |-> `func`,`explicit` |-> `explicit`,`PG` |-> `PG`]
    (SPEC_ALL body_full_memory_copy_path)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `typed_copy_state_frame sm _ _ u t` >>
  `!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
    ghost_inv_at D lo d cenv cx es Gf tf t` by suspend "ghost" >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_copy_memory,pairTheory.SND] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sb x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)`` o
        CONJUNCT1 o REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `lookup_var root t = SOME (n2w b) /\
   FLOOKUP Gf root = FLOOKUP G1 root /\
   op_taint tf (Var root) = op_taint tn1 (Var root)` by metis_tac[] >>
  `ptr_covers Gf tf root t n` by
    metis_tac[ptr_covers_lookup_frame] >>
  `!name a len. local_region cenv es.scopes t name a len <=>
    local_region cenv es.scopes u name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `!x. not_fresh_at sa x ==>
    not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `b MOD dimword (:256) = b` by simp[] >>
  `allocas_from lo t` by (fs[allocas_from_def] >> metis_tac[]) >>
  qpat_assum `w2n ((n2w b):bytes32) = b`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len` by
    (qpat_assum `!name a len. local_region cenv es.scopes u name a len ==> _` mp_tac >>
     simp[]) >>
  qexistsl_tac [`t`,`root`,`b`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (gen_tac >>
      qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
        (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
      disch_then (qspecl_then [`u`,`G1`,`tn1`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
      simp[]) >>
  conj_tac >- suspend "state" >> first_assum ACCEPT_TAC
QED

Resume body_full_memory_stage_path[source]:
  mp_tac (Q.SPECL [`tn.t_mem`,`tn1.t_mem`,`s.vs_memory`,`u.vs_memory`,
    `{i | b <= i /\ i < b+n}`,`tv`,`v`,`w2n (sw:bytes32)`]
    robust_val_in_memory_exterior_frame) >>
  (impl_tac
   >- (simp[] >> rpt strip_tac >>
       qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
         (mp_tac o Q.SPEC `tv` o REWRITE_RULE [expr_val_at_def]) >>
       simp[eval_operand_def] >> strip_tac >>
       gvs[regions_disjoint_def] >> res_tac >> decide_tac)) >> simp[]
QED

Resume body_full_memory_stage_path[frontier]:
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `cx_dead H0 cx` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  drule gas_origin_path_erase >> strip_tac >>
  drule gas_marked_path_exec >> strip_tac >>
  drule rest_word_path_frontier >> simp[]
QED

Resume body_full_memory_stage_path[state]:
  rpt strip_tac >>
  `copy_static t = copy_static u` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``copy_static`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[copy_static_def]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE
      [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`sa.cs_next_id`,`b`,`n`,
    `STRING #"%" (toString sa.cs_next_var)`,`sa`,`sm`,`u`] >>
  rpt conj_tac >> rpt strip_tac >> simp[] >> first_assum irule >> simp[] >>
  qexists_tac `name` >>
  qpat_assum `!name a len. local_region cenv es.scopes u name a len <=> _`
    (qspecl_then [`name`,`a`,`len`] mp_tac) >> simp[]
QED

Resume body_full_memory_stage_path[ghost]:
  rpt strip_tac >>
  `ghost_inv_at D lo d cenv cx es G1 tn1 u` by metis_tac[] >>
  qpat_assum `w2n ((n2w b):bytes32) = b`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_immutables = u.vs_immutables /\
   t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
   t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``\z. (z.vs_call_ctx,z.vs_immutables,z.vs_accounts,
          z.vs_transient,z.vs_allocas,z.vs_alloca_next)`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sm x` by metis_tac[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sm x` by metis_tac[] >>
  irule body_full_memory_ghost_frame >>
  simp[] >> qexistsl_tac [`G1`,`u`,`sm`,`tn1`,`{i | b <= i /\ i < b+n}`] >>
  simp[] >> rpt conj_tac
  >- (qx_genl_tac [`name`,`entry`,`p`,`cap`,`w`] >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint b n a len` by
        (qpat_assum `!name a len. local_region cenv es.scopes u name a len ==> _` mp_tac >>
         simp[]) >>
      drule_all literal_ptr_local_footprint_exterior >> simp[])
  >- (qx_gen_tac `i` >> strip_tac >>
      qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE
          [typed_copy_state_frame_def,typed_copy_frame_def]) >>
      qpat_assum `!a len. a+len <= b \/ b+n <= a ==> _`
        (qspecl_then [`i`,`1`] mp_tac) >>
      (impl_tac >-
        (irule (DECIDE ``!b i n:num.
          ~(b <= i /\ i < b+n) ==> i+1 <= b \/ b+n <= i``) >> simp[])) >> simp[])
  >- (qx_gen_tac `i` >> strip_tac >>
      `~(b <= i /\ i < b+n)` by
        (irule (DECIDE ``!i lo b n:num.
          i < lo /\ lo <= b ==> ~(b <= i /\ i < b+n)``) >>
         qexists_tac `lo` >> simp[]) >>
      qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tn1.t_mem)`
        (qspec_then `i` mp_tac) >>
      qpat_assum `!i. _ ==> (i IN tn1.t_mem <=> i IN tn.t_mem)`
        (qspec_then `i` mp_tac) >> simp[])
  >- (qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE
          [typed_copy_state_frame_def,typed_copy_frame_def]) >>
      qpat_assum `!a len. a+len <= b \/ b+n <= a ==> _`
        (qspecl_then [`0`,`lo`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[]) >>
  fs[typed_copy_state_frame_def,venom_state_component_equality,allocas_from_def] >>
  metis_tac[]
QED

Finalise body_full_memory_stage_path
