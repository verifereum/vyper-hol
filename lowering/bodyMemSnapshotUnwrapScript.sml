(* Framed counted materialisation of non-memory aggregate values. *)
Theory bodyMemSnapshotUnwrap
Ancestors
  bodyMemAggregateMaterialise exprSimMemUnwrap exprSimStorageCopy exprSimCopy
  exprSimProps exprSimMemDefs exprLoweringProps freshWrites valueEncodingProps
  loweringPosts fragGasPathMem exprLowering context compileEnv
  loweringStateRelDefs exprSimAlloc fragExec bodyImmutableUnwrapMemory
  venomExecSemantics venomInst venomState

Theorem snapshot_copy_frame[local]:
  !cenv func ee sm s u z b sz ops outs.
    local_ptrs_reserved cenv sm /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_memory = s.vs_memory /\ copy_static z = copy_static u /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,sz) /\
    MEM (mk_inst sm.cs_next_id ALLOCA ops outs) (fn_insts func) /\
    (!n lb len. local_region cenv ee.scopes u n lb len ==>
       regions_disjoint b sz lb len) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) ==>
    pure_frame cenv func ee sm s z
Proof
  rpt gen_tac >> strip_tac >> drule copy_static_fields >> strip_tac >>
  irule pure_frame_fresh_alloca >>
  reverse conj_tac
  >- (qexistsl_tac [`b`, `sm.cs_next_id`, `ops`, `outs`, `sz`] >>
      simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
      `local_region cenv ee.scopes u n lb lsz` by
        metis_tac[copy_buffer_local_region_frame] >>
      `regions_disjoint b sz lb lsz` by metis_tac[] >>
      fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem snapshot_storage_unwrap_mem[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?z w tvt. gas_path_mem ctx func s 0 (OK z) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
      evaluate_type (get_tenv cx) t = SOME tvt /\ eval_operand op z = SOME w /\
      w2n w + type_memory_size tvt <= z.vs_alloca_next /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP z.vs_allocas aid = SOME entry) /\
      pure_frame cenv func ee sm s z /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ ~z.vs_halted /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_unwrap_layout_facts >> strip_tac >>
  drule_all storage_unwrap_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a ee u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >> simp[storage_holds_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256 /\
   w2n w + 32 * type_slot_size tv <= u.vs_alloca_next` by
    fs[type_memory_size_slots, wordsTheory.dimword_def] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all storage_unwrap_typed_suffix_path_mem >> strip_tac >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v buf.buf_operand z` by
    (irule buffer_post_transport >> simp[] >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `tv`, `u`] >>
     qpat_assum `t = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
     simp[arithmeticTheory.ADD_COMM] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `pure_frame cenv func ee sm s z` by
    (drule_all buffer_alloc_code >> strip_tac >>
     irule snapshot_copy_frame >>
     conj_tac
     >- (qexistsl_tac [`w2n w`, `type_memory_bytes cenv t`, `u`] >>
         simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >>
  conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_mem_then >> qexists_tac `u` >> simp[]) >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED
