Theory tuplePlaceOwnedNormalize
Ancestors
  tuplePlaceTypedSize tuplePlaceStore tuplePlaceStaging placeMemoryCopyEffect
  exprSimCopy exprSimAlloc exprSimStorageCopy placeStoreStorage
  freshWrites fragGasMode venomState compileEnv loweringPosts context
  exprLoweringProps stmtSimDefs bodyMemoryDefs venomMemDefs

Theorem tuple_place_owned_normalize_frame:
  !cenv cx ctx func es sa sm sc buf dty sty dtv stv v src sw s.
    compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
    compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sc) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    type_memory_size stv + 64 < dimword (:256) /\
    type_memory_size dtv + 64 < dimword (:256) /\
    (?aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id /\ b <= w2n sw /\
      w2n sw + type_memory_size stv <= b+len) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t dw. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME dw /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      t.vs_labels = s.vs_labels /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      (!aid b len a n. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
        aid < sa.cs_next_id /\ b <= a /\ a + n <= b + len ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sm` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by gvs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all place_store_alloc_buffer_path >>
  disch_then (qx_choose_then `u` (qx_choose_then `w`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qpat_x_assum `?p. buf.buf_operand = Var p /\ not_fresh_at sm p`
    strip_assume_tac >>
  `eval_operand src u = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
  `alloca_inv u` by metis_tac[stmt_state_rel_def] >>
  Q.SUBGOAL_THEN
    `w2n sw + type_memory_size stv <= w2n w \/
     w2n w + type_memory_size dtv <= w2n sw` assume_tac
  >- (`aid <> sa.cs_next_id` by decide_tac >>
      qpat_x_assum `alloca_inv u` mp_tac >>
      rewrite_tac[alloca_inv_def, allocas_non_overlapping_def] >> strip_tac >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >>
      simp[] >> decide_tac) >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  `type_memory_bytes cenv sty = type_memory_size stv /\
   type_memory_bytes cenv dty = type_memory_size dtv` by metis_tac[] >>
  drule_all tuple_place_typed_size_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `typed_copy_effect _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_effect_def]) >>
  `exprSimStorageCopy$copy_static t = exprSimStorageCopy$copy_static u` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[copy_static_def, venom_state_component_equality]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx es t` by suspend "state" >>
  `!aid b len a n. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
     aid < sa.cs_next_id /\ b <= a /\ a + n <= b + len ==>
     mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    suspend "bytes" >>
  qexistsl_tac [`t`, `w`] >> suspend "post"
QED

Resume tuple_place_owned_normalize_frame[state]:
  markerLib.RESUME_TAC >>
  drule_all buffer_alloc_code >> strip_tac >>
  `!name lb len. local_region cenv es.scopes u name lb len ==>
     w2n w + type_memory_size dtv <= lb \/ lb + len <= w2n w` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. _` drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`w2n w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
       [STRING #"%" (toString sa.cs_next_var)]`, `u`, `sm`, `type_memory_size dtv`] >>
  asm_rewrite_tac[venomInstTheory.mk_inst_def] >> simp[]
QED

Resume tuple_place_owned_normalize_frame[bytes]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `regions_disjoint (w2n w) (type_memory_size dtv) b' len'` by
    (qpat_x_assum `!aid b len. _` drule_all >> simp[]) >>
  `a + n <= w2n w \/ w2n w + type_memory_size dtv <= a` by
    (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!a len. _` (qspecl_then [`a`, `n`] mp_tac) >> simp[]
QED

Resume tuple_place_owned_normalize_frame[post]:
  markerLib.RESUME_TAC >>
  drule_all copy_static_fields >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     metis_tac[]) >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >> metis_tac[eval_operand_def]
QED
Finalise tuple_place_owned_normalize_frame
