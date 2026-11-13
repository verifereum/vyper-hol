(* The bytestring snapshot dispatch is the existing typed copy at one type. *)
Theory bodyPtrAssignBytesLiveSnapshot
Ancestors
  aggregateNormalizeBytesPtr bodyPtrAssignMemorySnapshot bodyDeclMemoryCore abiDecodeStaticProps
  context compileEnv exprLowering exprLoweringProps fragExec loweringHalt
  loweringPosts loweringStateRelDefs bodyPtrDefs exprSimProps exprSimAlloc
  valueCopyBytes vyperTypeArgFits valueEncoding valueEncodingDefs
  venomState venomInst words finite_map list arithmetic

Theorem snapshot_memory_bytes_live_counted_ptr:
  !cenv ty vv saved sa sb ctx fn cx es s G tn d D PG tv v src sw va vb.
    is_bytestring_type ty /\
    (vv = StackValue ty (Var src) \/
     ?pp. vv = LocatedValue ty pp /\ pp.ptr_location = LocMemory /\
       pp.ptr_operand = Var src) /\
    compile_snapshot_vv cenv T vv sa = (saved,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_size tv < dimword (:256) /\
    expr_val_at cenv cx ty va vb es v (Var src) s /\
    lookup_var src s = SOME sw /\ ptr_covers G tn src s (type_memory_size tv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n sw) m) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?out t H tt.
      saved = LocatedValue ty (mk_ptr (Var out) LocMemory) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
      stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es H tt t /\
      ghost_kept cenv es sa G tn s H tt /\
      expr_val_own cenv cx ty sa sb es v (Var out) t /\
      pure_frame cenv fn es sa s t /\
      ptr_covers H tt out t (type_memory_size tv) /\
      (!m. mem_agree_outside tt.t_mem t.vs_memory m ==>
        ?a. eval_operand (Var out) t = SOME a /\
          val_in_memory tv v (w2n a) m) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `vv_type vv = ty /\ !sc. unwrap_value cenv vv sc = (Var src,sc)` by
    (qpat_x_assum `vv = _ \/ _` strip_assume_tac >>
     gvs[vv_type_def, unwrap_value_def, comp_return_def]) >>
  Cases_on `compile_alloc_buffer (type_memory_size tv) sa` >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  Cases_on `compile_store_memory_typed cenv buf.buf_operand ty (Var src) ty sm` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ sm = (ans,sc)` >> Cases_on `ans` >>
  `compile_store_memory cenv (Var src) buf.buf_operand ty ty sm = ((),sc)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ sm = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, compile_store_memory_def]) >>
  `saved = LocatedValue ty (mk_ptr buf.buf_operand LocMemory) /\ sb = sc` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def, compile_materialize_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  qpat_x_assum `sb = sc` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`type_memory_size tv`,`sa`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`cenv`,`buf.buf_operand`,`ty`,`Var src`,`ty`,`sm`]
      (cj 1 ci_mono_typed_memory_family)) >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  mp_tac (Q.SPECL [`cenv`,`ctx`,`fn`,`cx`,`es`,`sa`,`sm`,`sb`,`buf`,`s`,
    `G`,`tn`,`d`,`D`,`PG`,`ty`,`ty`,`tv`,`tv`,`v`,`src`,`sw`,`va`,`vb`] aggregate_normalize_fresh_bytes_ptr) >>
  impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`root`,`b`,`u`,`H`,`tt`,`t`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >> suspend "pack"
QED

Resume snapshot_memory_bytes_live_counted_ptr[pack]:
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:256 word) = b` by simp[] >>
  `sa.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> fs[ci_mono_def]) >>
  `!name lb len. local_region cenv es.scopes t name lb len <=>
    local_region cenv es.scopes s name lb len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     map_every qx_gen_tac [`name1`,`entry`,`p`,`sz`] >> strip_tac >>
     `not_fresh_at sa p` by
       (qpat_x_assum `local_ptrs_reserved cenv sa` mp_tac >>
        simp[local_ptrs_reserved_def] >> strip_tac >> res_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))` by
    (drule body_scratch_alloc_operand >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [root])
    (fn_insts fn)` by
    (drule_all buffer_alloc_code >> fs[]) >>
  `val_footprint tv v <= type_memory_size tv` by
    (irule val_footprint_le >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_id < sb.cs_next_id` by decide_tac >>
  `!off len. regions_disjoint off len b (type_memory_size tv) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule mem_bytes_at_bytewise >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!i. i < b \/ _ <= i ==> _ /\ _` (qspec_then `i` mp_tac) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  mp_tac (Q.SPECL [`cenv`,`cx`,`fn`,`es`,`ty`,`sa`,`sb`,`s`,`t`,`tv`,`v`,
    `root`,`n2w b`,`sa.cs_next_id`,`type_memory_size tv`]
    snapshot_fresh_buffer_owned_frame) >>
  impl_tac >- (fs[eval_operand_def] >> first_assum ACCEPT_TAC) >> strip_tac >>
  `saved = LocatedValue ty (mk_ptr (Var root) LocMemory)` by metis_tac[] >>
  qexistsl_tac [`root`,`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> qexists_tac `n2w b` >> simp[eval_operand_def]
QED

Finalise snapshot_memory_bytes_live_counted_ptr
