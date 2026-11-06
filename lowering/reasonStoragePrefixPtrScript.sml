(* Located storage/transient source frames for the shared reason prefix. *)
Theory reasonStoragePrefixPtr
Ancestors
  storageNormalizationOwnershipPtr reasonPrefixPtr reasonPrefixResourcesPtr
  bodyPtrDefs loweringPosts allocationPtr reasonAllocationFramePtr
  exprSimAlloc exprSimProps exprLoweringProps loweringHalt compileEnv
  context venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words typedCopyPtr emitHelperProps exprSimHash venomInstProofs
  ghostPcTransportPtr instIdxIndep fragGasPathPtr emitHelper fragExecPtr codegenRel fragExec

Theorem reason_storage_alloc_buffer_resources:
  !ctx func cenv cx es s cc cd buf n ty tv p t' PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
    local_ptrs_reserved cenv cc /\ fn_inst_ids_distinct func /\
    n < dimword(:256) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s ==>
    ?s1 out w G1 tn1.
      buf.buf_operand = Var out /\
      step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
      stmt_state_rel ctx func cenv cx es s1 /\
      local_ptrs_reserved cenv cd /\
      G1 = step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s1 /\
      tn1 = step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
      FLOOKUP s1.vs_allocas cc.cs_next_id = SOME (w2n w,n) /\
      w2n w+n < dimword(:256) /\ eval_operand (Var out) s1 = SOME w /\
      ptr_covers G1 tn1 out s1 n /\
      (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
        ptr_covers G1 tn1 old s1 k) /\
      eval_operand p.ptr_operand s1 = eval_operand p.ptr_operand s /\
      ptr_vv_ok cx ty tv (LocatedValue t' p) es G1 tn1 s1 /\
      (!tr sty stv a. storage_holds cx tr sty stv a es s ==>
        storage_holds cx tr sty stv a es s1) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP s1.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < cc.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) n b len) /\
      (!name b len. local_region cenv es.scopes s1 name b len ==>
        regions_disjoint (w2n w) n b len) /\
      MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
      not_local_ptr cenv es.scopes out /\
      (!old. not_fresh_at cc old ==>
        FLOOKUP G1 old = FLOOKUP G old /\
        op_taint tn1 (Var old) = op_taint tn (Var old))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rename1 `buf.buf_operand = Var out` >>
  `out = STRING #"%" (toString cc.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `!x. p.ptr_operand = Var x ==> x <> out` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func)` by metis_tac[] >>
  `eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
   ptr_vv_ok cx ty tv (LocatedValue t' p) es
     (step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) t)
     (step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn) t` by
    (irule normalization_alloca_located_storage >> metis_tac[]) >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >>
     drule compile_alloc_buffer_parts >> simp[]) >>
  qexistsl_tac [`t`, `out`, `w`,
    `step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) t`,
    `step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[])
  >- (rpt strip_tac >> irule normalization_alloca_storage_holds >> metis_tac[])
  >- (qspecl_then [`cenv`, `cc`, `es.scopes`, `cc.cs_next_var`] mp_tac
        local_ptrs_reserved_fresh >> simp[]) >>
  gen_tac >> disch_tac >>
  `old <> out` by (gvs[not_fresh_at_def] >> metis_tac[]) >>
  drule_all reason_alloca_old_metadata >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >>
  gvs[]
QED

(* A memory write cannot alter a located storage source or its key taints. *)
Theorem reason_storage_mstore_source:
  !cx ty tv p t' es PG G tn s id dst a value w.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s ==>
    eval_operand p.ptr_operand (mstore (w2n a) w s) =
      eval_operand p.ptr_operand s /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn) (mstore (w2n a) w s) /\
    (!tr sty stv base. storage_holds cx tr sty stv base es s ==>
      storage_holds cx tr sty stv base es (mstore (w2n a) w s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  gvs[ptr_vv_ok_def, op_taint_def, mstore_def, eval_operand_def,
      lookup_var_def, storage_holds_def, contract_storage_def,
      contract_transient_def]
QED

Theorem reason_storage_allocated_mstore_state_rel:
  !ctx func cenv cx es s inst b n a w.
    stmt_state_rel ctx func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
    b <= a /\ a + 32 <= b + n /\
    (!name off len. local_region cenv es.scopes s name off len ==>
      regions_disjoint b n off len) ==>
    stmt_state_rel ctx func cenv cx es (mstore a w s)
Proof
  rpt strip_tac >> irule literal_mstore_state_rel >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`b`, `inst`, `n`] >>
  gvs[regions_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem reason_storage_add_source:
  !ctx func cenv cx es s cc cd src result a d ty tv p t' PG G tn.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv cc /\
    emit_op ADD [src; Lit d] cc = (result,cd) /\
    eval_operand src s = SOME a /\
    (!z. p.ptr_operand = Var z ==> not_fresh_at cc z) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s ==>
    ?u x G1 tn1.
      result = Var x /\ ~not_fresh_at cc x /\
      u = update_var x (a+d) s /\
      step_inst_base (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s = OK u /\
      run_inst_seq (emitted_insts cc cd) s = OK u /\
      G1 = step_prov PG G (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) u /\
      tn1 = step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s u tn /\
      stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv cd /\
      eval_operand result u = SOME (a+d) /\
      eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
      ptr_vv_ok cx ty tv (LocatedValue t' p) es G1 tn1 u /\
      (!tr sty stv base. storage_holds cx tr sty stv base es s ==>
        storage_holds cx tr sty stv base es u) /\
      u.vs_allocas = s.vs_allocas /\
      (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
        ptr_covers G1 tn1 old u k) /\
      (!old. not_fresh_at cc old ==> FLOOKUP G1 old = FLOOKUP G old /\
        op_taint tn1 (Var old) = op_taint tn (Var old))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `result = Var x` >>
  `~not_fresh_at cc x` by simp[Abbr `x`, not_fresh_at_def] >>
  `not_local_ptr cenv es.scopes x` by
    (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var x (a+d) s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >> simp[]) >>
  `step_inst_base (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s =
     OK (update_var x (a+d) s)` by (irule step_ADD >> simp[eval_operand_def]) >>
  `eval_operand p.ptr_operand (update_var x (a+d) s) = eval_operand p.ptr_operand s` by
    (Cases_on `p.ptr_operand` >> simp[eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  qexistsl_tac [`update_var x (a+d) s`, `x`,
    `step_prov PG G (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) (update_var x (a+d) s)`,
    `step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s (update_var x (a+d) s) tn`] >>
  asm_rewrite_tac[] >> simp[run_inst_seq_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt conj_tac >- suspend "source" >- suspend "holds"
  >- suspend "covers" >>
  rpt strip_tac >> `old <> x` by metis_tac[] >>
  gvs[SRULE [update_var_def] copy_len_binop_ghost_frame]
QED

Resume reason_storage_add_source[source]:
  `op_taint (step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s
     (update_var x (a+d) s) tn) p.ptr_operand = op_taint tn p.ptr_operand` by
    (Cases_on `p.ptr_operand`
     >- simp[op_taint_def]
     >- (rename1 `p.ptr_operand = Var old` >>
         `old <> x` by metis_tac[] >> simp[copy_len_binop_ghost_frame]) >>
     simp[op_taint_def]) >>
  gvs[ptr_vv_ok_def, SRULE [update_var_def] copy_len_binop_ghost_frame, update_var_def]
QED

Resume reason_storage_add_source[holds]:
  simp[storage_holds_def, contract_storage_def, contract_transient_def, update_var_def]
QED

Resume reason_storage_add_source[covers]:
  rpt strip_tac >> `old <> x` by metis_tac[] >>
  gvs[ptr_covers_def, SRULE [update_var_def] copy_len_binop_ghost_frame,
      lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Finalise reason_storage_add_source

(* The selector write keeps the registered allocation and all located-source
   resources; its ghost changes only memory taint. *)
Theorem reason_storage_selector_resources:
  !ctx func cenv cx es s cc cd buf out b n aid ty tv p t' G tn.
    stmt_state_rel ctx func cenv cx es s /\
    emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] cc = ((),cd) /\
    buf.buf_operand = Var out /\ lookup_var out s = SOME (n2w b) /\
    b+n < dimword(:256) /\ 32 <= n /\
    MEM (mk_inst aid ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    FLOOKUP s.vs_allocas aid = SOME (b,n) /\
    (!name off len. local_region cenv es.scopes s name off len ==>
      regions_disjoint b n off len) /\
    local_ptrs_reserved cenv cc /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s ==>
    ?u tn1.
      u = mstore b 0x08c379a0w s /\
      run_inst_seq (emitted_insts cc cd) s = OK u /\
      step_inst_base (mk_inst cc.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) s = OK u /\
      tn1 = step_taint (mk_inst cc.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) s u tn /\
      stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv cd /\
      eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
      ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn1 u /\
      (!tr sty stv base. storage_holds cx tr sty stv base es s ==>
        storage_holds cx tr sty stv base es u) /\
      u.vs_allocas = s.vs_allocas /\
      (!old k. ptr_covers G tn old s k ==> ptr_covers G tn1 old u k) /\
      (!PG. step_prov PG G (mk_inst cc.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) u = G)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  `step_inst_base (mk_inst cc.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) s =
     OK (mstore b 0x08c379a0w s)` by
    (qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule step_MSTORE >> simp[eval_operand_def]) >>
  `run_inst_seq (emitted_insts cc cd) s = OK (mstore b 0x08c379a0w s)` by
    (drule emitted_insts_emit_void >> strip_tac >> simp[run_inst_seq_def]) >>
  `stmt_state_rel ctx func cenv cx es (mstore b 0x08c379a0w s)` by
    (irule reason_storage_allocated_mstore_state_rel >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`b`, `mk_inst aid ALLOCA [Lit (n2w n)] [out]`, `n`] >>
     asm_rewrite_tac[] >> simp[mk_inst_def]) >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >> simp[] >>
     drule emitted_insts_emit_void >> simp[]) >>
  qexistsl_tac [`mstore b 0x08c379a0w s`,
    `step_taint (mk_inst cc.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) s
      (mstore b 0x08c379a0w s) tn`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- suspend "source_eval"
  >- suspend "source_ptr"
  >- suspend "source_holds"
  >- simp[mstore_def]
  >- suspend "covers" >> suspend "prov"
QED

Resume reason_storage_selector_resources[source_eval]:
  simp[eval_operand_mstore]
QED

Resume reason_storage_selector_resources[source_ptr]:
  `eval_operand (Lit 0x08c379a0w) s = SOME 0x08c379a0w /\
   op_taint tn (Lit 0x08c379a0w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all reason_storage_mstore_source >>
  disch_then (qspecl_then [`ARB`, `cc.cs_next_id`] mp_tac) >> simp[]
QED

Resume reason_storage_selector_resources[source_holds]:
  simp[storage_holds_def, contract_storage_def, contract_transient_def, mstore_def]
QED

Resume reason_storage_selector_resources[covers]:
  `eval_operand (Lit 0x08c379a0w) s = SOME 0x08c379a0w /\
   op_taint tn (Lit 0x08c379a0w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`, `G`, `cc.cs_next_id`] mp_tac) >>
  simp[] >> strip_tac >> rpt strip_tac >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def,
      write_memory_with_expansion_def]
QED

Resume reason_storage_selector_resources[prov]:
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def, finite_mapTheory.DRESTRICT_UNIV]
QED

Finalise reason_storage_selector_resources

Theorem reason_storage_encoder_prefix_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  compile_alloc_buffer n cc = (buf,c1) /\
  emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
  emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
  compile_alloc_buffer m c3 = (tuple,c4) /\
  fn_has_code cc c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  local_ptrs_reserved cenv cc /\ 32 <= n /\ n < dimword(:256) /\
  m < dimword(:256) /\
  (!z. p.ptr_operand = Var z ==> not_fresh_at cc z) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s
  ==>
  ?t out x out2 b b2 Gf tnf.
    buf.buf_operand = Var out /\ payload = Var x /\
    tuple.buf_operand = Var out2 /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = c4.cs_current_bb /\
    t.vs_inst_idx = LENGTH c4.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv c4 /\
    lookup_var out t = SOME (n2w b) /\
    lookup_var x t = SOME (n2w b + 32w) /\
    lookup_var out2 t = SOME (n2w b2) /\
    b+n < dimword(:256) /\ b2+m < dimword(:256) /\
    ptr_covers Gf tnf out t n /\ ptr_covers Gf tnf x t (n-32) /\
    ptr_covers Gf tnf out2 t m /\
    FLOOKUP t.vs_allocas cc.cs_next_id = SOME (b,n) /\
    FLOOKUP t.vs_allocas c3.cs_next_id = SOME (b2,m) /\
    MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    MEM (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) (fn_insts func) /\
    not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes out2 /\
    (!z. MEM z [out;x;out2] ==> not_fresh_at c4 z) /\
    eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es Gf tnf t /\
    (!tr sty stv a. storage_holds cx tr sty stv a es s ==>
      storage_holds cx tr sty stv a es t) /\
    (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
      ptr_covers Gf tnf old t k) /\
    (!old. not_fresh_at cc old ==> FLOOKUP Gf old = FLOOKUP G old /\
      op_taint tnf (Var old) = op_taint tn (Var old))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all reason_storage_alloc_buffer_resources >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `lookup_var out s1 = SOME (n2w (w2n w))` by gvs[eval_operand_def] >>
  drule_all reason_storage_selector_resources >> strip_tac >>
  `!z. p.ptr_operand = Var z ==> not_fresh_at c2 z` by
    (qpat_assum `compile_alloc_buffer n cc = _` (mp_tac o MATCH_MP compile_alloc_buffer_parts) >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     rpt strip_tac >>
     `not_fresh_at c1 z` by metis_tac[] >>
     fs[not_fresh_at_def]) >>
  `eval_operand buf.buf_operand u = SOME w` by
    gvs[eval_operand_mstore] >>
  drule_all reason_storage_add_source >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!z. p.ptr_operand = Var z ==> not_fresh_at c3 z` by
    (drule emitted_insts_emit_op >> strip_tac >>
     rpt strip_tac >>
     qpat_x_assum `!z. p.ptr_operand = Var z ==> not_fresh_at c2 z`
       (qspec_then `z` mp_tac) >>
     simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all reason_storage_alloc_buffer_resources >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `tuple.buf_operand = Var out2` >>
  rename1 `FLOOKUP s1'.vs_allocas c3.cs_next_id = SOME (w2n w2,m)` >>
  rename1 `ptr_vv_ok cx ty tv (LocatedValue t' p) es Gf tnf s1'` >>
  `(!old. not_fresh_at cc old ==> not_fresh_at c2 old) /\
   (!old. not_fresh_at c2 old ==> not_fresh_at c3 old) /\
   (!z. MEM z [out;x;out2] ==> not_fresh_at c4 z) /\
   not_fresh_at c2 out /\ not_fresh_at c3 x` by suspend "names" >>
  `ptr_covers G1 tn1' out u n` by metis_tac[] >>
  `ptr_covers G1' tn1'' out u' n` by metis_tac[] >>
  `ptr_covers G1' tn1'' x u' (n-32)` by suspend "offset" >>
  `lookup_var out s1' = SOME w /\ lookup_var x s1' = SOME (w+32w)` by
    suspend "values" >>
  `s1'.vs_current_bb = c4.cs_current_bb /\ ~s1'.vs_halted` by suspend "control" >>
  qexistsl_tac [`s1' with vs_inst_idx := LENGTH c4.cs_current_insts`,
    `out`, `x`, `out2`, `w2n w`, `w2n w2`, `Gf`, `tnf`] >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  asm_rewrite_tac[] >> suspend "endpoint"
QED

Resume reason_storage_encoder_prefix_path_ptr[names]:
  map_every (fn q => qpat_assum q mp_tac)
    [`compile_alloc_buffer n cc = _`, `compile_alloc_buffer m c3 = _`,
     `emit_void MSTORE _ c1 = _`, `emit_op ADD _ c2 = _`,
     `buf.buf_operand = Var out`, `payload = Var x`, `tuple.buf_operand = Var out2`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac compile_alloc_buffer_parts >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_ADD]
QED

Resume reason_storage_encoder_prefix_path_ptr[offset]:
  map_every (fn q => qpat_assum q mp_tac)
    [`G1' = _`, `tn1'' = _`, `u' = _`, `buf.buf_operand = Var out`,
     `ptr_covers G1 tn1' out u n`, `eval_operand buf.buf_operand u = SOME w`,
     `w2n w + n < _`, `32 <= n`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  asm_rewrite_tac[] >> irule reason_encoder_offset_covers >>
  rpt conj_tac >- decide_tac >- gvs[eval_operand_def] >>
  qexists_tac `n` >> simp[]
QED

Resume reason_storage_encoder_prefix_path_ptr[values]:
  `out <> x` by (strip_tac >> fs[]) >>
  `lookup_var out u' = SOME w` by
    (map_every (fn q => qpat_assum q mp_tac)
      [`u' = _`, `u = _`, `lookup_var out s1 = _`, `out <> x`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[lookup_var_def, update_var_def, mstore_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  `not_fresh_at c3 out` by metis_tac[] >>
  qpat_assum `compile_alloc_buffer m c3 = _`
    (mp_tac o MATCH_MP compile_alloc_buffer_parts) >> strip_tac >>
  `out <> out2 /\ x <> out2` by
    (map_every (fn q => qpat_assum q mp_tac)
      [`tuple.buf_operand = Var out2`,
       `tuple.buf_operand = Var (STRING _ _)`,
       `not_fresh_at c3 out`, `not_fresh_at c3 x`,
       `~not_fresh_at c3 _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qspecl_then [`c3.cs_next_id`, `n2w m`, `out2`, `u'`] strip_assume_tac step_alloca_frame >>
  `s1' = s1''` by
    (qpat_assum `step_inst_base _ u' = OK s1'` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  map_every (fn q => qpat_assum q mp_tac)
    [`s1' = s1''`, `!z. z <> out2 ==> lookup_var z s1'' = _`,
     `out <> out2`, `x <> out2`, `lookup_var out u' = SOME w`,
     `eval_operand payload u' = _`, `payload = Var x`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[eval_operand_def]
QED

Resume reason_storage_encoder_prefix_path_ptr[control]:
  drule_all reason_encoder_prefix_code >> strip_tac >>
  map_every (fn q => qpat_assum q mp_tac)
    [`c4.cs_current_bb = _`, `s.vs_current_bb = _`, `~s.vs_halted`] >>
  rpt (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `!id opc ops outs a b.
     step_inst_base (mk_inst id opc ops outs) a = OK b ==>
     opc <> INVOKE /\ ~is_terminator opc ==>
     b.vs_current_bb = a.vs_current_bb /\ b.vs_halted = a.vs_halted` by
    (rpt gen_tac >> disch_tac >> strip_tac >>
     `step_inst 0 ctx (mk_inst id opc ops outs) a = OK b` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     conj_tac >- (drule step_preserves_control_flow >> simp[mk_inst_def]) >>
     drule step_preserves_halted >> simp[mk_inst_def]) >>
  qpat_x_assum `!id opc ops outs a b. _` imp_res_tac >>
  fs[is_terminator_def]
QED

Resume reason_storage_encoder_prefix_path_ptr[endpoint]:
  conj_tac >- suspend "path" >>
  `FLOOKUP s1'.vs_vars out = SOME w /\
   FLOOKUP s1'.vs_vars x = SOME (w+32w) /\
   FLOOKUP s1'.vs_vars out2 = SOME w2` by
    (rpt (qpat_x_assum `lookup_var _ s1' = _` mp_tac) >>
     qpat_assum `eval_operand (Var out2) s1' = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[eval_operand_def, lookup_var_def]) >>
  asm_rewrite_tac[] >> conj_tac >- suspend "source_ptr" >>
  conj_tac >- suspend "holds" >> suspend "metadata"
QED

Resume reason_storage_encoder_prefix_path_ptr[source_ptr]:
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ Gf tnf s1'` mp_tac >>
  asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def, lookup_var_def]
QED

Resume reason_storage_encoder_prefix_path_ptr[holds]:
  rpt strip_tac >>
  `storage_holds cx tr sty stv a es s1'` by metis_tac[] >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp[storage_holds_def, contract_storage_def,
    contract_transient_def, eval_operand_def, lookup_var_def]
QED

Resume reason_storage_encoder_prefix_path_ptr[metadata]:
  qpat_x_assum `!old. not_fresh_at cc old ==> FLOOKUP G1 old = _ /\ _` mp_tac >>
  asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, op_taint_def,
    finite_mapTheory.DRESTRICT_UNIV]
QED

Resume reason_storage_encoder_prefix_path_ptr[path]:
  `c1.cs_current_bb = cc.cs_current_bb /\
   c2.cs_current_bb = cc.cs_current_bb /\ c3.cs_current_bb = cc.cs_current_bb /\
   LENGTH c1.cs_current_insts = SUC (LENGTH cc.cs_current_insts) /\
   LENGTH c2.cs_current_insts = SUC (LENGTH c1.cs_current_insts) /\
   LENGTH c3.cs_current_insts = SUC (LENGTH c2.cs_current_insts) /\
   LENGTH c4.cs_current_insts = SUC (LENGTH c3.cs_current_insts)` by suspend "layout" >>
  `s1.vs_current_bb = cc.cs_current_bb /\ ~s1.vs_halted /\
   u.vs_current_bb = cc.cs_current_bb /\ ~u.vs_halted /\
   u'.vs_current_bb = cc.cs_current_bb /\ ~u'.vs_halted` by suspend "fields" >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1
     (OK (s1 with vs_inst_idx := LENGTH c1.cs_current_insts))` by suspend "edge1" >>
  `gas_path_ptr D 0 ctx func PG G1 tn1
     (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) 0 G1 tn1'
     (OK (u with vs_inst_idx := LENGTH c2.cs_current_insts))` by suspend "edge2" >>
  `gas_path_ptr D 0 ctx func PG G1 tn1'
     (u with vs_inst_idx := LENGTH c2.cs_current_insts) 0 G1' tn1''
     (OK (u' with vs_inst_idx := LENGTH c3.cs_current_insts))` by suspend "edge3" >>
  `gas_path_ptr D 0 ctx func PG G1' tn1''
     (u' with vs_inst_idx := LENGTH c3.cs_current_insts) 0 Gf tnf
     (OK (s1' with vs_inst_idx := LENGTH c4.cs_current_insts))` by suspend "edge4" >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
     (OK (s1' with vs_inst_idx := LENGTH c4.cs_current_insts))` by
    (rpt (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)]) >>
  pop_assum mp_tac >> asm_rewrite_tac[]
QED

Resume reason_storage_encoder_prefix_path_ptr[layout]:
  map_every (fn q => qpat_assum q mp_tac)
    [`compile_alloc_buffer n cc = _`, `compile_alloc_buffer m c3 = _`,
     `emit_void MSTORE _ c1 = _`, `emit_op ADD _ c2 = _`] >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Resume reason_storage_encoder_prefix_path_ptr[fields]:
  map_every (fn q => qpat_assum q mp_tac)
    [`s.vs_current_bb = _`, `~s.vs_halted`] >>
  rpt (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `!id opc ops outs a b.
     step_inst_base (mk_inst id opc ops outs) a = OK b ==>
     opc <> INVOKE /\ ~is_terminator opc ==>
     b.vs_current_bb = a.vs_current_bb /\ b.vs_halted = a.vs_halted` by
    (rpt gen_tac >> disch_tac >> strip_tac >>
     `step_inst 0 ctx (mk_inst id opc ops outs) a = OK b` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     conj_tac >- (drule step_preserves_control_flow >> simp[mk_inst_def]) >>
     drule step_preserves_halted >> simp[mk_inst_def]) >>
  qpat_x_assum `!id opc ops outs a b. _` imp_res_tac >>
  fs[is_terminator_def]
QED

Resume reason_storage_encoder_prefix_path_ptr[edge1]:
  drule_all reason_encoder_alloc_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >>
  asm_rewrite_tac[]
QED

Resume reason_storage_encoder_prefix_path_ptr[edge2]:
  `ptr_covers G1 tn1 out s1 32` by
    (qpat_assum `ptr_covers G1 tn1 out s1 n` mp_tac >>
     qpat_assum `32 <= n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `emit_inst MSTORE [Var out; Lit 0x08c379a0w] [] c1 = ((),c2)` by
    (qpat_x_assum `emit_void MSTORE _ c1 = _` mp_tac >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
     simp[emit_void_def, emit_inst_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1
     (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [])
     (s1 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  `step_inst_base (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [])
     (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
     OK (u with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_x_assum `step_inst_base _ s1 = OK u` mp_tac >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
     simp[step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  `MSTORE <> INVOKE /\ MSTORE <> GAS /\ ~is_terminator MSTORE` by
    simp[is_terminator_def] >>
  `s1.vs_current_bb = c1.cs_current_bb` by simp[] >>
  `(s1 with vs_inst_idx := LENGTH c1.cs_current_insts).vs_current_bb = c1.cs_current_bb /\
   (s1 with vs_inst_idx := LENGTH c1.cs_current_insts).vs_inst_idx = LENGTH c1.cs_current_insts /\
   ~(s1 with vs_inst_idx := LENGTH c1.cs_current_insts).vs_halted` by simp[] >>
  drule_all reason_encoder_emit_path_ptr >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[] >> asm_rewrite_tac[]
QED

Resume reason_storage_encoder_prefix_path_ptr[edge3]:
  `emit_inst ADD [buf.buf_operand; Lit 32w] [x]
     (c2 with cs_next_var := c2.cs_next_var+1) = ((),c3)` by
    (qpat_x_assum `emit_op ADD _ c2 = _` mp_tac >>
     qpat_assum `payload = Var x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `op_taint tn1' (Var out) = {}` by
    (qpat_assum `ptr_covers G1 tn1' out u n` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptr_covers_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1'
     (mk_inst c2.cs_next_id ADD [buf.buf_operand; Lit 32w] [x])
     (u with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `op_taint tn1' (Var out) = {}` mp_tac >>
     qpat_assum `buf.buf_operand = Var out` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     asm_rewrite_tac[] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base (mk_inst c2.cs_next_id ADD [buf.buf_operand; Lit 32w] [x])
     (u with vs_inst_idx := LENGTH c2.cs_current_insts) =
     OK (u' with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_x_assum `step_inst_base _ u = OK u'` mp_tac >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
     simp[step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  `fn_has_code (c2 with cs_next_var := c2.cs_next_var+1) c3 func` by
    (qpat_x_assum `fn_has_code c2 c3 func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[fn_has_code_def, emitted_blocks_def]) >>
  `(u with vs_inst_idx := LENGTH c2.cs_current_insts).vs_current_bb =
       (c2 with cs_next_var := c2.cs_next_var+1).cs_current_bb /\
   (u with vs_inst_idx := LENGTH c2.cs_current_insts).vs_inst_idx =
       LENGTH (c2 with cs_next_var := c2.cs_next_var+1).cs_current_insts /\
   ~(u with vs_inst_idx := LENGTH c2.cs_current_insts).vs_halted` by simp[] >>
  `ADD <> INVOKE /\ ADD <> GAS /\ ~is_terminator ADD` by simp[is_terminator_def] >>
  `(u with vs_inst_idx := LENGTH c2.cs_current_insts).vs_current_bb = c2.cs_current_bb /\
   (u with vs_inst_idx := LENGTH c2.cs_current_insts).vs_inst_idx = LENGTH c2.cs_current_insts` by simp[] >>
  drule_then (drule_all o SRULE []) reason_encoder_emit_path_ptr >>
  disch_then (qspec_then `PG` mp_tac) >> simp[] >> asm_rewrite_tac[]
QED

Resume reason_storage_encoder_prefix_path_ptr[edge4]:
  `step_inst_base (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2])
     (u' with vs_inst_idx := LENGTH c3.cs_current_insts) =
     OK (s1' with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (qpat_x_assum `step_inst_base _ u' = OK s1'` mp_tac >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
     simp[step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  `(u' with vs_inst_idx := LENGTH c3.cs_current_insts).vs_current_bb = c3.cs_current_bb /\
   (u' with vs_inst_idx := LENGTH c3.cs_current_insts).vs_inst_idx = LENGTH c3.cs_current_insts /\
   ~(u' with vs_inst_idx := LENGTH c3.cs_current_insts).vs_halted` by simp[] >>
  qpat_x_assum `compile_alloc_buffer n cc = _` kall_tac >>
  qpat_x_assum `step_inst_base _ u' = OK s1'` kall_tac >>
  drule_all reason_encoder_alloc_path_ptr >>
  disch_then (qspecl_then [`tn1''`, `PG`, `G1'`, `D`] mp_tac) >>
  simp[] >> asm_rewrite_tac[]
QED

Finalise reason_storage_encoder_prefix_path_ptr
