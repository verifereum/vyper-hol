(* Located storage/transient source frames for the shared reason prefix. *)
Theory reasonStoragePrefixPtr
Ancestors
  storageNormalizationOwnershipPtr reasonPrefixPtr reasonPrefixResourcesPtr
  bodyPtrDefs loweringPosts allocationPtr reasonAllocationFramePtr
  exprSimAlloc exprSimProps exprLoweringProps loweringHalt compileEnv
  context venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words typedCopyPtr emitHelperProps exprSimHash

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
