(* The post-allocation RawCreate copy from a physical immutable offset. *)
Theory bodyCreateRawCodeRunMods
Ancestors
  bodyForArraySnapshotCodeRunMods abiCanonicalHeadSize memoryReadProps
  typedMemoryCopy exprSimCopy fragGasOriginPtrDead venomState
  valueEncodingDefs words arithmetic finite_map pred_set ptrDiscipline

Triviality raw_code_copy_slice:
  mem_bytes_at dst cap mem' = mem_bytes_at src cap mem /\ n + off <= cap ==>
  mem_bytes_at (dst + off) n mem' = mem_bytes_at (src + off) n mem
Proof
  strip_tac >>
  qpat_assum `mem_bytes_at _ _ _ = _`
    (mp_tac o Q.AP_TERM `\xs. TAKE n (DROP off xs)`) >>
  simp[abiCanonicalHeadSizeTheory.mem_bytes_at_window, ADD_COMM]
QED

Triviality raw_code_copy_contents:
  mem_bytes_at dst cap u.vs_memory = mem_bytes_at src cap mem /\
  32 + LENGTH bs <= cap /\
  word_of_bytes T (0w:bytes32) (mem_bytes_at src 32 mem) = n2w (LENGTH bs) /\
  mem_bytes_at (src + 32) (LENGTH bs) mem = bs ==>
  mload dst u = n2w (LENGTH bs) /\ read_memory (dst + 32) (LENGTH bs) u = bs
Proof
  strip_tac >>
  `mem_bytes_at dst 32 u.vs_memory = mem_bytes_at src 32 mem` by
    (`mem_bytes_at (dst + 0) 32 u.vs_memory = mem_bytes_at (src + 0) 32 mem`
       suffices_by simp[] >>
     irule raw_code_copy_slice >> qexists `cap` >> simp[] >> decide_tac) >>
  simp[mload_def, GSYM mem_bytes_at_def, read_memory_eq_mem_bytes_at] >>
  `LENGTH bs + 32 <= cap` by decide_tac >>
  drule_all raw_code_copy_slice >> simp[]
QED

Theorem raw_create_code_run_mods:
  compile_imm_copy_to_memory ctor imm src (Var owner) q 0 m = ((),b) /\
  copy_old_operand m src /\ not_fresh_at m owner /\
  eval_operand src j = SOME w /\ lookup_var owner j = SOME (n2w pbase) /\
  op_taint tj src = {} /\ ptr_covers Gj tj owner j cap /\
  32*q = cap /\ 32 + LENGTH bs <= cap /\ pbase + cap < dimword (:256) /\
  FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  pbase + cap <= j.vs_alloca_next /\
  allocas_from lo j /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  (ctor ==> op_prov Gj src = NONE /\ w2n w + cap <= lo /\ lo <= pbase /\
     (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tj.t_mem) /\
     !region. imm = SOME region ==> eval_operand region j = SOME 0w /\
        copy_old_operand m region /\ op_taint tj region = {} /\ op_prov Gj region = NONE) /\
  (~ctor ==> w2n w + cap <= LENGTH j.vs_data_section /\
     w2n w + cap < dimword (:256)) /\
  word_of_bytes T (0w:bytes32) (mem_bytes_at (w2n w) 32
      (if ctor then j.vs_memory else j.vs_data_section)) = n2w (LENGTH bs) /\
  mem_bytes_at (w2n w + 32) (LENGTH bs)
      (if ctor then j.vs_memory else j.vs_data_section) = bs /\
  fn_has_code m b func /\ ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\
    FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
    lookup_var owner u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
    mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase + 32) (LENGTH bs) u = bs /\
    (!i. pbase <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tu.t_mem) /\
    typed_copy_state_frame m pbase cap j u /\
    typed_copy_frame pbase cap j.vs_memory u.vs_memory /\
    (!i. i < pbase \/ pbase + cap <= i ==> (i IN tu.t_mem <=> i IN tj.t_mem)) /\
    (!x. not_fresh_at m x ==> lookup_var x u = lookup_var x j /\
       FLOOKUP Gu x = FLOOKUP Gj x /\ op_taint tu (Var x) = op_taint tj (Var x)) /\
    u.vs_allocas = j.vs_allocas /\ u.vs_alloca_next = j.vs_alloca_next /\
    u.vs_data_section = j.vs_data_section /\ u.vs_accounts = j.vs_accounts /\
    u.vs_call_ctx = j.vs_call_ctx /\ u.vs_transient = j.vs_transient /\
    u.vs_immutables = j.vs_immutables /\
    tu.t_imm = tj.t_imm /\ tu.t_stor = tj.t_stor /\ tu.t_trans = tj.t_trans /\
    pbase + cap <= u.vs_alloca_next /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  `0 < q /\ pbase < dimword (:256)` by decide_tac >>
  `w2n (n2w pbase:bytes32) = pbase` by simp[LESS_MOD] >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    for_array_snapshot_code_run_mods >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  qpat_assum `w2n (n2w pbase:bytes32) = pbase`
    (fn eq => disch_then (mp_tac o PURE_REWRITE_RULE [eq])) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  `ctor ==> w2n w + cap <= j.vs_alloca_next` by
    (disch_tac >> qpat_assum `ctor ==> _ /\ _` (drule_then strip_assume_tac) >>
     decide_tac) >>
  impl_tac >- (Cases_on `ctor` >> fs[]) >>
  qpat_assum `32*q = cap` (fn eq =>
    disch_then (qx_choosel_then [`raw`,`u`,`Gu`,`tu`] strip_assume_tac o
      PURE_REWRITE_RULE [eq])) >>
  qpat_x_assum `copy_runtime_frame _ _ _ _` kall_tac >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  `(mload pbase u = n2w (LENGTH bs)) /\ read_memory (pbase + 32) (LENGTH bs) u = bs` by
    (irule raw_code_copy_contents >>
     goal_assum (drule_at (Pat `word_of_bytes _ _ _ = _`)) >>
     qexists `cap` >> simp[]) >>
  `!i. pbase <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tu.t_mem` by
    (rpt strip_tac >>
     `i < pbase + cap` by decide_tac >>
     qpat_assum `!i. i IN tu.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >>
     `w2n w <= w2n w + (i - pbase) /\
      w2n w + (i - pbase) < w2n w + 32 + LENGTH bs` by decide_tac >>
     metis_tac[]) >>
  `!i. i < pbase \/ pbase + cap <= i ==> (i IN tu.t_mem <=> i IN tj.t_mem)` by
    (gen_tac >> disch_tac >>
     `~(pbase <= i /\ i < pbase + cap)` by decide_tac >> simp[]) >>
  qexistsl [`u`,`Gu`,`tu`] >> simp[] >>
  fs[typed_copy_state_frame_def, venom_state_component_equality]
QED
