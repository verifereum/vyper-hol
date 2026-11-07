Theory extRetScratchInitPtr
Ancestors
  extRetBufferStatePtr extRetBulkCopyCountedPtr extRetBytesCopyCountedPtr
  allocaSiteResource localPtrsProps loweringHalt venomMemDefs fragExecPtr fragGasPathPtr fragGasSeqPtr fragExec emitHelperProps
  exprLoweringProps compileEnv emitHelper context codegenRel loweringPosts
  ptrDiscipline ptrSafeRun bodyPtrDefs typedCopyPtr venomState venomInst
  venomExecSemantics venomMemProps valueEncoding valueEncodingProps words
  finite_map pred_set arithmetic

(* The existing store interface omits concrete allocation metadata. Retain
   its exact state here, so no recursive consumer must unfold MSTORE. *)
Theorem scratch_store_state_counted_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf = (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst;value] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qabbrev_tac `t = mstore (w2n a) w s` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MSTORE [Var dst;value] []` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  `step_prov PG G inst t = G /\ tnf.t_var = tn.t_var /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (simp[Abbr `inst`, Abbr `t`, Abbr `tnf`] >>
     irule mstore_ghost_frame >> simp[]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst t) tnf
       (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     qunabbrev_tac `tnf` >> irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >> simp[]) >>
  simp[Abbr `t`, mstore_def, write_memory_with_expansion_def,
       Abbr `tnf`, Abbr `inst`, step_taint_def, imm_taint_def, mk_inst_def,
       lookup_var_def, op_taint_def]
QED

Theorem scratch_word_init_ambient_counted_ptr:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; init] sm = ((),sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand init s = SOME w /\ op_taint tn init = {} /\
  (!v. init = Var v ==> not_fresh_at sa v) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    addr+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    mload addr sf = w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    sf.vs_memory = (mstore addr w s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
                FLOOKUP sf.vs_allocas aid = SOME site) /\
    alloca_inv sf /\ sf.vs_labels = s.vs_labels /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (buf.buf_operand,sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `32 < dimword(:256)` by simp[dimword_def] >>
  drule_all compile_alloc_buffer_state_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand init sf = SOME w /\ op_taint tnf init = {}` by
    (Cases_on `init` >> gvs[eval_operand_def, op_taint_def]) >>
  gvs[] >> drule_all scratch_store_state_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`addr`, `Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> metis_tac[]) >>
  `addr < dimword(:256)` by decide_tac >>
  `sf'.vs_allocas = sf.vs_allocas /\ sf'.vs_alloca_next = sf.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  `alloca_inv sf'` by
    (irule alloca_inv_fields >> qexists_tac `sf` >>
     gvs[stmt_state_rel_def]) >>
  `sf'.vs_memory = (mstore addr w s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  `mload addr sf' = w` by
    (qspecl_then [`addr`, `w`, `s`] mp_tac mload_mstore_same >> simp[mload_def]) >>
  `mem_agree_outside {i | addr <= i /\ i < addr+32} sf'.vs_memory s.vs_memory` by
    metis_tac[mstore_memory_frame] >>
  `ptr_covers Gf tnf' ip sf' 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[] >>
  simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  metis_tac[]
QED

(* Consume only the resource/effect projections of scratch initialization. *)
Theorem scratch_word_init_registered_frame:
  alloca_inv sf /\
  (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
              FLOOKUP sf.vs_allocas aid = SOME site) /\
  FLOOKUP sf.vs_allocas child = SOME (addr,32) /\
  mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
  (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) ==>
  !parent p n. FLOOKUP s.vs_allocas parent = SOME (p,n) /\ parent <> child ==>
    (!i. p <= i /\ i < p+n ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  rpt strip_tac >>
  `venomMemDefs$regions_disjoint (p,n) (addr,32)` by
    (irule alloca_site_preserved_protection >> metis_tac[]) >>
  `i < addr \/ addr+32 <= i` by
    (gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

Theorem scratch_word_init_registered_cursor:
  alloca_inv sf /\
  (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
              FLOOKUP sf.vs_allocas aid = SOME site) /\
  FLOOKUP sf.vs_allocas child = SOME (addr,32) /\
  sf.vs_memory = (mstore addr w s).vs_memory /\
  (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  FLOOKUP s.vs_allocas parent = SOME (p,32) /\ parent <> child ==>
    mload p sf = mload p s /\
    ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
     (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))
Proof
  strip_tac >>
  `venomMemDefs$regions_disjoint (p,32) (addr,32)` by
    (irule alloca_site_preserved_protection >> metis_tac[]) >>
  conj_tac >-
    (qspecl_then [`p`, `addr`, `w`, `s`] mp_tac mstore_mem_word_at_disjoint >>
     qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     simp[venomMemDefsTheory.regions_disjoint_def,
          mload_def, mem_word_at_def, mem_bytes_at_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `i < addr \/ addr+32 <= i` by
    (gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED
