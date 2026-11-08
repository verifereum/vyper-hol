Theory bodyPtrTypeBuiltinsEmptyMemoryRun
Ancestors
  bodyPtrTypeBuiltinsEmptyExec bodyPtrTypeBuiltinsEmptyFrame
  bodyPtrTypeBuiltinsEmptyAlloc exprLoweringProps venomState
  exprSimAlloc exprSimProps valueEncodingProps
  compileEnv context finite_map pred_set loweringHalt bodyPtrDefs valueEncoding
  exprSimDefs fragGasPathPtr

Theorem empty_buffer_framed_certificate:
  !sz header sa sb buf func cenv cx es s t ctx D PG G tn d.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!p n. cenv.ce_return_buf = SOME (PtrVar (Var p) n) ==> not_fresh_at sa p) /\
    (!p n. cenv.ce_return_pc = SOME (PtrVar (Var p) n) ==> not_fresh_at sa p) /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!a n. a+n <= w2n (THE (eval_operand buf.buf_operand t)) \/
      w2n (THE (eval_operand buf.buf_operand t))+sz <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    ghost_inv d cenv cx es G tn s ==>
    ?p w H th. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
      ptr_covers H th p t sz /\
      (!a. w2n w <= a /\ a < w2n w+(if header then 32 else sz) ==>
        a NOTIN th.t_mem) /\
      ghost_inv d cenv cx es H th t /\
      ghost_kept cenv es sa G tn s H th
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_compile_prefix >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all empty_alloc_buffer_certificate >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  gvs[] >> rename1 `ptr_covers midG midtn p u sz` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `w2n w + sz < dimword (:256)` by decide_tac >>
  drule_all empty_buffer_prefixed_tail_certificate >> strip_tac >>
  rename1 `ptr_covers finalG finaltn p t sz` >>
  qexistsl_tac [`w`, `finalG`, `finaltn`] >> simp[] >>
  rpt conj_tac
  >- suspend "inv"
  >- suspend "kept"
QED
Resume empty_buffer_framed_certificate[inv]:
  irule ghost_inv_exterior_frame >>
  qexistsl_tac [`midG`, `not_fresh_at sm`, `u`, `midtn`,
    `{a | w2n w <= a /\ a < w2n w+sz}`] >>
  simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  rpt conj_tac
  >- (fs[local_ptrs_reserved_def] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- suspend "locals"
  >- (rpt strip_tac >> Cases_on `header` >> gvs[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!a n. _ \/ _ ==> mem_bytes_at _ _ _ = _` irule >>
  gvs[eval_operand_def] >> Cases_on `header` >> gvs[] >> decide_tac
QED
Resume empty_buffer_framed_certificate[locals]:
  rpt gen_tac >> strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
  strip_tac >> gvs[] >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[val_footprint_le] >>
  `local_region cenv es.scopes u name (w2n w') sz'` by
    (simp[local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[regions_disjoint_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED
Resume empty_buffer_framed_certificate[kept]:
  irule ghost_kept_decreasing_frame >>
  qexistsl_tac [`midG`, `midtn`] >> simp[SUBSET_DEF] >>
  drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]
QED
Finalise empty_buffer_framed_certificate

Theorem empty_buffer_framed_path:
  !sz header sa sb buf func cenv cx es s t ctx D PG G tn d.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!p n. cenv.ce_return_buf = SOME (PtrVar (Var p) n) ==> not_fresh_at sa p) /\
    (!p n. cenv.ce_return_pc = SOME (PtrVar (Var p) n) ==> not_fresh_at sa p) /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!a n. a+n <= w2n (THE (eval_operand buf.buf_operand t)) \/
      w2n (THE (eval_operand buf.buf_operand t))+sz <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    ghost_inv d cenv cx es G tn s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?p w H th. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
      gas_path_ptr D 0 ctx func PG G tn s 0 H th
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      ptr_covers H th p t sz /\
      (!a. w2n w <= a /\ a < w2n w+(if header then 32 else sz) ==>
        a NOTIN th.t_mem) /\
      ghost_inv d cenv cx es H th t /\
      ghost_kept cenv es sa G tn s H th
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_framed_certificate >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all empty_buffer_checked_path >>
  strip_tac >> qexistsl_tac [`p`, `w`, `H`, `th`] >> simp[]
QED
