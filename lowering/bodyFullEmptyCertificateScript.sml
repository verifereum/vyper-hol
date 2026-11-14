Theory bodyFullEmptyCertificate
Ancestors
  bodyFullEmptyOrigin bodyFullEmptyFrame bodyFullAllocGeneric
  bodyPtrTypeBuiltinsEmptyAlloc exprLoweringProps bodyPtrDefs
  ptrDiscipline compileEnv venomState finite_map words pred_set
  abiEmptyAllocate abiEmptySequence emitHelperProps bodyPtrIfExpAllocCompiler
  rich_list fragGasSeqPtr instIdxIndep fragExec
  exprSimBufferEmptyExec exprSimAlloc loweringHalt list loweringStateRelDefs
  bodyFullUnwrapRun instSeqPtrLo entrySinkExtraction fragExecPtr
  venomInst bodyEmptyBufferMemory

Theorem empty_alloc_ghost_kept_at[local]:
  !ctx func cenv cx es s sa n out t PG G tn lo.
    stmt_state_rel (H : (bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ ~not_fresh_at sa out /\
    lo <= s.vs_alloca_next /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
    ghost_kept_at lo cenv es sa G tn s
      (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) t)
      (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_alloc_ghost_kept >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  fs[ghost_kept_def] >> rewrite_tac[ghost_kept_at_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule_all bodyPtrIfExpAllocKeptTheory.alloca_step_taint_below_frontier >> metis_tac[]
QED


Theorem empty_buffer_indexed_frames:
  !H D lo d ctx func cenv cx es sa sb buf sz header s t PG G tn Gf tnf.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel (H : (bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ghost_inv_at D lo d cenv cx es G tn s /\ lo <= s.vs_alloca_next /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf ==>
    ghost_inv_at D lo d cenv cx es Gf tnf t /\
    ghost_kept_at lo cenv es sa G tn s Gf tnf
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_compile_prefix >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `ghost_inv_at D lo d cenv cx es
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s u tn) u` by
    (irule compile_alloc_buffer_ghost_frame_at >> simp[] >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`H`, `ctx`, `func`] >> gvs[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `ghost_kept_at lo cenv es sa G tn s
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s u tn)` by
    (irule empty_alloc_ghost_kept_at >> gvs[] >>
     qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> simp[]) >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by gvs[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] allocationPtrTheory.alloca_step_ptr_covers) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `ghost_inv_at D lo d cenv cx es Ga ta u` >>
  `lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    fs[lookup_var_def] >>
  `ptr_covers Ga ta p (u with vs_inst_idx := SUC s.vs_inst_idx) sz` by simp[] >>
  qpat_x_assum `lookup_var p u = SOME w` kall_tac >>
  qpat_x_assum `ptr_covers Ga ta p u sz` kall_tac >>
  drule_all empty_buffer_tail_effects >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sm sb) _ = OK v` >>
  `run_inst_seq (emitted_insts sm sb) u = OK t` by gvs[run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule compile_builtin_empty_complex_shape >> strip_tac >>
     gvs[EVERY_MEM] >> metis_tac[MEM]) >>
  `v = t with vs_inst_idx := SUC s.vs_inst_idx` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`u`, `SUC s.vs_inst_idx`] mp_tac) >>
     gvs[run_inst_seq_def, exec_result_map_def]) >>
  suspend "finish"
QED
Resume empty_buffer_indexed_frames[finish]:
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    metis_tac[ghost_inv_at_def] >>
  qpat_x_assum `!D lo. _` (qspecl_then [`D`, `lo`] mp_tac) >>
  simp[] >> (impl_tac >- (qpat_x_assum `allocas_from lo u` mp_tac >> simp[allocas_from_def])) >> strip_tac >>
  qpat_x_assum `inst_seq_ptr D lo ctx func PG G tn _ s Gf tnf` mp_tac >>
  asm_rewrite_tac[inst_seq_ptr_def] >>
  simp[GSYM markerTheory.Abbrev_def] >> strip_tac >>
  `Gf = Gf' /\ tnf = tnf'` by metis_tac[inst_seq_ptr_ghost_unique] >>
  reverse conj_tac
  >- (irule ghost_kept_at_clean_suffix >>
      qexistsl_tac [`Ga`, `ta`] >> simp[] >> metis_tac[]) >>
  `!q. not_fresh_at sm q ==> lookup_var q t = lookup_var q u /\
     FLOOKUP Gf q = FLOOKUP Ga q /\ op_taint tnf (Var q) = op_taint ta (Var q)` by
    (rpt strip_tac >> first_x_assum drule >> simp[lookup_var_def]) >>
  `local_ptrs_rel func cenv es.scopes u` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es u` kall_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  `!a len. a + len <= w2n w \/ w2n w + sz <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory` by
    (gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  irule empty_ghost_inv_exterior_frame_at >>
  qexistsl_tac [`Ga`, `\q. not_fresh_at sm q`, `u`, `ta`,
    `{a | w2n w <= a /\ a < w2n w + sz}`] >>
  simp[] >> rpt conj_tac
  >- suspend "locals_reserved"
  >- suspend "return_buf"
  >- suspend "return_pc"
  >- suspend "imm_reserved"
  >- suspend "locals_sep"
  >- suspend "bytes"
  >- suspend "taint"
  >- suspend "prefix"
  >> (qpat_x_assum `v with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
      simp[venom_state_component_equality])
QED
Resume empty_buffer_indexed_frames[bytes]:
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  rpt strip_tac >> decide_tac
QED
Resume empty_buffer_indexed_frames[taint]:
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume empty_buffer_indexed_frames[prefix]:
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume empty_buffer_indexed_frames[locals_reserved]:
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED
Resume empty_buffer_indexed_frames[return_buf]:
  rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz'` by
    (fs[local_ptrs_rel_def] >> metis_tac[optionTheory.SOME_11]) >>
  `val_footprint entry.type entry.value <= sz'` by
    metis_tac[exprSimPropsTheory.val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `local_region cenv es.scopes u name (w2n w'') sz'` by
    (simp[local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED
Resume empty_buffer_indexed_frames[return_pc]:
  metis_tac[local_ptrs_reserved_imm_base]
QED
Resume empty_buffer_indexed_frames[imm_reserved]:
  Cases_on `header` >> gvs[] >> rpt strip_tac >>
  `~(w2n w <= i) \/ ~(i < w2n w + 32)` by decide_tac >> simp[]
QED
Resume empty_buffer_indexed_frames[locals_sep]:
  rpt strip_tac >>
  `i + 1 <= w2n w \/ w2n w + sz <= i` by decide_tac >>
  metis_tac[]
QED
Finalise empty_buffer_indexed_frames

Theorem empty_buffer_uniform_run:
  !sz header sa sb buf func cenv cx es s t ctx PG G tn.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel (H : (bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?p w Gf tnf. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
      ptr_covers Gf tnf p t sz /\
      (!a. w2n w <= a /\ a < w2n w+(if header then 32 else sz) ==>
        a NOTIN tnf.t_mem) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      (!D lo explicit. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
      (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
        inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_compile_prefix >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all empty_alloc_checked_coverage >>
  disch_then (qspecl_then [`ARB`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    fs[lookup_var_def] >>
  `ptr_covers G' tn' p (u with vs_inst_idx := SUC s.vs_inst_idx) sz` by gvs[] >>
  qpat_x_assum `lookup_var p u = _` kall_tac >>
  qpat_x_assum `ptr_covers G' tn' _ u sz` kall_tac >>
  `w2n w+sz < dimword (:256)` by decide_tac >>
  drule_all empty_buffer_tail_effects >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sm sb) _ = OK v` >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (fs[EVERY_MEM] >> metis_tac[MEM]) >>
  `run_inst_seq (emitted_insts sm sb) u = OK t` by
    gvs[run_inst_seq_def] >>
  `v = t with vs_inst_idx := SUC s.vs_inst_idx` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`u`, `SUC s.vs_inst_idx`] mp_tac) >>
     gvs[run_inst_seq_def, exec_result_map_def]) >>
  rename1 `ptr_covers finalG tk p v sz` >>
  `!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s finalG tk` by
    suspend "sequence" >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (gvs[EVERY_MEM, mk_inst_def] >> metis_tac[MEM]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es u` kall_tac >>
  drule_all compile_empty_buffer_seq_mem >> strip_tac >>
  qexistsl_tac [`p`, `w`, `finalG`, `tk`] >>
  gvs[lookup_var_def] >>
  rpt gen_tac >> strip_tac >> suspend "path"
QED
Resume empty_buffer_uniform_run[sequence]:
  rpt gen_tac >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s finalG tk` by
    (qpat_x_assum `inst_seq_ptr ARB 0 _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[inst_seq_ptr_def, ptr_inst_ok_alloca] >> strip_tac >> gvs[] >>
     first_x_assum irule >> simp[allocas_from_def]) >>
  irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> gvs[]
QED
Resume empty_buffer_uniform_run[path]:
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `isPREFIX sa.cs_current_insts sb.cs_current_insts` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     simp_tac (srw_ss()) [emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     simp[DROP_LENGTH_APPEND]) >>
  irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
  gvs[EVERY_MEM, mk_inst_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
Finalise empty_buffer_uniform_run

Theorem empty_buffer_origin_full:
  !H0 DF lo d ctx func cenv cx es sa sb buf sz header s t PG G tn st0.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel (H0 : (bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    alloca_history func s /\ lo <= s.vs_alloca_next /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?p w Gf tnf. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
      ptr_covers Gf tnf p t sz /\
      (!a. w2n w <= a /\ a < w2n w+(if header then 32 else sz) ==>
        a NOTIN tnf.t_mem) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        ghost_inv_at (DF H) lo d cenv cx es Gf tnf
          (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
        ghost_kept_at lo cenv es sa G tn s Gf tnf) /\
      (!D base explicit. allocas_from base s /\ base <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D,base,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_uniform_run >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qexistsl_tac [`p`, `w`, `Gf`, `tnf`] >> simp[] >>
  conj_tac >- suspend "history" >>
  rpt strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  `inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (first_x_assum irule >> metis_tac[ghost_inv_at_def]) >>
  `ghost_inv_at (DF H) lo d cenv cx es Gf tnf t /\
   ghost_kept_at lo cenv es sa G tn s Gf tnf` by
    (irule empty_buffer_indexed_frames >> simp[] >>
     qexistsl_tac [`H`, `PG`, `buf`, `ctx`, `func`, `header`, `sb`, `sz`] >> simp[]) >>
  Cases_on `d`
  >- (fs[ghost_inv_at_def, lookup_var_def, return_buf_ptr_def,
         stor_taint_ok_at_def, allocas_from_def] >> metis_tac[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  fs[ghost_inv_at_def, lookup_var_def, return_buf_ptr_def,
     stor_taint_ok_at_def, allocas_from_def] >> metis_tac[]
QED
Resume empty_buffer_origin_full[history]:
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  irule emitted_alloca_history >>
  conj_tac >- simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `s`, `sa`] >> simp[] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >> simp[] >>
  reverse conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `isPREFIX sa.cs_current_insts sb.cs_current_insts` mp_tac >>
  rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >> simp[DROP_LENGTH_APPEND]
QED
Finalise empty_buffer_origin_full
