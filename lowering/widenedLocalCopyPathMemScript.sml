(* Counted normalization of a staged aggregate into a reserved local. *)
Theory widenedLocalCopyPathMem
Ancestors
  widenedStagingState fragGasPathResources typedNormalizeRankPathMem freshWrites
  abiDecoderFrame compileEnv context stmtLowering venomState words
  abiBuiltinAllocation emitHelperProps exprLoweringProps loweringHalt
  abiTupleProps fragGasPathMem list rich_list arithmetic

Theorem staged_local_typed_copy_path_mem:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  compile_store_memory_typed ce dst dty buf.buf_operand sty sn = ((),sb) /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ alloca_history fn s /\
  fn_has_code sa sn fn /\ fn_has_code sn sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n = type_memory_size stv /\ n < dimword(:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + n <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id /\
  type_memory_size dtv <= sz /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r u t (tw:256 word) g.
    gas_path_mem ctx fn s 0 (OK u) /\ gas_path_mem ctx fn s g (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn ce cx es r /\ r.vs_memory = s.vs_memory /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    s.vs_alloca_next <= r.vs_alloca_next /\
    (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx;
      vs_prev_bb := r.vs_prev_bb|>) = r /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a k. (a+k <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
      (a+k <= w2n tw \/ w2n tw+n <= a) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    stmt_state_rel ctx fn ce cx es u /\ alloca_history fn u /\
    alloca_history fn t /\ LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
      vs_prev_bb := u.vs_prev_bb|>) = u /\
    (!a k. a+k <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k u.vs_memory)
Proof
  strip_tac >> `!x. src = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all compile_staging_prefix_state_mem >>
  disch_then (qx_choose_then `r` (qx_choose_then `t` (qx_choose_then `tw`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_x_assum `n = type_memory_size stv` SUBST_ALL_TAC >>
  qpat_x_assum `?p. _` (qx_choose_then `p` strip_assume_tac) >>
  `cs_extends sa sn` by
    (irule cs_extends_trans >> qexists `sm` >> conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (mp_tac (Q.SPECL [`type_memory_size stv`, `sa`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`buf.buf_operand`, `src`, `type_memory_size stv`, `sm`] ci_mono_compile_copy_memory) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `eval_operand dst t = SOME dw` by metis_tac[] >>
  `!x. dst = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sn x` by
    (gen_tac >> strip_tac >-
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> conj_tac >- decide_tac >>
        qpat_x_assum `!x. src = Var x \/ dst = Var x ==> _` irule >> simp[]) >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >> gvs[]) >>
  `w2n tw + type_memory_size stv <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n tw` by
    (qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `w2n dw + type_memory_size dtv <= t.vs_alloca_next` by
    (gvs[venom_state_component_equality] >> decide_tac) >>
  `?u g. gas_path_mem ctx fn t g (OK u) /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    (!a k. a+k <= w2n dw \/ w2n dw+type_memory_size dtv <= a ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k t.vs_memory) /\
    (u with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_current_bb := sn.cs_current_bb; vs_inst_idx := LENGTH sn.cs_current_insts;
      vs_prev_bb := t.vs_prev_bb|>) = t /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
    LENGTH t.vs_memory <= LENGTH u.vs_memory` by
    (irule typed_store_rank_path_mem >>
     first_assum (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     first_assum (irule_at (Pat `type_widens_to _ _ _`)) >> first_assum (irule_at (Pat `val_in_memory _ _ _ _`)) >>
     gvs[] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  suspend "finish"
QED

Resume staged_local_typed_copy_path_mem[finish]:
  markerLib.RESUME_TAC >>
  `gas_path_mem ctx fn s g (OK u)` by (drule_all gas_path_mem_then >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at sn x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >> metis_tac[]) >>
  `(u with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx;
      vs_prev_bb := r.vs_prev_bb|>) = r` by
    suspend "restore" >>
  `alloca_history fn u` by
    (irule (cj 1 gas_path_mem_history) >>
     first_assum (irule_at (Pat `gas_path_mem _ _ t _ _`)) >>
     simp[] >> fs[stmt_state_rel_def]) >>
  qexistsl_tac [`r`, `t`, `u`, `tw`, `g`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory = _` (qspecl_then [`a`, `k`] mp_tac) >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k t.vs_memory = _` (qspecl_then [`a`, `k`] mp_tac) >> simp[]
QED

Resume staged_local_typed_copy_path_mem[restore]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `(u with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|>) = t` mp_tac >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
    vs_current_bb := _; vs_inst_idx := _|>) = r` mp_tac >>
  qpat_x_assum `t.vs_current_bb = sn.cs_current_bb` mp_tac >>
  qpat_x_assum `t.vs_inst_idx = LENGTH sn.cs_current_insts` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[venom_state_component_equality] >> rpt strip_tac >> simp[]
QED

Finalise staged_local_typed_copy_path_mem
