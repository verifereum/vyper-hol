(* Allocation execution uses the semantic function only for allocation bounds.
   Its executable fragment is independent of that function. *)
Theory placeRelayoutNormalizeFrame
Ancestors
  exprSimTypedAlloc exprSimAlloc exprSimCopy typedMemoryCopy exprLoweringProps
  loweringPosts venomMemDefs loweringHalt localPtrsProps freshWrites valueEncoding
  vyperTypeSystem list finite_map venomInst venomState fragExec exprSimProps
  loweringSlice compileEnv exprSimStorageCopy aggregateCodeTrace aggregateCountedRenamedStore
  placeRelayoutNormalizeCode aggregateCountedRawRelabel aggregateCountedStraightStore
  exprSimHash aggregateCountedStraightExec exprSimAbiGasBridge

Theorem place_alloc_buffer_source_frag:
  !ctx func cenv cx es sm mid buf sz s src a R.
    compile_alloc_buffer sz sm = (buf,mid) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) ==>
    ?u w. frag_exec ctx sm mid (\z. z = s) (\z. z = u) R /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> reverse conj_tac
  >- (Cases_on `src` >>
      gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
          local_region_def] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, emitted_insts_def,
      rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.IS_PREFIX_APPEND,
      mk_inst_def, is_terminator_def]
QED

(* Unlike the ancestor fragment, only the semantic ALLOCA membership is needed.
   In particular the function subsequently executing this fragment is arbitrary. *)
Theorem place_normalize_framed_frag:
  !ctx func cenv cx es ty sty stv dtv v val_op sa sm sb buf s sw R.
    compile_alloc_buffer (type_memory_bytes cenv ty) sa = (buf, sm) /\
    compile_store_memory_typed cenv buf.buf_operand ty val_op sty sm =
      ((), sb) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    type_memory_size dtv < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    stmt_state_rel ctx func cenv cx es s /\
    eval_operand val_op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\
                  FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                  b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len) \/
     (?n b len. local_region cenv es.scopes s n b len /\
                b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len)) ==>
    frag_exec ctx sa sb (\z. z = s)
      (\u. ?w. stmt_state_rel ctx func cenv cx es u /\
               eval_operand buf.buf_operand u = SOME w /\
               w2n w + type_memory_size dtv < dimword (:256) /\
               val_in_memory dtv v (w2n w) u.vs_memory /\
               FLOOKUP u.vs_allocas sa.cs_next_id =
                 SOME (w2n w, type_memory_size dtv) /\
               (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
               (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
               (!off len. off + len <= w2n w \/
                  w2n w + type_memory_size dtv <= off ==>
                 mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
               (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
               (!name b len. local_region cenv es.scopes s name b len ==>
                 regions_disjoint (w2n w) (type_memory_size dtv) b len)) R
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `type_memory_bytes cenv ty < dimword (:256)` by simp[] >>
  drule_all place_alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `(?aid b len. _) \/ _` strip_assume_tac
     >- (qpat_x_assum `!aid b len. _` drule_all >>
         simp[regions_disjoint_def] >> decide_tac) >>
     `local_region cenv es.scopes u n b len` by
       (drule_all copy_buffer_local_region_frame >>
        disch_then (qspecl_then [`es.scopes`, `n`, `b`, `len`] mp_tac) >> simp[]) >>
     qpat_x_assum `!name b len. _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!x. val_op = Var x ==> not_fresh_at sm x` by
    (qspecl_then [`type_memory_bytes cenv ty`, `sa`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[ci_mono_def] >> strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`type_memory_bytes cenv ty`, `sa`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  drule typed_return_store_frag >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`dtv`, `ctx`, `R`,
    `\t. stmt_state_rel ctx func cenv cx es t /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)`] mp_tac) >>
  (impl_tac >- suspend "frame" >> suspend "post")
QED

Resume place_normalize_framed_frag[frame]:
  markerLib.RESUME_TAC >> (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> conj_tac
  >- (irule copy_buffer_state_rel_frame >>
      qexistsl_tac [`w2n w`,
        `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
           [STRING #"%" (toString sa.cs_next_var)]`,
        `u`, `sm`, `type_memory_size dtv`] >>
      simp[mk_inst_def] >> conj_tac
      >- (rpt strip_tac >> qpat_x_assum `!name b len. _` drule >>
          simp[regions_disjoint_def] >> decide_tac) >>
      rpt strip_tac >> first_x_assum irule >> simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >> first_x_assum irule >> simp[arithmeticTheory.ADD_COMM])
QED

Resume place_normalize_framed_frag[post]:
  markerLib.RESUME_TAC >> (disch_then assume_tac >> drule frag_exec_weaken >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  drule copy_static_fields >> strip_tac >>
  qexists_tac `w` >> simp[] >> conj_tac
  >- (gvs[eval_operand_def] >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name b len. local_region _ _ u _ _ _ ==> _` mp_tac >>
  simp[] >> disch_then irule >>
  qpat_assum `local_ptrs_reserved cenv sa`
    (mp_then Any mp_tac copy_buffer_local_region_frame) >>
  simp[] >> disch_then drule >>
  disch_then (qspecl_then [`es.scopes`, `name`, `b`, `len`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `name` >> simp[])
QED

Finalise place_normalize_framed_frag

Theorem place_normalize_alloc_start_oblivious:
  frag_start_oblivious (compile_alloc_buffer nbytes)
Proof
  irule code_trace_start_oblivious >>
  simp[contextTheory.compile_alloc_buffer_def] >> irule code_trace_bind >>
  simp[code_trace_emit_op, code_trace_return]
QED

Theorem place_normalize_start_relabel:
  compile_alloc_buffer nbytes sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ty src sty sm = ((),sb) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  ?mid. compile_alloc_buffer nbytes (start_relabel L ids sa) = (buf,mid) /\
    compile_store_memory_typed ce buf.buf_operand ty src sty mid =
      ((),start_swap sa L ids sb)
Proof
  strip_tac >>
  `code_trace_parametric (comp_bind (compile_alloc_buffer nbytes) (\buf.
      compile_store_memory_typed ce buf.buf_operand ty src sty))` by
    (match_mp_tac code_trace_bind >> conj_tac
     >- (simp[contextTheory.compile_alloc_buffer_def] >> irule code_trace_bind >>
         simp[code_trace_emit_op, code_trace_return]) >>
     simp[code_trace_typed_copy_family]) >>
  drule code_trace_start_oblivious >>
  simp[exprSimAbiGasBridgeTheory.frag_start_oblivious_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `L`, `ids`] mp_tac) >>
  simp[comp_bind_def] >>
  mp_tac place_normalize_alloc_start_oblivious >>
  simp[exprSimAbiGasBridgeTheory.frag_start_oblivious_def] >>
  disch_then (qspecl_then [`sa`, `buf`, `sm`, `L`, `ids`] mp_tac) >> simp[] >>
  disch_then assume_tac >>
  simp[] >> strip_tac >>
  qexists_tac `start_swap sa L ids sm` >> simp[]
QED

Theorem place_normalize_framed_path:
  !ctx func cenv cx es ty sty stv dtv v val_op sa sm sb buf s sw.
    compile_alloc_buffer (type_memory_bytes cenv ty) sa = (buf, sm) /\
    compile_store_memory_typed cenv buf.buf_operand ty val_op sty sm = ((), sb) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    type_memory_size dtv < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    stmt_state_rel ctx func cenv cx es s /\ eval_operand val_op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
       b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len) \/
     (?n b len. local_region cenv es.scopes s n b len /\
       b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len)) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u w. gas_marked_path F ctx func s 0 (OK u) /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) u.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w, type_memory_size dtv) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      (!name b len. local_region cenv es.scopes s name b len ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all place_normalize_framed_frag >>
  disch_then (qspec_then `(\r. F)` assume_tac) >>
  qmatch_asmsub_abbrev_tac `frag_exec ctx sa sb _ Q _` >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  drule_all place_normalize_prefix_raw_shape >> strip_tac >>
  `!t rd. Q t ==> Q (t with vs_returndata := rd)` by suspend "rd" >>
  `!t p. Q t ==> Q (t with vs_prev_bb := p)` by suspend "prev" >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (Cases_on `sa.cs_blocks = sb.cs_blocks`
     >- (irule frag_exec_same_block_gas_path >> simp[] >>
         qexists_tac `(\z. z = s)` >> simp[] >> suspend "straight") >>
     `(?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
      (?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\ (\r. F) r)`
       suffices_by simp[] >>
     irule frag_exec_gas_path_relabel_raw >> simp[] >> suspend "relabel") >>
  qpat_x_assum `Q t` mp_tac >> simp[Abbr `Q`] >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> asm_rewrite_tac[]
QED

Resume place_normalize_framed_path[rd]:
  simp[Abbr `Q`] >> rpt gen_tac >> strip_tac >> qexists_tac `w` >>
  Cases_on `buf.buf_operand` >>
  gvs[hash_returndata_state_rel, eval_operand_def, lookup_var_def] >>
  asm_rewrite_tac[]
QED
Resume place_normalize_framed_path[prev]:
  simp[Abbr `Q`] >> rpt gen_tac >> strip_tac >> qexists_tac `w` >>
  Cases_on `buf.buf_operand` >>
  simp[aggregateCountedTypedStoreTheory.aggregate_stmt_state_rel_prev_bb,
       eval_operand_def, lookup_var_def] >>
  qpat_x_assum `eval_operand _ t = SOME w` mp_tac >>
  simp[eval_operand_def, lookup_var_def] >> strip_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` mp_tac >>
  simp[lookup_var_def]
QED
Resume place_normalize_framed_path[straight]:
  qexists_tac `sa` >> simp[] >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sm sb)` by
    (irule compile_store_memory_typed_same_block_nonterminators >>
     metis_tac[]) >>
  qpat_x_assum `EVERY _ (frag_code sm sb)` mp_tac >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def] >>
  `?code. sb.cs_current_insts = sm.cs_current_insts ++ code` by
    (qpat_x_assum `cs_extends sm sb` mp_tac >>
     simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> goal_assum (drule_at Any)) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, DROP_APPEND, mk_inst_def, is_terminator_def] >>
  `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0` by decide_tac >>
  simp[]
QED
Resume place_normalize_framed_path[relabel]:
  qexists_tac `sa` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all place_normalize_start_relabel >>
  disch_then (qspec_then `L` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx es (s with vs_current_bb := L)` by
    simp[aggregate_stmt_state_rel_current_bb] >>
  qpat_x_assum `compile_alloc_buffer _ sa = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ sm = _` kall_tac >>
  drule place_normalize_framed_frag >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`stv`, `dtv`, `v`, `sw`, `(\r. F)`] mp_tac) >>
  (impl_tac >- suspend "relabel_pre") >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `fn'` mp_tac) >>
  ` (start_swap sa L ids sb).cs_current_bb = sb.cs_current_bb /\
    (start_swap sa L ids sb).cs_current_insts = sb.cs_current_insts` by
    (irule start_swap_fields >> simp[]) >>
  simp[start_relabel_def] >> suspend "relabel_post"
QED
Resume place_normalize_framed_path[relabel_pre]:
  `local_ptrs_reserved cenv (start_relabel L ids sa)` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[start_relabel_def]) >>
  `!x. val_op = Var x ==> not_fresh_at (start_relabel L ids sa) x` by
    (qpat_x_assum `!x. val_op = Var x ==> _` mp_tac >>
     simp[start_relabel_def, not_fresh_at_def]) >>
  `eval_operand val_op (s with vs_current_bb := L) = SOME sw` by
    (Cases_on `val_op` >> gvs[eval_operand_def, lookup_var_def]) >>
  asm_rewrite_tac[] >>
  simp[start_relabel_def] >>
  qpat_x_assum `(?aid b len. _) \/ _` mp_tac >>
  simp[local_region_def, lookup_var_def] >>
  qpat_x_assum `MEM _ (fn_insts func)` mp_tac >> simp[]
QED
Resume place_normalize_framed_path[relabel_post]:
  strip_tac >> qexists_tac `u` >> simp[] >>
  simp[Abbr `Q`] >>
  conj_tac
  >- (qpat_x_assum `!x. not_fresh_at _ x ==> _` mp_tac >>
      simp[not_fresh_at_def, lookup_var_def]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` mp_tac >>
  simp[local_region_def, lookup_var_def]
QED
Finalise place_normalize_framed_path
