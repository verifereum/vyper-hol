Theory assignPlaceStaging
Ancestors
  loweringStateRelDefs
  placeMemoryStaging placeMemoryTypedPrimitive exprLoweringProps
  placeMemoryCopyEffect fragGasMode exprSimProps valueCopy
  context compileEnv venomState venomInst exprSimAlloc fragExec
  loweringHalt abiTupleProps rich_list exprSimCopy localMemoryStorePath
  stmtSimDefs venomMemDefs emitHelperProps exprSimStorageCopy

(* The staging copy is a snapshot. Only the value's live footprint needs
   to be valid at the source; the dead capacity may overlap the temporary. *)
Theorem assign_place_staging_live:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op n sm = ((),sn) /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ val_footprint stv v <= n /\
  val_wf stv v /\ val_in_memory stv v (w2n sw) s.vs_memory ==>
  ?r u tw.
    gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx ee r /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw + n < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP r.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n tw = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n tw,n)) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    gas_marked_path F ctx func r 0 (OK u) /\
    gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory stv v (w2n tw) u.vs_memory /\
    u.vs_allocas = r.vs_allocas /\
    (u with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
      vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a len. a+len <= w2n tw \/ w2n tw+n <= a ==>
       mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME tw /\
    stmt_state_rel ctx func cenv cx ee u /\
    alloca_frame cenv ee sa s cenv ee u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_alloc_buffer_forward >> strip_tac >>
  `eval_operand op r = SOME sw` by
    (qpat_assum `(r with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|>) = s`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
  drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `val_in_memory stv v (w2n tw) t.vs_memory` by
    (irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
     qexistsl_tac [`w2n sw`, `n`, `s.vs_memory`] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by suspend "copy_state" >>
  `alloca_frame cenv ee sa s cenv ee t` by suspend "copy_frame" >>
  qexistsl_tac [`r`, `t`, `tw`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Resume assign_place_staging_live[copy_state]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  drule compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`, `q`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `fn_has_code sx sm func` by metis_tac[fn_has_code_split] >>
  `MEM (mk_inst sx.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists_tac `sm` >> simp[]) >>
  `sx.cs_next_id = sa.cs_next_id` by simp[] >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`w2n tw`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]`, `r`, `sm`, `n`] >>
  simp[mk_inst_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  conj_tac >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> fs[] >>
    qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> decide_tac) >>
  conj_tac
  >- gvs[copy_static_def, venom_state_component_equality] >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[mk_inst_def])
QED

Resume assign_place_staging_live[copy_frame]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  `allocas_non_overlapping t` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `!ad len. ad + len <= w2n tw \/ w2n tw + n <= ad ==>
    mem_bytes_at ad len t.vs_memory = mem_bytes_at ad len s.vs_memory` by
    (gvs[] >> metis_tac[]) >>
  irule alloca_frame_owned_copy >> simp[] >>
  rpt conj_tac
  >- (qexistsl_tac [`w2n tw`, `sa.cs_next_id`, `n`] >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[])
QED

Finalise assign_place_staging_live
