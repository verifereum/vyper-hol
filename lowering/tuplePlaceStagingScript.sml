Theory tuplePlaceStaging
Ancestors
  placeMemoryStaging exprSimProps bodyMemoryDefs venomMemDefs
  placeMemoryTypedPrimitive exprLoweringProps compileEnv venomState
  fragGasMode valueEncodingProps loweringPosts stmtSimDefs
  finite_map context freshWrites loweringHalt rich_list fragExec
  abiTupleProps placeMemoryCopyFrames

(* The source is either a contained live local or a contained older allocation.
   Only the allocation actually executed below needs separation. *)
Theorem tuple_place_staging_positive:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op n sm = ((),sn) /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 0 < n /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ n = type_memory_size stv /\
  val_wf stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  b <= w2n sw /\ w2n sw+n <= b+len /\
  ((?name. local_region cenv ee.scopes s name b len) \/
   (?aid. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id)) ==>
  ?r u tw. gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx ee r /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw+n < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
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
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw+n <= w2n tw \/ w2n tw+n <= w2n sw) /\
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
    eval_operand buf.buf_operand u = SOME tw
Proof
  strip_tac >>
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
  `w2n sw+n <= w2n tw \/ w2n tw+n <= w2n sw` by
    (all_tac >>~- ([`local_region cenv ee.scopes s name b len`],
      (`local_region cenv ee.scopes r name b len` by
       (irule local_region_frame_fwd >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      `regions_disjoint (w2n tw) n b len` by metis_tac[] >>
      gvs[regions_disjoint_def] >> decide_tac)) >>
     (`FLOOKUP r.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
      `alloca_inv r` by metis_tac[stmt_state_rel_def] >>
      `b+len <= w2n tw \/ w2n tw+n <= b` by
       (`aid <> sa.cs_next_id` by decide_tac >>
        qpat_x_assum `alloca_inv r` mp_tac >>
        rewrite_tac[alloca_inv_def, allocas_non_overlapping_def] >> strip_tac >>
        qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >>
        simp[] >> decide_tac) >> decide_tac)) >>
  drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `val_in_memory stv v (w2n tw) t.vs_memory` by
    (irule val_in_memory_relocate >> conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `n`, `w2n sw`] >> simp[]) >>
  `val_in_memory stv v (w2n sw) t.vs_memory` by
    (irule val_in_memory_outside_write >> conj_tac >- simp[] >>
     qexistsl_tac [`w2n tw`, `s.vs_memory`, `n`] >> metis_tac[]) >>
  qexistsl_tac [`r`, `t`, `tw`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[regions_disjoint_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED
