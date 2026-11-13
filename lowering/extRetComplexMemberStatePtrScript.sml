Theory extRetComplexMemberStatePtr
Ancestors
  extRetRecursiveResourcePtr extRetRecursiveFramePtr extRetScratchResourcePtr
  extRetFramedChildPtr extRetChildNarrowFramePtr extRetBulkCopyCountedPtr
  extRetDynamicBodyPtr bodyPtrDefs compileEnv loweringStateRelDefs emitHelper
  fragExec fragGasPathPtr ptrDiscipline venomState venomMemDefs valueEncoding
  valueEncodingProps robustCopyTransportPtr words finite_map pred_set list
  rich_list arithmetic

(* All offsets are relative to the original source/destination, even when
   the compiler is processing a suffix of the member list. *)
Definition encoder_member_offset_def:
  encoder_member_offset start_offset sizes j = start_offset + SUM (TAKE j sizes)
End

Definition encoder_complex_layout_def:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor <=>
  LENGTH hs = LENGTH ms /\ LENGTH tails = LENGTH ms /\
  LENGTH dyn = LENGTH ms /\ LENGTH ns = LENGTH ms /\
  active = EXISTS I dyn /\
  a+scap < dimword(:256) /\ b+dcap < dimword(:256) /\
  regions_disjoint (a,scap) (b,dcap) /\
  ho + SUM hs + SUM tails <= dcap /\
  (?id p sz. MEM (id,p,sz) protected /\ p <= b /\ b+dcap <= p+sz) /\
  (!j. j < LENGTH ms ==>
    encoder_member_offset so ms j + EL j ms <= scap /\
    EL j ns <= caps j /\ children j SUBSET sites /\
    EL j tails = (if EL j dyn then EL j ns else 0) /\
    (if EL j dyn then
       EL j hs = 32 /\
       encoder_member_offset (ho+SUM hs) tails j + caps j <= dcap
     else EL j ns = EL j hs /\ caps j <= EL j hs)) /\
  (active ==>
    cid IN sites /\ cursor+32 < dimword(:256) /\
    regions_disjoint (cursor,32) (a,scap) /\
    regions_disjoint (cursor,32) (b,dcap) /\
    (!j. j < LENGTH ms ==> cid NOTIN children j))
End

(* Compiler PCs are deliberately outside this invariant. The conditional
   cursor clause is vacuous for NIL and for a wholly static aggregate. *)
Definition encoder_complex_member_inv_def:
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v j st G tn s <=>
  ~s.vs_halted /\
  not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  encoder_resource ctx fn sites a scap protected s /\
  (!i mem. j <= i /\ i < LENGTH ms /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) mem) /\
  (!x. b <= x /\ x < b+encoder_member_offset ho hs j ==> x NOTIN tn.t_mem) /\
  (!x. b+(ho+SUM hs) <= x /\
    x < b+encoder_member_offset (ho+SUM hs) tails j ==> x NOTIN tn.t_mem) /\
  (active ==>
    not_fresh_at st ip /\ lookup_var ip s = SOME (n2w cursor) /\
    ptr_covers G tn ip s 32 /\ FLOOKUP s.vs_allocas cid = SOME (cursor,32) /\
    mload cursor s = n2w (encoder_member_offset (ho+SUM hs) tails j) /\
    (!x. cursor <= x /\ x < cursor+32 ==> x NOTIN tn.t_mem))
End

Theorem encoder_member_offset_zero:
  encoder_member_offset start_offset sizes 0 = start_offset
Proof
  simp[encoder_member_offset_def]
QED

Theorem encoder_member_offset_done:
  encoder_member_offset start_offset sizes (LENGTH sizes) = start_offset+SUM sizes
Proof
  simp[encoder_member_offset_def]
QED

Theorem encoder_member_offset_step:
  j < LENGTH sizes ==>
  encoder_member_offset start_offset sizes (j+1) =
    encoder_member_offset start_offset sizes j + EL j sizes
Proof
  metis_tac[encoder_member_offset_def, TAKE_EL_SNOC, SUM_SNOC, ADD_ASSOC]
QED

Theorem encoder_complex_member_completed:
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v (LENGTH ms) st G tn s /\
  LENGTH hs = LENGTH ms /\ LENGTH tails = LENGTH ms ==>
  (!x. b <= x /\ x < b+(ho+SUM hs+SUM tails) ==> x NOTIN tn.t_mem) /\
  (active ==> mload cursor s = n2w (ho+SUM hs+SUM tails))
Proof
  simp[encoder_complex_member_inv_def, encoder_member_offset_def] >>
  strip_tac >>
  `TAKE (LENGTH ms) hs = hs /\ TAKE (LENGTH ms) tails = tails` by
    metis_tac[TAKE_LENGTH_ID] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  Cases_on `x < b+(ho+SUM hs)` >- metis_tac[] >>
  `b+(ho+SUM hs) <= x` by decide_tac >> metis_tac[ADD_ASSOC]
QED

Theorem encoder_complex_empty_no_cursor:
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap F cid cursor
    so 0 [] [] [] tv v 0 st G tn s <=>
  ~s.vs_halted /\ not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  encoder_resource ctx fn sites a scap protected s
Proof
  simp[encoder_complex_member_inv_def, encoder_member_offset_def]
QED

Theorem encoder_complex_static_no_cursor:
  EVERY ($= F) dyn /\ LENGTH dyn = LENGTH ms /\
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor ==>
  ~active /\ tails = REPLICATE (LENGTH ms) 0
Proof
  simp[encoder_complex_layout_def, EVERY_EL, EXISTS_MEM] >> strip_tac >>
  `!i. i < LENGTH dyn ==> ~EL i dyn` by metis_tac[] >>
  conj_tac >- metis_tac[MEM_EL] >>
  irule LIST_EQ >> simp[EL_REPLICATE] >> metis_tac[]
QED

Theorem encoder_complex_member_memory_frame:
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v j sa G tn s /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  ~sf.vs_halted /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
  sf.vs_fmp = s.vs_fmp /\
  (!x. not_fresh_at sa x ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) ==>
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v j sb Gf tnf sf
Proof
  strip_tac >>
  `encoder_resource ctx fn sites a scap protected sf` by
    (irule encoder_resource_fields >>
     metis_tac[encoder_complex_member_inv_def]) >>
  Cases_on `active` >>
  gvs[encoder_complex_member_inv_def, mload_def, ptr_covers_def, op_prov_def] >>
  metis_tac[]
QED

Theorem encoder_complex_source_prepare_counted_ptr:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\ j < LENGTH ms /\
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v j sa G tn s /\
  emit_op ADD [Var src; Lit (n2w (encoder_member_offset so ms j))] sa = (Var es,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gp tnp sp.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gp tnp (OK sp) /\
    sp.vs_current_bb = sb.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sb.cs_current_insts /\
    encoder_complex_member_inv ctx fn sites protected
      src dst ip a b scap dcap active cid cursor
      so ho ms hs tails tv v j sb Gp tnp sp /\
    lookup_var es sp = SOME (n2w (a+encoder_member_offset so ms j)) /\
    ptr_covers Gp tnp es sp (EL j ms) /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
    sp.vs_allocas = s.vs_allocas /\ sp.vs_alloca_next = s.vs_alloca_next /\
    sp.vs_fmp = s.vs_fmp /\ encoder_ambient_frame tn s tnp sp /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sp = lookup_var x s /\ FLOOKUP Gp x = FLOOKUP G x /\
      op_taint tnp (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `lookup_var src s = SOME (n2w a) /\ ptr_covers G tn src s scap /\ ~s.vs_halted` by
    fs[encoder_complex_member_inv_def] >>
  `encoder_member_offset so ms j + EL j ms <= scap /\ a+scap < dimword(:256)` by
    metis_tac[encoder_complex_layout_def] >>
  `w2n (n2w a : bytes32) = a` by simp[w2n_n2w, LESS_MOD] >>
  `w2n (n2w a : bytes32) + encoder_member_offset so ms j < dimword(:256)` by
    decide_tac >>
  drule_all emit_bulk_offset_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[LESS_EQ_REFL]) >>
  qexistsl [`Gf`,`tnf`,`sf`] >> simp[encoder_ambient_frame_def] >>
  irule encoder_complex_member_memory_frame >>
  metis_tac[]
QED

(* Scratch is excluded at the actual endpoint, not at a guessed allocation
   address. This also handles reuse of an already registered scratch site. *)
Theorem encoder_complex_scratch_excludes_source:
  encoder_resource ctx fn sites a scap protected s /\
  a <= i /\ i < a+scap ==>
  i NOTIN encoder_scratch_span sites s
Proof
  pure_rewrite_tac[encoder_resource_def, scratch_resource_def,
    encoder_scratch_span_def] >>
  pure_rewrite_tac [GSPECIFICATION] >> BETA_TAC >>
  pure_rewrite_tac [pairTheory.PAIR_EQ, AND_CLAUSES] >>
  strip_tac >> strip_tac >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE [EQ_CLAUSES]) >>
  `scap <> 0` by decide_tac >>
  `regions_disjoint (a,scap) (b,n)` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_complex_scratch_excludes_protected:
  encoder_resource ctx fn sites a scap protected s /\
  MEM (id,p,sz) protected /\ p <= i /\ i < p+sz ==>
  i NOTIN encoder_scratch_span sites s
Proof
  strip_tac >> drule_all encoder_resource_protected >> strip_tac >>
  qpat_x_assum `scratch_resource _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scratch_resource_def, encoder_scratch_span_def,
    GSPECIFICATION] >> BETA_TAC >>
  pure_rewrite_tac[pairTheory.PAIR_EQ, AND_CLAUSES] >>
  strip_tac >> strip_tac >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE [EQ_CLAUSES]) >>
  `sz <> 0` by decide_tac >>
  `regions_disjoint (p,sz) (b,n)` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_complex_member_initial:
  ~s.vs_halted /\ not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  encoder_resource ctx fn sites a scap protected s /\
  (!i mem. i < LENGTH ms /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) mem) /\
  (!x. b <= x /\ x < b+ho ==> x NOTIN tn.t_mem) /\
  (active ==> not_fresh_at st ip /\ lookup_var ip s = SOME (n2w cursor) /\
    ptr_covers G tn ip s 32 /\ FLOOKUP s.vs_allocas cid = SOME (cursor,32) /\
    mload cursor s = n2w (ho+SUM hs) /\
    (!x. cursor <= x /\ x < cursor+32 ==> x NOTIN tn.t_mem)) ==>
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v 0 st G tn s
Proof
  simp[encoder_complex_member_inv_def, encoder_member_offset_zero]
QED

Theorem encoder_complex_envelope_excludes_source:
  encoder_resource ctx fn sites a scap protected s /\
  regions_disjoint (a,scap) (dst,cap) ==>
  !i. a <= i /\ i < a+scap ==>
    i NOTIN encoder_write_envelope sites s dst cap
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `i NOTIN encoder_scratch_span sites s` by
    (irule encoder_complex_scratch_excludes_source >> metis_tac[]) >>
  simp[encoder_write_envelope_def] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_complex_unread_frame:
  encoder_resource ctx fn sites a scap protected sf /\
  regions_disjoint (a,scap) (dst,cap) /\
  mem_agree_outside (encoder_write_envelope sites sf dst cap)
    sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope sites sf dst cap ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  val_wf tv v /\ a <= p /\ p+val_footprint tv v <= a+scap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v p mem) ==>
  !mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv v p mem
Proof
  strip_tac >> gen_tac >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `encoder_write_envelope sites sf dst cap`] >> simp[] >>
  reverse conj_tac >-
    (gen_tac >> strip_tac >>
     `a <= i /\ i < a+scap` by decide_tac >>
     drule_all encoder_complex_envelope_excludes_source >>
     simp[]) >>
  fs[mem_agree_outside_def]
QED

Theorem encoder_complex_protected_prefix_frame:
  encoder_resource ctx fn sites a scap protected sf /\
  MEM (id,p,sz) protected /\ p <= start /\ start+len <= p+sz /\
  regions_disjoint (start,len) (dst,cap) /\
  mem_agree_outside (encoder_write_envelope sites sf dst cap)
    sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope sites sf dst cap ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. start <= i /\ i < start+len ==> i NOTIN tn.t_mem) ==>
  mem_bytes_at start len sf.vs_memory = mem_bytes_at start len s.vs_memory /\
  (!i. start <= i /\ i < start+len ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> irule encoder_narrow_frame_preserves_clean_interval >>
  qexistsl_tac [`tn`, `encoder_write_envelope sites sf dst cap`] >> simp[] >>
  simp[DISJOINT_DEF, EXTENSION, encoder_write_envelope_def] >>
  gen_tac >> Cases_on `start <= x /\ x < start+len` >> simp[] >>
  `x NOTIN encoder_scratch_span sites sf` by
    (`p <= x /\ x < p+sz` by decide_tac >>
     drule_all encoder_complex_scratch_excludes_protected >> simp[]) >>
  simp[] >> fs[regions_disjoint_def] >> decide_tac
QED
