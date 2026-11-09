Theory bodyPtrIfExpStorageBodyInvariant
Ancestors
  bodyPtrIfExpStorageInvariant bodyPtrIfExpStorageBodyPost
  bodyPtrIfExpMaterializeFrame bodyPtrIfExpStorageFrame slotCopyExecution copyExecution
  bodyPtrDefs compileEnv venomState ptrDiscipline finite_map words
  valueEncoding vyperValue venomInst emitHelper bodyPtrIfExpStorageOrdinary

Theorem ifexp_copy_interior_live_bounds:
  slot_copy_inv cs load sBase p (d:bytes32) n [] i s /\ i<n /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= cs.cs_next_var /\
  (!name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\
    lookup_var v sBase = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n d \/ w2n d+32*n <= w2n w)) ==>
  !name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\
    lookup_var v s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n (d+n2w i*32w) \/
     w2n (d+n2w i*32w)+32 <= w2n w)
Proof
  strip_tac >>
  `w2n (d+n2w i*32w) = w2n d+32*i` by
    (irule slot_copy_body_nonwrapping >> qexists_tac `n` >> fs[slot_copy_inv_def]) >>
  rpt strip_tac >>
  `slot_copy_external cs (Var v)` by
    (irule ifexp_copy_not_fresh_external >>
     irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var v sBase = SOME w` by
    (fs[slot_copy_inv_def] >>
     qpat_x_assum `!op. _ ==> eval_operand op s = _`
       (qspec_then `Var v` mp_tac) >> simp[eval_operand_def]) >>
  `val_wf entry.type entry.value /\
   (w2n w+type_memory_size entry.type <= w2n d \/ w2n d+32*n <= w2n w)` by
    metis_tac[] >> simp[] >> decide_tac
QED

Theorem ifexp_copy_ptr_body:
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
    cs load src (Var out) sBase GBase tnBase p d n X i s G tn /\
  i<n /\ MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (TAKE 7 (slot_copy_body_insts cs src (Var out) load))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+7) =
    SOME (mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] []) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var out) /\
  eval_operand src sBase = SOME p /\ eval_operand (Var out) sBase = SOME d /\
  sa.cs_next_var <= cs.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n d \/ w2n d+32*n <= off) /\
  (!name pos len. local_region ce es.scopes s0 name pos len ==>
    pos+len <= w2n d \/ w2n d+32*n <= pos) /\
  (!name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\ lookup_var v sBase = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n d \/ w2n d+32*n <= w2n w)) /\
  (!j k. j<n /\ k IN (if load=SLOAD then key_taint tnBase.t_stor (p+n2w j)
    else key_taint tnBase.t_trans (p+n2w j)) ==> (j,k) IN X) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (slot_copy_body_result cs p d load i s)) /\
    ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
      cs load src (Var out) sBase GBase tnBase p d n X (i+1)
      (slot_copy_body_result cs p d load i s) G' tn'
Proof
  strip_tac >>
  `slot_copy_inv cs load sBase p d n [] i s /\
   ptr_covers G tn out s (32*n)` by fs[ifexp_copy_ptr_inv_def] >>
  `w2n (d+n2w i*32w) = w2n d+32*i` by
    (irule slot_copy_body_nonwrapping >> qexists_tac `n` >> fs[slot_copy_inv_def]) >>
  `eval_operand src s = SOME p /\ eval_operand (Var out) s = SOME d /\
   eval_operand (Var (slot_copy_var cs 0)) s = SOME (n2w i)` by
    (fs[slot_copy_inv_def] >> metis_tac[eval_operand_def]) >>
  `?b cap. op_prov G (Var out) = SOME (b,cap) /\
    b <= w2n (d+n2w i*32w) /\ w2n (d+n2w i*32w)+32 <= b+cap /\
    op_taint tn (Var out) = {}` by
    (fs[ptr_covers_def, eval_operand_def, op_prov_def] >>
     qexistsl_tac [`b`, `n'`] >> simp[] >> decide_tac) >>
  `op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
   op_prov G (Var (slot_copy_var cs 0)) = NONE` by fs[ifexp_copy_ptr_inv_def] >>
  drule_all ifexp_copy_body_transition >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_inv rty ce cx ee G' tn' (slot_copy_body_result cs p d load i s) /\
   ghost_kept ce es sa G0 tn0 s0 G' tn'` by suspend "frames" >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  qhdtm_x_assum `ifexp_copy_ptr_inv`
    (strip_assume_tac o REWRITE_RULE [ifexp_copy_ptr_inv_def]) >>
  simp[ifexp_copy_ptr_inv_def, IgnAsm `tn'.t_mem = _`] >>
  conj_tac >- (irule slot_copy_body_invariant >> simp[]) >>
  conj_tac >- (irule ifexp_copy_body_destination_coverage >> metis_tac[]) >>
  conj_tac >- (metis_tac[ifexp_copy_body_external_ghost]) >>
  conj_tac >- (gvs[slot_copy_external_def] >> metis_tac[]) >>
  reverse conj_tac >- suspend "ordinary" >>
  `!j k. j < SUC i /\ k < 32 /\ w2n d+32*j+k IN tn'.t_mem ==> (j,k) IN X`
    suffices_by simp[arithmeticTheory.ADD1] >>
  ho_match_mp_tac (INST_TYPE [alpha |-> ``:256``] ifexp_copy_body_taint_prefix) >>
  simp[] >> metis_tac[]
QED

Resume ifexp_copy_ptr_body[frames]:
  `!x. not_fresh_at sa x ==> !k. k<7 ==> x <> slot_copy_var cs k` by
    metis_tac[ifexp_copy_scratch_not_fresh] >>
  `!name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\ lookup_var v s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n (d+n2w i*32w) \/
     w2n (d+n2w i*32w)+32 <= w2n w)` by
    (ho_match_mp_tac ifexp_copy_interior_live_bounds >> simp[] >>
     rpt strip_tac >> qpat_x_assum `!name entry v sz w. _` drule_all >> simp[]) >>
  conj_tac
  >- (ho_match_mp_tac (INST_TYPE [alpha |-> ``:256``] ifexp_copy_body_ghost_inv) >>
      simp[IgnAsm `tn'.t_mem = _`, slot_copy_body_memory, slot_copy_body_sources] >>
      conj_tac >- fs[ifexp_copy_ptr_inv_def] >>
      conj_tac >- (qpat_x_assum `tn'.t_mem = _` mp_tac >> simp[]) >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  `ghost_kept ce es sa G0 tn0 s0 G tn` by fs[ifexp_copy_ptr_inv_def] >>
  drule_at (Pat `tn'.t_mem = _`)
    (INST_TYPE [alpha |-> ``:num # num``] ifexp_copy_body_ghost_kept) >>
  disch_then ho_match_mp_tac >>
  qexistsl_tac [`cs`, `G`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!aid off sz. _` drule_all >>
      strip_tac >> decide_tac) >>
  rpt strip_tac >> qpat_x_assum `!name pos len. _` drule_all >>
  strip_tac >> decide_tac
QED

Resume ifexp_copy_ptr_body[ordinary]:
  `w2n d+32*n < 2**256` by fs[slot_copy_inv_def] >>
  drule_all ifexp_slot_body_memory_frame >>
  disch_then (qspecl_then [`s`, `p`, `load`, `cs`] strip_assume_tac) >>
  simp[ifexp_slot_body_ordinary, ifexp_slot_copy_static] >>
  conj_tac
  >- (qpat_x_assum `LENGTH s.vs_memory <= LENGTH (slot_copy_body_result _ _ _ _ _ _).vs_memory`
        mp_tac >> simp[ifexp_slot_body_ordinary] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ (slot_copy_body_result _ _ _ _ _ _).vs_memory = _`
    (qspecl_then [`b'`, `len`] mp_tac) >>
  qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ s.vs_memory = _`
    (qspecl_then [`b'`, `len`] mp_tac) >> simp[ifexp_slot_body_ordinary]
QED

Finalise ifexp_copy_ptr_body
