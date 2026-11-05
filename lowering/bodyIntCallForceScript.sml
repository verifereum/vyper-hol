(* Clean runtime forcing: code-aware allocation and copy composition. *)
Theory bodyIntCallForce
Ancestors
  bodyIntCallForceFrame loweringSlice exprLoweringProps
  exprSim exprSimOperands context compileEnv venomExecSemantics venomInst
  words finite_map list localPtrsProps venomState venomMemDefs loweringHalt
  exprSimWordArgs bodyIntCallCodeCopy fragExec freshWrites
  bodyIntCallCopyContent bodyIntCallStorageLayout bodyIntCallArgLifetime
  loweringPosts valueEncodingProofs exprSafeOperand exprSimCopy
  immutableCopyExecution exprSimStorageCopy

(* Preserve the full statement relation across allocation, including replay.
   This supplements the destination-window contract, rather than rebuilding
   its individual invariant clauses at every aggregate-copy consumer. *)
Theorem compile_alloc_buffer_stmt_step:
  !ctx func cenv cx es s n sm buf sb s'.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
    step_inst_base
      (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sm.cs_next_var)]) s = OK s' ==>
    stmt_state_rel ctx func cenv cx es s'
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_member >> strip_tac >>
  `~not_fresh_at sm (STRING #"%" (toString sm.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sm.cs_next_var))` by
    metis_tac[fresh_not_local_ptr] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def] >> strip_tac >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  simp[mk_inst_def] >> metis_tac[mk_inst_def]
QED

(* Runtime copies cannot affect immutables: their image is in the data
   section. Only live-local byte agreement is needed for the memory part. *)
Theorem runtime_stmt_memory_frame:
  !ctx func cenv cx es s mem.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      mem_bytes_at b sz mem = mem_bytes_at b sz s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_memory := mem)
Proof
  rpt strip_tac >> irule stmt_state_rel_allocas_frame >>
  conj_tac
  >- (simp[immutable_alloca_sep_def] >>
      irule immutable_base_zero_frame >> qexists_tac `s` >>
      fs[stmt_state_rel_def, lookup_var_def]) >>
  simp[] >> conj_tac >- simp[immutable_alloca_sep_def] >>
  reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes (s with vs_memory := mem)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def, lookup_var_def] >>
     conj_tac
     >- (rpt strip_tac >> sym_tac >> first_x_assum irule >>
         goal_assum drule) >>
     rpt strip_tac >> gvs[]) >>
  irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`es`, `s`] >>
  fs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem runtime_stmt_memory_window:
  !ctx func cenv cx es s mem b n.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    (!name lo sz. local_region cenv es.scopes s name lo sz ==>
      compileEnv$regions_disjoint b n lo sz) /\
    (!off len. off+len <= b \/ b+n <= off ==>
      mem_bytes_at off len mem = mem_bytes_at off len s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_memory := mem)
Proof
  rpt strip_tac >> irule runtime_stmt_memory_frame >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_x_assum `!name lo sz. local_region _ _ _ name lo sz ==> _` drule >>
  simp[compileEnvTheory.regions_disjoint_def]
QED

(* Statement relations do not observe the instruction cursor. *)
Theorem stmt_state_rel_control:
  !ctx func cenv cx es s prev bb idx.
    stmt_state_rel ctx func cenv cx es
      (s with <|vs_prev_bb := prev; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
    stmt_state_rel ctx func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, fmp_room_def, accounts_rel_def]
QED

Theorem runtime_stmt_copy_frame:
  !ctx func cenv cx es sa s t b n.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    local_ptrs_reserved cenv sa /\
    (!name lo sz. local_region cenv es.scopes s name lo sz ==>
      compileEnv$regions_disjoint b n lo sz) /\
    (!off len. off+len <= b \/ b+n <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars;
      vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx|> = s ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_memory := t.vs_memory)` by
    (irule runtime_stmt_memory_window >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es
     (s with <|vs_memory := t.vs_memory; vs_vars := t.vs_vars|>)` by
    (drule stmt_state_rel_vars_frame >>
     disch_then (qspec_then `t.vs_vars` mp_tac) >>
     simp[] >> impl_tac >- (rpt strip_tac >>
       `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
       fs[lookup_var_def] >> metis_tac[lookup_var_def]) >> simp[]) >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _;
      vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s`
    (mp_tac o AP_TERM
      ``\u:venom_state. u with <|vs_memory := t.vs_memory; vs_vars := t.vs_vars;
        vs_prev_bb := t.vs_prev_bb; vs_current_bb := t.vs_current_bb;
        vs_inst_idx := t.vs_inst_idx|>``) >>
  simp[] >> disch_then SUBST1_TAC >>
  drule (iffRL (SPEC_ALL stmt_state_rel_control)) >>
  disch_then (qspecl_then [`t.vs_prev_bb`, `t.vs_inst_idx`, `t.vs_current_bb`] mp_tac) >>
  simp[]
QED

Theorem force_alloca_storage_frame[local]:
  step_inst_base (mk_inst aid ALLOCA [Lit allocsz] [out]) s = OK t ==>
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s
Proof
  simp[step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas aid` >>
  simp[AllCaseEqs(), update_var_def, contract_storage_def,
       contract_transient_def] >> rpt strip_tac >> gvs[]
QED

(* Allocation certificate with the full statement relation retained. *)
Theorem runtime_alloc_buffer_frag:
  !ctx func cenv cx es s0 n sm buf sb R.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
    n < dimword (:256) ==>
    frag_exec ctx sm sb (\s. s = s0)
      (\s. stmt_state_rel ctx func cenv cx es s /\
        contract_storage s = contract_storage s0 /\
        contract_transient s = contract_transient s0 /\
        ?b. eval_operand buf.buf_operand s = SOME (n2w b) /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,n) /\
        b + n < dimword (:256) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_memory = s0.vs_memory /\
        (!r. not_fresh_at sm r ==> lookup_var r s = lookup_var r s0) /\
        (!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) ==>
          FLOOKUP s.vs_allocas aid = SOME (p,sz)) /\
        (!name lo sz. local_region cenv es.scopes s name lo sz ==>
          compileEnv$regions_disjoint b n lo sz) /\
        (!aid p sz. aid < sm.cs_next_id /\
          FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
          compileEnv$regions_disjoint b n p sz)) R
Proof
  rpt strip_tac >> irule compile_alloc_buffer_frag >>
  qexistsl_tac [`buf`, `n`] >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all compile_alloc_buffer_step >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s'` by
    (irule compile_alloc_buffer_stmt_step >> metis_tac[]) >>
  drule force_alloca_storage_frame >>
  disch_then (strip_assume_tac o
    SRULE [contract_storage_def, contract_transient_def]) >>
  qexists_tac `s'` >>
  simp[stmt_state_rel_inst_idx, contract_storage_def, contract_transient_def] >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  fs[eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name lo sz. local_region _ _ s' name lo sz ==> _` irule >>
      gvs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* A separated copy preserves the existing expression-frame interface. The
   id cutoff is the beginning of the allocation, not the later copy loop. *)
Theorem runtime_copy_wb_frame:
  !cenv es sa s t b n.
    (!name lo sz. local_region cenv es.scopes s name lo sz ==>
      compileEnv$regions_disjoint b n lo sz) /\
    (!aid lo sz. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (lo,sz) ==>
      compileEnv$regions_disjoint b n lo sz) /\
    (!off len. off+len <= b \/ b+n <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas ==>
    wb_frame cenv es sa s t
Proof
  rpt gen_tac >> strip_tac >> simp[wb_frame_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _` irule >>
      qpat_x_assum `!aid lo sz. _ ==> compileEnv$regions_disjoint _ _ _ _` drule_all >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  irule locals_kept_regions >> rpt strip_tac >>
  qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  qpat_x_assum `!name lo sz. _ ==> compileEnv$regions_disjoint _ _ _ _` drule >>
  simp[compileEnvTheory.regions_disjoint_def]
QED

(* Typed immutable copy with both consumer-facing frames. *)
Theorem runtime_code_copy_framed_frag:
  !ctx func cenv cx es src dst tv v itv iv off k sf sa u sb sbase b R.
    compile_code_to_memory src dst ((type_memory_size tv+31) DIV 32) sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME (n2w (off+k)) /\
    eval_operand dst sbase = SOME b /\
    val_in_memory itv iv off sbase.vs_data_section /\
    sub_layout itv iv k tv v /\ value_has_type tv v /\
    off+type_memory_size itv < dimword (:256) /\
    w2n b+type_memory_size tv < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es sbase /\ ~cenv.ce_is_ctor /\
    local_ptrs_reserved cenv sa /\ sf.cs_next_var <= sa.cs_next_var /\
    (!name lo sz. local_region cenv es.scopes sbase name lo sz ==>
      compileEnv$regions_disjoint (w2n b) (type_memory_size tv) lo sz) /\
    (!aid lo sz. aid < sf.cs_next_id /\
      FLOOKUP sbase.vs_allocas aid = SOME (lo,sz) ==>
      compileEnv$regions_disjoint (w2n b) (type_memory_size tv) lo sz) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. val_in_memory tv v (w2n b) s.vs_memory /\
        stmt_state_rel ctx func cenv cx es s /\
        wb_frame cenv es sf sbase s) R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_code_to_memory_subvalue_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (fn th => irule frag_exec_conseq >> irule_at Any th) >>
  simp[] >> rpt strip_tac >> simp[]
  >- (irule runtime_stmt_copy_frame >> goal_assum drule >>
      qexistsl_tac [`w2n b`, `type_memory_size tv`, `sbase`, `sa`] >>
      simp[arithmeticTheory.ADD_COMM] >> conj_tac >> first_assum ACCEPT_TAC) >>
  irule runtime_copy_wb_frame >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (qexistsl_tac [`w2n b`, `type_memory_size tv`] >>
      simp[arithmeticTheory.ADD_COMM] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = _`
    (mp_tac o AP_TERM ``\s:venom_state. s.vs_allocas``) >> simp[]
QED

(* Typed transfer is independent of the source live-byte agreement proof:
   instantiate st with the backend image obtained from that agreement. *)
Theorem runtime_storage_copy_typed_frag:
  !ctx loc src dst tv v st sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    type_slot_size tv < dimword (:256) /\
    w2n b+32*type_slot_size tv < dimword (:256) /\
    well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
    decode_value st (w2n a) tv = SOME v /\
    (!j. j < type_slot_size tv ==>
      (if loc = LocStorage then sload (a+n2w j) sbase
       else tload (a+n2w j) sbase) = read_slot st (w2n a+j)) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. val_in_memory tv v (w2n b) s.vs_memory /\
        (!off len. off+len <= w2n b \/ w2n b+32*type_slot_size tv <= off ==>
          mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all bodyIntCallCopyContentTheory.compile_storage_copy_content_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (fn th => irule frag_exec_conseq >> irule_at Any th) >>
  simp[] >> rpt strip_tac >> simp[] >>
  irule decoded_copied_in_memory >> goal_assum drule >>
  qexistsl_tac [`w2n a`, `st`] >> simp[] >> metis_tac[]
QED

(* The ensure-in-memory singleton branch emits no loop. *)
Theorem runtime_storage_singleton_typed_frag:
  !ctx opc src dst tv v st sa u sb sbase a b R.
    (opc = SLOAD \/ opc = TLOAD) /\
    do value <- emit_op opc [src]; emit_void MSTORE [dst; value] od sa = (u,sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    type_slot_size tv = 1 /\ well_formed_type_value tv /\
    slots_in_range st (w2n a) tv /\ decode_value st (w2n a) tv = SOME v /\
    (if opc = SLOAD then sload a sbase else tload a sbase) =
      read_slot st (w2n a) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. val_in_memory tv v (w2n b) s.vs_memory /\
        (!off len. off+len <= w2n b \/ w2n b+32 <= off ==>
          mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all compile_storage_singleton_content_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (fn th => irule frag_exec_conseq >> irule_at Any th) >>
  simp[] >> rpt strip_tac >> simp[] >>
  irule decoded_copied_in_memory >> goal_assum drule >>
  qexistsl_tac [`w2n a`, `st`] >> simp[] >>
  rpt strip_tac >> `j = 0` by decide_tac >> gvs[]
QED

(* Check the singleton boundary and the strict proof dependencies used here. *)
val () = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print ("SINGLETON_FORCE_AUDIT " ^ name ^ " OK\n")
    else raise Fail (name ^ " has unproved dependencies")
  end)
  [("compile_storage_singleton_content_frag", compile_storage_singleton_content_frag),
   ("runtime_storage_singleton_typed_frag", runtime_storage_singleton_typed_frag),
   ("force_alloca_frame", force_alloca_frame),
   ("decoded_copied_in_memory", decoded_copied_in_memory),
   ("runtime_stmt_memory_frame", runtime_stmt_memory_frame),
   ("stmt_state_rel_control", stmt_state_rel_control)];

(* A copy's exact outside-window frame protects any held footprint covered
   by an old allocation or a live local. This uses the allocation-start
   cutoff, so it remains valid when ALLOCA replays an existing buffer. *)
Theorem force_copy_covered_window:
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!off len. off + len <= dst \/ dst + n <= off ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
  ((?aid b sz. aid < sm.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      b <= off /\ off + len <= b + sz) \/
   (?name b sz. local_region cenv es.scopes s0 name b sz /\
      b <= off /\ off + len <= b + sz) \/ len = 0) ==>
  mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac
  >- (first_x_assum irule >>
      `compileEnv$regions_disjoint dst n b sz` by metis_tac[] >>
      fs[compileEnvTheory.regions_disjoint_def] >> decide_tac)
  >- (first_x_assum irule >>
      `compileEnv$regions_disjoint dst n b sz` by metis_tac[] >>
      fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  simp[valueEncodingTheory.mem_bytes_at_def]
QED

Theorem force_copy_preserves_stack:
  vv_holds cenv cx ty raw (StackValue ty' op) es s0 /\
  vv_at cenv cx ty lo sm es raw (StackValue ty' op) s0 /\
  (!w. eval_operand op s0 = SOME w ==> eval_operand op s = SOME w) /\
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!off len. off + len <= dst \/ dst + n <= off ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  vv_holds cenv cx ty raw (StackValue ty' op) es s
Proof
  strip_tac >> gvs[vv_holds_def, expr_val_rel_def] >>
  gen_tac >> strip_tac >> Cases_on `is_word_type ty`
  >- gvs[] >>
  gvs[vv_at_def, expr_val_at_def] >>
  (irule val_in_memory_footprint_agree >> conj_tac >- simp[] >>
   qexists_tac `s0.vs_memory` >> simp[] >> sym_tac >>
   irule force_copy_covered_window >>
   goal_assum (drule_at Any) >> simp[] >>
   qexists_tac `sm` >> simp[] >> metis_tac[])
QED

Theorem force_copy_preserves_memory:
  vv_holds cenv cx ty raw (LocatedValue ty' p) es s0 /\
  vv_at cenv cx ty lo sm es raw (LocatedValue ty' p) s0 /\
  p.ptr_location = LocMemory /\
  (!w. eval_operand p.ptr_operand s0 = SOME w ==>
     eval_operand p.ptr_operand s = SOME w) /\
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!off len. off + len <= dst \/ dst + n <= off ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  vv_holds cenv cx ty raw (LocatedValue ty' p) es s
Proof
  strip_tac >> irule vv_holds_memory_footprint_frame >>
  conj_tac >- simp[] >> qexists_tac `s0` >> simp[] >>
  map_every qx_gen_tac [`v`, `tv`, `w`] >> strip_tac >>
  gvs[vv_at_def] >> sym_tac >>
  irule force_copy_covered_window >>
   goal_assum (drule_at Any) >> simp[] >>
   qexists_tac `sm` >> simp[] >> metis_tac[]
QED

Theorem force_copy_preserves_held:
  vv_holds cenv cx ty raw held es s0 /\
  vv_at cenv cx ty lo sm es raw held s0 /\
  (!w. eval_operand (vv_operand held) s0 = SOME w ==>
     eval_operand (vv_operand held) s = SOME w) /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!off len. off + len <= dst \/ dst + n <= off ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  vv_holds cenv cx ty raw held es s
Proof
  Cases_on `held` >> simp[vv_operand_def] >> strip_tac
  >- (irule force_copy_preserves_stack >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (irule force_copy_preserves_memory >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule vv_holds_nonmemory_frame >> metis_tac[]
QED

(* Pointwise transfer at a single, already selected allocation/copy endpoint.
   No independent frag_exec witnesses are combined by this boundary. *)
Theorem force_copy_held_entry:
  vv_holds cenv cx ty raw held es s0 /\
  vv_at cenv cx ty lo sm es raw held s0 /\
  safe_operand sm (vv_operand held) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  (!x. not_fresh_at sm x ==> lookup_var x s = lookup_var x s0) /\
  (!aid region. FLOOKUP s0.vs_allocas aid = SOME region ==>
     FLOOKUP s.vs_allocas aid = SOME region) /\
  (!name b sz. local_region cenv es.scopes s name b sz <=>
     local_region cenv es.scopes s0 name b sz) /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!off len. off + len <= dst \/ dst + n <= off ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  vv_holds cenv cx ty raw held es s /\
  vv_at cenv cx ty lo sb es raw held s /\
  safe_operand sb (vv_operand held)
Proof
  strip_tac >>
  `!w. eval_operand (vv_operand held) s0 = SOME w ==>
       eval_operand (vv_operand held) s = SOME w` by
    (rpt strip_tac >> irule safe_operand_value_preserved >>
     qexistsl_tac [`s0`, `sm`] >> simp[]) >>
  conj_tac
  >- (irule force_copy_preserves_held >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`dst`, `lo`, `n`, `sm`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (irule vv_at_region_frame >>
      qexistsl_tac [`sm`, `s0`] >> simp[]) >>
  metis_tac[safe_operand_mono]
QED

Theorem force_copy_held_prefix:
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es s0 /\
    vv_at cenv cx ty lo sm es raw held s0 /\
    safe_operand sm (vv_operand held)) hs /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  (!x. not_fresh_at sm x ==> lookup_var x s = lookup_var x s0) /\
  (!aid region. FLOOKUP s0.vs_allocas aid = SOME region ==>
     FLOOKUP s.vs_allocas aid = SOME region) /\
  (!name b sz. local_region cenv es.scopes s name b sz <=>
     local_region cenv es.scopes s0 name b sz) /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
     compileEnv$regions_disjoint dst n b sz) /\
  (!off len. off + len <= dst \/ dst + n <= off ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es s /\
    vv_at cenv cx ty lo sb es raw held s /\
    safe_operand sb (vv_operand held)) hs
Proof
  simp[listTheory.EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
  rename1 `MEM item hs` >> PairCases_on `item` >>
  first_x_assum drule >> simp[] >> strip_tac >>
  irule force_copy_held_entry >>
  qexistsl_tac [`dst`, `n`, `s0`, `sm`] >> simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The actual immutable-copy fragment carries its held prefix on the SAME
   endpoint as its memory/static/register certificate. The cutoff sf precedes
   the destination allocation; using mid here would include that buffer. *)
Theorem force_runtime_copy_held_frag:
  compile_imm_copy_to_memory F imm src dst nwords 0 mid = ((),sb) /\
  copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME b /\
  w2n a + 32 * nwords < dimword (:256) /\
  w2n b + 32 * nwords < dimword (:256) /\
  sf.cs_next_var <= mid.cs_next_var /\
  mid.cs_next_var <= sb.cs_next_var /\ sf.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sf /\
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es u /\
    vv_at cenv cx ty lo sf es raw held u /\
    safe_operand sf (vv_operand held)) hs /\
  (!aid p sz. aid < sf.cs_next_id /\
     FLOOKUP u.vs_allocas aid = SOME (p,sz) ==>
     compileEnv$regions_disjoint (w2n b) (32 * nwords) p sz) /\
  (!name p sz. local_region cenv es.scopes u name p sz ==>
     compileEnv$regions_disjoint (w2n b) (32 * nwords) p sz) ==>
  frag_exec ctx mid sb (\s. s = u)
    (\s. s.vs_memory = (immutable_transfers F F a b nwords 0 u).vs_memory /\
      copy_static s = copy_static u /\
      (!x. not_fresh_at mid x ==> lookup_var x s = lookup_var x u) /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sb es raw held s /\
        safe_operand sb (vv_operand held)) hs) R
Proof
  strip_tac >> drule_all copy_runtime_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  `!x. not_fresh_at sf x ==> lookup_var x s = lookup_var x u` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(!aid region. FLOOKUP u.vs_allocas aid = SOME region ==>
       FLOOKUP s.vs_allocas aid = SOME region) /\
   contract_storage s = contract_storage u /\
   contract_transient s = contract_transient u` by
    (gvs[copy_static_def, venom_state_component_equality] >>
     simp[contract_storage_def, contract_transient_def]) >>
  `!name p sz. local_region cenv es.scopes s name p sz <=>
               local_region cenv es.scopes u name p sz` by
    (rpt strip_tac >> irule local_region_pointer_frame >>
     rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  suspend "held_endpoint"
QED

Resume force_runtime_copy_held_frag[held_endpoint]:
  irule force_copy_held_prefix >>
  qexistsl_tac [`w2n b`, `32 * nwords`, `u`, `sf`] >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!name p sz. local_region _ _ _ name p sz ==> _` irule >>
    goal_assum (drule_at Any)) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid p sz. aid < _ /\ FLOOKUP _ aid = _ ==> _` irule >>
    goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `nwords = 0`
  >- gvs[immutable_transfers_def] >>
  `immutable_transfers F F a b nwords 0 u =
    write_memory_with_expansion (w2n b)
      (TAKE (32 * nwords) (DROP (w2n a) u.vs_data_section ++
        REPLICATE (32 * nwords) 0w)) u` by
    (qspecl_then [`nwords`, `w2n a`, `w2n b`, `0`, `u`] mp_tac
      immutable_runtime_transfers_snapshot >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]
QED
Finalise force_runtime_copy_held_frag

(* Replay-safe allocation retains both the old semantic certificate and the
   held entries at its one endpoint; no fresh-bump assumption is used. *)
Theorem force_alloc_buffer_held_frag:
  compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es s0 /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  n < dimword (:256) /\
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es s0 /\
    vv_at cenv cx ty lo sm es raw held s0 /\
    safe_operand sm (vv_operand held)) hs ==>
  frag_exec ctx sm sb (\s. s = s0)
    (\s. stmt_state_rel ctx func cenv cx es s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sm es raw held s /\
        safe_operand sm (vv_operand held)) hs /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sb es raw held s /\
        safe_operand sb (vv_operand held)) hs /\
      ?b. eval_operand buf.buf_operand s = SOME (n2w b) /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,n) /\
        b + n < dimword (:256) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_memory = s0.vs_memory /\
        (!r. not_fresh_at sm r ==> lookup_var r s = lookup_var r s0) /\
        (!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) ==>
          FLOOKUP s.vs_allocas aid = SOME (p,sz)) /\
        (!name lo sz. local_region cenv es.scopes s name lo sz ==>
          compileEnv$regions_disjoint b n lo sz) /\
        (!aid p sz. aid < sm.cs_next_id /\
          FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
          compileEnv$regions_disjoint b n p sz)) R
Proof
  strip_tac >> drule_all runtime_alloc_buffer_frag >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >> simp[] >>
  `sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by
    (qspecl_then [`n`, `sm`] mp_tac ci_mono_compile_alloc_buffer >>
     simp[ci_mono_def] >> gvs[]) >>
  `!name p sz. local_region cenv es.scopes s name p sz <=>
               local_region cenv es.scopes s0 name p sz` by
    (rpt strip_tac >> irule local_region_pointer_frame >>
     rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  suspend "alloc_endpoint"
QED

Resume force_alloc_buffer_held_frag[alloc_endpoint]:
  conj_tac >> irule force_copy_held_prefix >>
  qexistsl_tac [`0`, `0`, `s0`, `sm`] >>
  simp[compileEnvTheory.regions_disjoint_def] >>
  rpt strip_tac >> PairCases_on `region` >> metis_tac[]
QED
Finalise force_alloc_buffer_held_frag

(* One pointwise memory certificate serves both held framing and typed post
   reconstruction. It describes the actual emitted runtime immutable copy. *)
Theorem force_runtime_copy_window:
  z.vs_memory = (immutable_transfers F F a b nw 0 u).vs_memory /\
  w2n a + 32 * nw < dimword (:256) /\
  w2n b + 32 * nw < dimword (:256) ==>
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off + len <= w2n b \/ w2n b + 32 * nw <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> Cases_on `nw = 0`
  >- gvs[immutable_transfers_def] >>
  `immutable_transfers F F a b nw 0 u =
    write_memory_with_expansion (w2n b)
      (TAKE (32 * nw) (DROP (w2n a) u.vs_data_section ++
        REPLICATE (32 * nw) 0w)) u` by
    (qspecl_then [`nw`, `w2n a`, `w2n b`, `0`, `u`] mp_tac
      immutable_runtime_transfers_snapshot >> simp[]) >>
  gvs[] >> conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >>
  simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]
QED

(* Typed semantics is reconstructed on the very endpoint already carrying
   the held prefix. No second existential execution is combined with it. *)
Theorem force_runtime_copy_typed_endpoint:
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
  local_ptrs_reserved cenv sa /\ ~cenv.ce_is_ctor /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  stmt_state_rel ctx func cenv cx es' u /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sm.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    compileEnv$regions_disjoint (w2n w) (type_memory_size tv) b len) /\
  (!name b len. local_region cenv es'.scopes u name b len ==>
    compileEnv$regions_disjoint (w2n w) (type_memory_size tv) b len) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sm.cs_next_id /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
  copy_static z = copy_static u /\
  (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
  immutable_holds cenv cx (expr_type e) (Value v) a es' /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  z.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory /\
  eval_operand op z = SOME w ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  strip_tac >>
  drule_all copy_runtime_contents >> strip_tac >>
  `w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `LENGTH u.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (rewrite_tac[storageDecodeMemoryTheory.type_memory_size_slots] >>
     irule force_runtime_copy_window >>
     gvs[storageDecodeMemoryTheory.type_memory_size_slots] >>
     qexists_tac `a` >> simp[]) >>
  irule copy_buffer_post_transport >> simp[] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ u` (irule_at Any) >>
  qpat_assum `FLOOKUP u.vs_allocas _ = _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`mid`, `inst`] >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print ("HELD_FORCE_AUDIT " ^ name ^ " OK\n")
    else raise Fail (name ^ " has unproved dependencies")
  end)
  [("force_copy_held_prefix", force_copy_held_prefix),
   ("force_runtime_copy_held_frag", force_runtime_copy_held_frag),
   ("force_alloc_buffer_held_frag", force_alloc_buffer_held_frag),
   ("force_runtime_copy_window", force_runtime_copy_window),
   ("force_runtime_copy_typed_endpoint", force_runtime_copy_typed_endpoint)];

Theorem force_runtime_code_unwrap_held:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
        (LocatedValue t p) s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es' s /\
        vv_at cenv cx ty lo sm es' raw held s /\
        safe_operand sm (vv_operand held)) hs)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es' s /\
        vv_at cenv cx ty lo sb es' raw held s /\
        safe_operand sb (vv_operand held)) hs) R
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  irule frag_exec_pointwise >> qx_gen_tac `s1` >> simp[] >> strip_tac >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       immutable_holds cenv cx t (Value v) a es'` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv t < dimword (:256)` by decide_tac >>
  suspend "allocate"
QED

Resume force_runtime_code_unwrap_held[allocate]:
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = (_,sb)` >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sb` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid sb /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id /\
   mid.cs_next_var <= sb.cs_next_var` by gvs[ci_mono_def] >>
  `fn_has_code sm mid func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s1` by gvs[vv_post_def] >>
  drule_all exprSimAllocTheory.alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  suspend "allocated"
QED

Resume force_runtime_code_unwrap_held[allocated]:
  `!name b len. local_region cenv es'.scopes u name b len <=>
                local_region cenv es'.scopes s1 name b len` by
    (rpt strip_tac >> irule local_region_pointer_frame >>
     rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `EVERY (\(ty,raw,held,lo).
      vv_holds cenv cx ty raw held es' u /\
      vv_at cenv cx ty lo sm es' raw held u /\
      safe_operand sm (vv_operand held)) hs` by
    (irule force_copy_held_prefix >>
     qexistsl_tac [`0`, `0`, `s1`, `sm`] >>
     simp[compileEnvTheory.regions_disjoint_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv` by
    (simp[storageDecodeMemoryTheory.type_memory_size_slots] >> decide_tac) >>
  suspend "copy_ready"
QED

Resume force_runtime_code_unwrap_held[copy_ready]:
  qpat_assum `frag_exec ctx sm mid _ _ R` (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> simp[] >>
  `sm.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!aid b len. aid < sm.cs_next_id /\
     FLOOKUP u.vs_allocas aid = SOME (b,len) ==>
     compileEnv$regions_disjoint (w2n w) (type_memory_size tv) b len` by
    (rpt strip_tac >>
     irule exprSimPrecompilesTheory.state_allocations_disjoint >>
     goal_assum (drule_at Any) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ u` (irule_at Any) >>
     qexists_tac `sm.cs_next_id` >> simp[] >> decide_tac) >>
  qpat_x_assum `EVERY (\(ty,raw,held,lo).
    vv_holds _ _ _ _ _ _ s1 /\ _) hs` kall_tac >>
  qpat_x_assum `p.ptr_location = _` kall_tac >>
  qpat_x_assum `!tv. evaluate_type _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `frag_exec ctx sm mid _ _ R` kall_tac >>
  qpat_x_assum `ci_mono sm mid` kall_tac >>
  qpat_x_assum `ci_mono mid sb` kall_tac >>
  qpat_x_assum `!name b len. local_region _ _ u name b len <=> _` kall_tac >>
  gvs[storageDecodeMemoryTheory.type_memory_size_slots] >>
  `w2n a + 32 * type_slot_size tv < dimword (:256) /\
   w2n w + 32 * type_slot_size tv < dimword (:256)` by decide_tac >>
  `sm.cs_next_id <= sb.cs_next_id` by decide_tac >>
  drule_all force_runtime_copy_held_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  suspend "copy"
QED

Resume force_runtime_code_unwrap_held[copy]:
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> qx_gen_tac `z` >> strip_tac >> simp[] >>
  `eval_operand (Var p') z = SOME w` by
    (gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  drule_all compile_alloc_buffer_member >> strip_tac >>
  irule force_runtime_copy_typed_endpoint >> simp[] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ u` (irule_at Any) >>
  simp[storageDecodeMemoryTheory.type_memory_size_slots] >>
  qpat_assum `MEM _ (fn_insts func)` (irule_at Any) >>
  qexistsl_tac [`mid`, `a`] >>
  simp[mk_inst_def] >>
  suspend "typed_endpoint"
QED

Resume force_runtime_code_unwrap_held[typed_endpoint]:
  conj_tac >> first_assum ACCEPT_TAC
QED
Finalise force_runtime_code_unwrap_held
