(* Clean runtime forcing: code-aware allocation and copy composition. *)
Theory bodyIntCallForce
Ancestors
  bodyIntCallForceFrame loweringSlice exprLoweringProps
  exprSim exprSimOperands context compileEnv venomExecSemantics venomInst
  words finite_map list localPtrsProps venomState venomMemDefs loweringHalt
  exprSimWordArgs bodyIntCallCodeCopy fragExec freshWrites
  bodyIntCallCopyContent bodyIntCallStorageLayout

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
      regions_disjoint b n lo sz) /\
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
      regions_disjoint b n lo sz) /\
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

(* Allocation certificate with the full statement relation retained. *)
Theorem runtime_alloc_buffer_frag:
  !ctx func cenv cx es s0 n sm buf sb R.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
    n < dimword (:256) ==>
    frag_exec ctx sm sb (\s. s = s0)
      (\s. stmt_state_rel ctx func cenv cx es s /\
        ?b. eval_operand buf.buf_operand s = SOME (n2w b) /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,n) /\
        b + n < dimword (:256) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_memory = s0.vs_memory /\
        (!r. not_fresh_at sm r ==> lookup_var r s = lookup_var r s0) /\
        (!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) ==>
          FLOOKUP s.vs_allocas aid = SOME (p,sz)) /\
        (!name lo sz. local_region cenv es.scopes s name lo sz ==>
          regions_disjoint b n lo sz) /\
        (!aid p sz. aid < sm.cs_next_id /\
          FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
          regions_disjoint b n p sz)) R
Proof
  rpt strip_tac >> irule compile_alloc_buffer_frag >>
  qexistsl_tac [`buf`, `n`] >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all compile_alloc_buffer_step >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s'` by
    (irule compile_alloc_buffer_stmt_step >> metis_tac[]) >>
  qexists_tac `s'` >> simp[stmt_state_rel_inst_idx] >>
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
      regions_disjoint b n lo sz) /\
    (!aid lo sz. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (lo,sz) ==>
      regions_disjoint b n lo sz) /\
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
      qpat_x_assum `!aid lo sz. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  irule locals_kept_regions >> rpt strip_tac >>
  qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  qpat_x_assum `!name lo sz. _ ==> regions_disjoint _ _ _ _` drule >>
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
      regions_disjoint (w2n b) (type_memory_size tv) lo sz) /\
    (!aid lo sz. aid < sf.cs_next_id /\
      FLOOKUP sbase.vs_allocas aid = SOME (lo,sz) ==>
      regions_disjoint (w2n b) (type_memory_size tv) lo sz) ==>
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
  drule_all compile_storage_copy_content_frag >>
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
