Theory bodyFullStoreSlotsStaticRelabel
Ancestors
  exprSimAbiGasBridge exprSimAbiGasBridgeEdge typedCopyArrayPtr
  fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExec ptrSafeRun ptrDiscipline
  gasEvents gasCount memSafeRun venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs
  list finite_map arithmetic

Theorem slots_relabel_step_frame[local]:
  MEM inst.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE] ==>
  (!u. step_inst fuel ctx inst s = OK u ==> u.vs_requests = s.vs_requests) /\
  (!u. step_inst fuel ctx inst s <> Halt u)
Proof
  simp[MEM] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_ASSIGN, step_inst_base_ADD,
       step_inst_base_MUL, step_inst_base_EQ, step_inst_base_LT,
       step_inst_base_ISZERO, step_inst_base_SHR, step_inst_base_MLOAD,
       step_inst_base_JMP, step_inst_base_JNZ, step_inst_base_SSTORE,
       step_inst_base_TSTORE, exec_pure1_def, exec_pure2_def,
       exec_read1_def, exec_write2_def, AllCaseEqs(),
       update_var_def, jump_to_def, sstore_def, tstore_def] >>
  rpt strip_tac >> gvs[update_var_def, jump_to_def, sstore_def, tstore_def]
QED

Theorem slots_relabel_checks[local]:
  MEM inst.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE] /\
  ~in_revert_forward fn s ==>
  (access_ok lo G fn inst s ==>
   access_ok lo G fn' inst
     (s with <|vs_current_bb := b; vs_prev_bb := p|>)) /\
  (taint_ok fn tn inst s = taint_ok fn' tn inst
     (s with <|vs_current_bb := b; vs_prev_bb := p|>)) /\
  (mem_safe_step fuel ctx inst s = mem_safe_step fuel ctx inst
     (s with <|vs_current_bb := b; vs_prev_bb := p|>))
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, about_to_revert_def,
       frag_eval_operand_control] >>
  gvs[MEM, mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, frag_eval_operand_control] >>
  metis_tac[]
QED

Theorem slots_relabel_ptr_safe[local]:
  MEM inst.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE] /\
  ~in_revert_forward fn s /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
  ptr_safe_step D lo fuel ctx fn' PG G tn inst
    (s with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  strip_tac >>
  drule_all slots_relabel_checks >> strip_tac >>
  drule slots_relabel_step_frame >> strip_tac >>
  qspec_then `s with <|vs_current_bb := b; vs_prev_bb := p|>`
    mp_tac (GEN_ALL slots_relabel_step_frame) >>
  simp[] >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, allocas_from_def,
      allocas_below_fmp_def, MEM] >> metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem slots_relabel_ordinary_ghost[local]:
  MEM inst.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;SSTORE;TSTORE] /\
  step_inst fuel ctx inst s = OK u ==>
  ghost_step fuel ctx PG G tn inst
    (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
  ghost_step fuel ctx PG G tn inst s
Proof
  strip_tac >>
  `step_inst fuel ctx inst
     (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
   OK (u with <|vs_current_bb := b; vs_prev_bb := p|>)` by
    (gvs[MEM] >> simp[step_inst_non_invoke] >>
     irule (SRULE [] frag_relabel_base_nonphi) >>
     gvs[is_terminator_def, step_inst_non_invoke]) >>
  gvs[MEM, ghost_step_def, step_prov_def, out_prov_def,
      step_taint_def, adopt_reset_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, out_taint_def,
      store_taint_def, imm_taint_def, source_memory_write_ranges_def,
      frag_eval_operand_control, lookup_var_def]
QED

Theorem store_slots_relabel_checked_edge:
  frag_relabel_state L entry a v /\
  lookup_block a.vs_current_bb canon.fn_blocks = SOME cb /\
  get_instruction cb a.vs_inst_idx = SOME inst /\
  lookup_block v.vs_current_bb func.fn_blocks = SOME ab /\
  get_instruction ab v.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE] /\
  (MEM inst.inst_opcode [JMP;JNZ] ==> ~MEM (Label L) inst.inst_operands) /\
  (!lbl bb. lbl <> L /\ lookup_block lbl canon.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,canon,PG) (a,Ga,tna) [] (OK b,Gb,tnb) ==>
  ?w. frag_relabel_state L entry b w /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (v,Ga,tna) [] (OK w,Gb,tnb)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb1` (qx_choose_then `i`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  gnvs[Excl "MEM"] >>
  rename1 `get_instruction cb a.vs_inst_idx = SOME inst` >>
  `~revert_forward_at cb a.vs_inst_idx` by
    (strip_tac >> drule_all revert_forward_at_opcode >> gvs[MEM]) >>
  `~in_revert_forward canon a` by simp[in_revert_forward_def] >>
  qpat_x_assum `(?t. middle = OK t /\ ~is_terminator _ /\ _) \/ _`
    (mk_asm "shape") >>
  `(?t. step_inst fuel ctx inst a = OK t /\ ~is_terminator inst.inst_opcode /\
        ~t.vs_halted /\ b = t with vs_inst_idx := SUC a.vs_inst_idx /\
        (Gb,tnb) = ghost_step fuel ctx PG Ga tna inst a) \/
   (?lbl. is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst a = OK (jump_to lbl a) /\ b = jump_to lbl a /\
     lbl <> L /\ Gb = Ga /\ tnb = tna)` by suspend "normalize" >>
  asm_x "shape" kall_tac >>
  drule frag_relabel_state_fields >> strip_tac >>
  `ptr_safe_step D lo fuel ctx func PG Ga tna inst v` by
    (gvs[frag_relabel_state_def] >> irule (SRULE [] slots_relabel_ptr_safe) >>
     metis_tac[]) >>
  `mem_safe_step fuel ctx inst v` by
    (drule_all (SRULE [MEM] slots_relabel_checks) >> strip_tac >>
     gvs[frag_relabel_state_def] >> metis_tac[]) >>
  `gas_events_step fuel ctx func.fn_name inst v = [] /\
   gas_count_step fuel ctx inst v = 0` by
    (gvs[MEM] >> simp[gas_events_step_def, gas_count_step_def]) >>
  FIRST [qpat_assum `~is_terminator _` (fn _ => suspend "ordinary"),
         suspend "jump"]
QED

Resume store_slots_relabel_checked_edge[normalize]:
  asm_x "shape" strip_assume_tac
  >- metis_tac[]
  >- suspend "entry"
  >- suspend "raw" >>
  qpat_x_assum `exit_result _` mp_tac >>
  qpat_x_assum `OK b = _` (SUBST1_TAC o SYM) >>
  simp[exit_result_def]
QED

Resume store_slots_relabel_checked_edge[entry]:
  `MEM inst.inst_opcode [JMP;JNZ;DJMP]` by gvs[MEM,is_terminator_def] >>
  `t.vs_current_bb <> L` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`inst`,`a`] >> gvs[MEM] >>
     gvs[step_inst_non_invoke]) >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
  `entered = t` by metis_tac[eval_phis_no_phi, exec_result_11] >>
  `entry_prov canon t Ga = Ga /\ entry_taint_vars canon t tna = tna` by
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >> metis_tac[]) >>
  `?lbl. t = jump_to lbl a` by
    (qpat_x_assum `step_inst fuel ctx inst a = OK t` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke,step_inst_base_JMP,
       step_inst_base_JNZ,AllCaseEqs()] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `lbl` >> gvs[jump_to_def]
QED

Resume store_slots_relabel_checked_edge[raw]:
  `MEM inst.inst_opcode [JMP;JNZ;DJMP]` by gvs[MEM,is_terminator_def] >>
  `lbl <> L` by
    (`(jump_to lbl a).vs_current_bb <> L` by
      (irule frag_observer_jump_no_reentry >>
       qexistsl_tac [`inst`,`a`] >> gvs[MEM] >>
       gvs[step_inst_non_invoke]) >> gvs[jump_to_def]) >>
  disj2_tac >> qexists_tac `lbl` >> gvs[]
QED

Resume store_slots_relabel_checked_edge[ordinary]:
  `MEM inst.inst_opcode
     [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;SSTORE;TSTORE]` by
    gvs[MEM,is_terminator_def] >>
  gvs[frag_relabel_state_def] >>
  `step_inst fuel ctx inst
     (a with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb);
               vs_prev_bb := p|>) =
   OK (t with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb);
                vs_prev_bb := p|>)` by
    (gvs[MEM,step_inst_non_invoke] >>
     irule (SRULE [] frag_relabel_base_nonphi) >>
     gvs[is_terminator_def,step_inst_non_invoke]) >>
  `t.vs_current_bb = a.vs_current_bb` by
    (gvs[MEM,step_inst_non_invoke,step_inst_base_ASSIGN,step_inst_base_ADD,
         step_inst_base_MUL,step_inst_base_EQ,step_inst_base_LT,
         step_inst_base_ISZERO,step_inst_base_SHR,step_inst_base_MLOAD,
         step_inst_base_SSTORE,step_inst_base_TSTORE,
         exec_pure1_def,exec_pure2_def,exec_read1_def,exec_write2_def,
         AllCaseEqs(),update_var_def,sstore_def,tstore_def]) >>
  `ghost_step fuel ctx PG Ga tna inst
     (a with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb); vs_prev_bb := p|>) =
   ghost_step fuel ctx PG Ga tna inst a` by
    (irule slots_relabel_ordinary_ghost >> gvs[MEM] >> metis_tac[]) >>
  qexists_tac `t with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb);
                       vs_prev_bb := p; vs_inst_idx := SUC a.vs_inst_idx|>` >>
  (conj_tac
   >- (simp[frag_relabel_state_def] >> qexists_tac `p` >> simp[])) >>
  qpat_assum `(Gb,tnb) = _` (fn th => rewrite_tac [GSYM th]) >>
  simp[gas_origin_ptr_edge_def,gas_origin_edge_def,gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `fuel` >> gvs[] >>
  disj1_tac >> qexists_tac `t with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb); vs_prev_bb := p|>` >>
  simp[]
QED

Resume store_slots_relabel_checked_edge[jump]:
  `MEM inst.inst_opcode [JMP;JNZ;DJMP]` by gvs[MEM,is_terminator_def] >>
  `step_inst_base inst a = OK (jump_to lbl a)` by
    gvs[MEM,step_inst_non_invoke] >>
  gvs[frag_relabel_state_def] >>
  `step_inst_base inst
     (a with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb); vs_prev_bb := p|>) =
   OK ((jump_to lbl a) with vs_prev_bb := SOME (if a.vs_current_bb = L then entry else a.vs_current_bb))` by
    (irule frag_relabel_edge_jump_control >> simp[]) >>
  qexists_tac `jump_to lbl (a with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb); vs_prev_bb := p|>)` >>
  (conj_tac
   >- simp[frag_relabel_state_def,jump_to_def,venom_state_component_equality]) >>
  `step_inst fuel ctx inst
     (a with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb); vs_prev_bb := p|>) =
   OK (jump_to lbl (a with <|vs_current_bb := (if a.vs_current_bb = L then entry else a.vs_current_bb); vs_prev_bb := p|>))` by
    gvs[MEM,step_inst_non_invoke,jump_to_def] >>
  simp[gas_origin_ptr_edge_def,gas_origin_edge_def,gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `fuel` >> gvs[] >>
  disj2_tac >> disj1_tac >> qexists_tac `lbl` >> gvs[MEM]
QED

Finalise store_slots_relabel_checked_edge
