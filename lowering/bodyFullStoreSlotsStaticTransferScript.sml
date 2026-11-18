Theory bodyFullStoreSlotsStaticTransfer
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExec ptrSafeRun ptrDiscipline
  gasEvents gasCount memSafeRun venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs
  list finite_map arithmetic

Theorem slots_static_operand[local,simp]:
  eval_operand op (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem slots_static_update_var[local,simp]:
  update_var x v (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  (update_var x v s) with vs_call_ctx :=
    ((update_var x v s).vs_call_ctx with cc_static := T)
Proof
  simp[update_var_def]
QED

Theorem slots_static_jump[local,simp]:
  jump_to lbl (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  (jump_to lbl s) with vs_call_ctx :=
    ((jump_to lbl s).vs_call_ctx with cc_static := T)
Proof
  simp[jump_to_def]
QED

Theorem slots_static_step_ok[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx inst s = OK u ==>
  step_inst fuel ctx inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  OK (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T))
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure1_def, exec_pure2_def, exec_read1_def, AllCaseEqs()] >>
  simp[mload_def]
QED

Theorem slots_static_phi[local,simp]:
  eval_one_phi (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) inst =
  eval_one_phi s inst
Proof
  simp[eval_one_phi_def]
QED

Theorem slots_static_phis[local]:
  !insts s u. eval_phis s insts = OK u ==>
  eval_phis (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) insts =
  OK (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T))
Proof
  Induct >> simp[eval_phis_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem slots_static_ranges[local,simp]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] ==>
  source_memory_read_ranges inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
    source_memory_read_ranges inst s /\
  source_memory_write_ranges inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
    source_memory_write_ranges inst s
Proof
  simp[MEM] >> strip_tac >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem slots_static_checks[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] ==>
  (access_ok lo G fn inst
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   access_ok lo G fn inst s) /\
  (taint_ok fn tn inst
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   taint_ok fn tn inst s) /\
  (mem_safe_step fuel ctx inst
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   mem_safe_step fuel ctx inst s)
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, in_revert_forward_def, about_to_revert_def] >>
  gvs[MEM, mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def]
QED

Theorem slots_readonly_step_frame:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] ==>
  (!u. step_inst fuel ctx inst s = OK u ==> u.vs_requests = s.vs_requests) /\
  (!u. step_inst fuel ctx inst s <> Halt u)
Proof
  simp[MEM] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure1_def, exec_pure2_def, exec_read1_def, AllCaseEqs(),
       update_var_def, jump_to_def] >>
  rpt strip_tac >> gvs[update_var_def, jump_to_def]
QED

Theorem slots_static_ptr_safe[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T))
Proof
  strip_tac >>
  drule slots_static_checks >> strip_tac >>
  drule slots_readonly_step_frame >> strip_tac >>
  qspec_then `s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)`
    mp_tac (GEN_ALL slots_readonly_step_frame) >>
  simp[] >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, allocas_from_def,
      allocas_below_fmp_def, MEM] >> metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem slots_static_ghost[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx inst s = OK u ==>
  ghost_step fuel ctx PG G tn inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  ghost_step fuel ctx PG G tn inst s
Proof
  strip_tac >> drule_all slots_static_step_ok >> strip_tac >>
  gvs[MEM, ghost_step_def, step_prov_def, out_prov_def,
      step_taint_def, adopt_reset_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, out_taint_def,
      store_taint_def, imm_taint_def, source_memory_write_ranges_def]
QED

Theorem slots_static_entry[local,simp]:
  entry_prov fn
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) G =
    entry_prov fn s G /\
  entry_taint_vars fn
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) tn =
    entry_taint_vars fn s tn
Proof
  simp[entry_prov_def, entry_taint_vars_def]
QED

Theorem store_slots_readonly_edge_static:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn') ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T),G,tn) []
    (OK (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T)),G',tn')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb1` (qx_choose_then `inst`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `?mid. middle = OK mid` by (gvs[exit_result_def] >> metis_tac[]) >>
  gnvs[Excl "MEM"] >>
  drule_all (SRULE[MEM] slots_static_step_ok) >> strip_tac >>
  `ghost_step fuel ctx PG G tn i
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   ghost_step fuel ctx PG G tn i s` by
    (irule slots_static_ghost >> simp[MEM] >> metis_tac[]) >>
  drule_all (SRULE[MEM] slots_static_ptr_safe) >> strip_tac >>
  drule (SRULE[MEM] slots_static_checks) >> strip_tac >>
  `gas_events_step fuel ctx func.fn_name i
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) = [] /\
   gas_count_step fuel ctx i
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) = 0` by
    (qpat_x_assum `_ = ASSIGN \/ _` mp_tac >> strip_tac >>
     simp[gas_events_step_def, gas_count_step_def]) >>
  qpat_x_assum `_ = ASSIGN \/ _` kall_tac >>
  rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> (conj_tac >- simp[]) >>
  qexistsl_tac [`fuel`, `bb`, `i`,
    `OK (mid with vs_call_ctx := (mid.vs_call_ctx with cc_static := T))`] >>
  simp[] >>
  qpat_x_assum `~is_terminator _ /\ _ \/ _` mp_tac >>
  strip_tac >> gvs[exit_result_def]
  >>~- ([`eval_phis mid target.bb_instructions = OK entered`],
    drule slots_static_phis >> strip_tac >> disj1_tac >>
    qexists_tac `entered with vs_call_ctx := (entered.vs_call_ctx with cc_static := T)` >>
    simp[venom_state_component_equality]) >>
  disj2_tac >> qexists_tac `lbl` >> simp[]
QED

Theorem store_slots_readonly_prefix_static:
  !L s G tn u G' tn' lo explicit ctx func PG.
    L <> [] /\ HD L = (s,G,tn) /\ LAST L = (u,G',tn') /\
    ~s.vs_halted /\
    (!D n a Ga tna b Gb tnb.
       SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\
       EL (SUC n) L = (b,Gb,tnb) ==>
       ?bb i.
         lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb a.vs_inst_idx = SOME i /\
         MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
         gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
           (a,Ga,tna) [] (OK b,Gb,tnb)) ==>
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T),G,tn) []
      (OK (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T)),G',tn')
Proof
  Induct_on `L` >- simp[] >>
  qx_gen_tac `head` >> Cases_on `L`
  >- (simp[] >> rpt strip_tac >> gvs[] >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[HD] >> PairCases_on `h` >>
  rename1 `LAST ((b,Gb,tnb)::t) = (u,G',tn')` >> gen_tac >>
  qpat_assum `!D n a Ga tna b Gb tnb. _`
    (qspecl_then [`D`, `0`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `bb` (qx_choose_then `i`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `~b.vs_halted` by
    (qpat_assum `gas_origin_ptr_edge _ _ [] (OK b,Gb,tnb)`
       (mp_tac o MATCH_MP gas_origin_ptr_edge_common_fuel) >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     fs[exit_result_def, jump_to_def] >>
     qpat_x_assum `OK b = _` (SUBST_ALL_TAC o SYM) >>
     fs[exit_result_def]) >>
  drule_all (SRULE[MEM] store_slots_readonly_edge_static) >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_edge _ (_ with vs_call_ctx := _,_,_) _ _`
    (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
  simp[] >> disch_then irule >>
  qpat_x_assum `!s G tn lo explicit ctx func PG. _` irule >>
  simp[] >>
  map_every qx_gen_tac [`horizon`, `n`, `a`, `Ga`, `tna`, `b1`, `Gb1`, `tnb1`] >>
  strip_tac >>
  qpat_x_assum `!D n a Ga tna b Gb tnb. _`
    (qspecl_then [`horizon`, `SUC n`] mp_tac) >>
  simp[]

QED
