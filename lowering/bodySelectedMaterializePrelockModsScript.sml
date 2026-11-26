(* Assemble the selected callee's materialization and scratch on one run. *)
Theory bodySelectedMaterializePrelockMods
Ancestors
  bodyMaterializeParamsFullMods bodySelectedMaterializeStateFrameMods
  bodySelectedMaterializeSeparationMods bodySelectedEntryScratchMods
  bodyFullPostsMods bodyFullPathHistory bodyFullIfExpReach bodyMemoryDefs
  exprOpenPrimitives compileAllocaProvenance externalEntryShape
  freshWrites intCallCallee moduleLowering bodyInvSplit fragExec
  loweringPosts exprLoweringProps loweringStateRelDefs bodyPtrDefs
  vyperStorageFootprint vyperFiniteStoragePreservation rich_list
  emitHelper compileEnv finite_map venomInst words ASCIInumbers abiBufferAllocationCode
  list venomState venomMemProofs bodyFullShadowBodyInv venomExecSemantics ptrDiscipline
  fragGasOriginPtrLoop unitTransformDefs fragGasOriginPtr allocaHistory
  fragExecMem vyperState vyperTypeInvariants vyperTypeEvalProofs stmtSimProps pred_set

(* The immutable decoration is not read by the parameter compiler. *)
Theorem prelock_materialize_imm[local]:
  !caps ce st ce' st' imm.
    materialize_internal_params ce caps st = (ce',st') ==>
    materialize_internal_params (ce with ce_imm_alloca := imm) caps st =
      (ce' with ce_imm_alloca := imm,st')
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem prelock_materialize_code[local]:
  !caps ce st ce' st'.
    materialize_internal_params ce caps st = (ce',st') ==>
    st.cs_next_var <= st'.cs_next_var /\ ce' = ce with ce_vars := ce'.ce_vars /\
    ?new. st'.cs_current_insts = st.cs_current_insts ++ new /\
          EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = MSTORE) new
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[]) >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >> Cases_on `loc` >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      fs[] >>
      qmatch_asmsub_rename_tac `st'.cs_current_insts = _ ++ new` >>
      qexists_tac `[mk_inst st.cs_next_id ALLOCA [Lit (n2w n0)]
                    [STRING #"%" (toString st.cs_next_var)];
                    mk_inst (st.cs_next_id + 1) MSTORE
                      [Var (STRING #"%" (toString st.cs_next_var)); h2] []] ++ new` >>
      simp[mk_inst_def, APPEND_ASSOC]) >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem prelock_scratch_code[local]:
  (case rt of NONE => comp_return ()
   | SOME ty => if 0 < ce.ce_returns_count then
       comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
         (comp_return ()) else comp_return ()) materialized = ((),prologue) ==>
  prologue = materialized \/ ?n buf. compile_alloc_buffer n materialized = (buf,prologue)
Proof
  Cases_on `rt` >> simp[comp_return_def] >>
  IF_CASES_TAC >> simp[comp_return_def, comp_ignore_bind_def, comp_bind_def] >>
  rename1 `compile_alloc_buffer (type_memory_bytes ce ty) materialized` >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ty) materialized` >>
  simp[comp_return_def] >> strip_tac >> disj2_tac >>
  qexists_tac `type_memory_bytes ce ty` >> simp[]
QED

Theorem prelock_open_append[local]:
  ~block_is_terminated a /\ b.cs_current_insts = a.cs_current_insts ++ code /\
  EVERY (\i. ~is_terminator i.inst_opcode) code ==>
  ~block_is_terminated b
Proof
  strip_tac >> Cases_on `code = []` >- fs[block_is_terminated_def] >>
  `MEM (LAST code) code` by simp[LAST_MEM] >>
  `~is_terminator (LAST code).inst_opcode` by fs[EVERY_MEM] >>
  `b.cs_current_insts <> []` by simp[] >>
  `LAST b.cs_current_insts = LAST code` by simp[LAST_APPEND_NOT_NIL] >>
  qpat_x_assum `b.cs_current_insts = _` kall_tac >>
  Cases_on `b.cs_current_insts` >> fs[block_is_terminated_def]
QED

Theorem prelock_scratch_shape[local]:
  (prologue = materialized \/ ?n buf. compile_alloc_buffer n materialized = (buf,prologue)) ==>
  materialized.cs_next_var <= prologue.cs_next_var /\
  (~block_is_terminated materialized ==> ~block_is_terminated prologue)
Proof
  strip_tac >- simp[] >>
  drule_then strip_assume_tac compile_alloc_buffer_code >>
  conj_tac >- simp[] >> disch_tac >>
  irule prelock_open_append >> qexistsl_tac [`materialized`,`emitted_insts materialized prologue`] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem prelock_materialize_room[local]:
  run_inst_seq code s = OK raw /\
  EVERY (\i. MEM i (fn_insts callee) /\ i.inst_opcode <> INVOKE) code /\
  mat_frame reserved s raw /\ alloca_room ctx callee s /\ fmp_room ctx callee s /\
  at_mat = raw with vs_inst_idx := k ==>
  alloca_room ctx callee at_mat /\ fmp_room ctx callee at_mat
Proof
  strip_tac >>
  drule_all_then assume_tac run_inst_seq_alloca_room >>
  `raw.vs_fmp = s.vs_fmp` by
    (qpat_assum `mat_frame _ _ _` (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     qpat_assum `raw = _ with <|vs_vars := _; vs_memory := _; vs_allocas := _; vs_alloca_next := _|>`
       (once_rewrite_tac o single) >> simp[]) >>
  drule_all_then assume_tac run_inst_seq_fmp_room >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `raw` >> simp[]) >>
  qspecl_then [`ctx`,`callee`,`raw`,`at_mat`] mp_tac fmp_room_fields_cong >> simp[]
QED

Theorem prelock_mat_cursor[local]:
  mat_inv callee mat_ce penv materialized raw f0 mr /\ lo <= f0 /\
  at_mat = raw with vs_inst_idx := k ==>
  materialized.cs_next_id NOTIN FDOM at_mat.vs_allocas /\
  alloca_inv at_mat /\ allocas_from lo at_mat /\ lo <= at_mat.vs_alloca_next /\
  fresh_vars_wrt materialized at_mat /\
  (!i w b sz. MEM i (fn_insts callee) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\ FLOOKUP at_mat.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n w)
Proof
  simp[mat_inv_def, allocas_from_def, alloca_inv_set_inst_idx, fresh_vars_wrt_def] >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem prelock_body_ghost[local]:
  ghost_inv_at_mods D lo d ce p es G tn s ==>
  ghost_inv_at_mods D lo d (ce with ce_alloca_locals := T) p es G tn s
Proof
  Cases_on `d` >-
    (simp[ghost_inv_at_mods_def, return_buf_ptr_def, imm_section_dead_mods_def] >>
     strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  PairCases_on `x` >>
  simp[ghost_inv_at_mods_def, return_buf_ptr_def, imm_section_dead_mods_def] >>
  strip_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem prelock_fmp_floor[local]:
  ctx_has_dalloca ctx /\ alloca_inv s /\ fmp_room ctx callee s ==>
  allocas_below_fmp s
Proof
  simp[allocas_below_fmp_def, fmp_room_def,
       venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  strip_tac >>
  qpat_x_assum `ctx_has_dalloca ctx \/ _ ==> _` mp_tac >>
  simp[] >> strip_tac >> rpt strip_tac >>
  qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = _ ==> _`
    (drule_then strip_assume_tac) >> decide_tac
QED

Theorem prelock_noinvoke[local]:
  fn_has_code reserved materialized callee /\
  materialized.cs_current_insts = reserved.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = MSTORE) code ==>
  EVERY (\i. MEM i (fn_insts callee) /\ i.inst_opcode <> INVOKE) code /\
  EVERY (\i. ~is_terminator i.inst_opcode) code
Proof
  simp[EVERY_MEM] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >> conj_tac
      >- (drule fn_has_code_current_member >> disch_then irule >> simp[MEM_APPEND]) >>
      qpat_assum `!i. MEM i code ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  rpt strip_tac >> qpat_assum `!i. MEM i code ==> _` (drule_then strip_assume_tac) >>
  gvs[is_terminator_def]
QED

Theorem prelock_mat_reserve[local]:
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  ce1.ce_imm_alloca = NONE /\ ALL_DISTINCT (MAP FST caps) /\
  ALL_DISTINCT (MAP (SND o SND) caps) /\
  (!n b op. MEM (n,b,op) caps ==>
    (?off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz)) /\
    (?p. op = Var p /\ not_fresh_at reserved p)) /\
  (!n off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz) ==> MEM n (MAP FST caps)) /\
  (!n op sz. FLOOKUP ce1.ce_vars n <> SOME (PtrVar op sz)) ==>
  local_ptrs_reserved ce2 materialized
Proof
  strip_tac >> irule materialize_internal_params_reserved >>
  qexistsl_tac [`caps`,`ce1`,`reserved`] >> asm_rewrite_tac[] >> simp[]
QED

Theorem prelock_materialize_avoids[local]:
  !caps ce st ce' st' p.
    materialize_internal_params ce caps st = (ce',st') /\
    not_fresh_at st p /\ ~MEM (Var p) (MAP (SND o SND) caps) /\
    (!n sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var p) sz)) ==>
    !n sz. FLOOKUP ce'.ce_vars n <> SOME (PtrVar (Var p) sz)
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[]) >>
      Cases_on `x` >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >> simp[FLOOKUP_UPDATE] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      gvs[not_fresh_at_def, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_REFL,
                arithmeticTheory.LESS_EQ_ADD]) >>
  strip_tac >> first_x_assum drule >>
  simp[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem prelock_active_separation[local]:
  immutable_alloca_sep_mods func ce cx es s /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME tops ==>
  immutable_alloca_sep func ce cx es s
Proof
  simp[immutable_alloca_sep_mods_def] >> strip_tac >>
  first_x_assum drule >> simp[compile_env_component_equality]
QED

Theorem prelock_alloca_cases[local]:
  (!aid r. FLOOKUP mat.vs_allocas aid = SOME r ==> FLOOKUP pro.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP pro.vs_allocas aid = SOME (b,sz) /\
     FLOOKUP mat.vs_allocas aid = NONE ==> mat.vs_alloca_next <= b) ==>
  !aid b sz. FLOOKUP pro.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP mat.vs_allocas aid = SOME (b,sz) \/ mat.vs_alloca_next <= b
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  Cases_on `FLOOKUP mat.vs_allocas aid` >> metis_tac[optionTheory.SOME_11]
QED

Theorem prelock_param_counter[local]:
  !params idx st out st'.
    compile_internal_param_decls params idx st = (out,st') ==>
    st'.cs_next_var = st.cs_next_var + LENGTH params
Proof
  Induct >- simp[compile_internal_param_decls_def, comp_return_def] >>
  PairCases >>
  simp[compile_internal_param_decls_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_def, fresh_var_def, fresh_id_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem prelock_capture_layout[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) ==>
  MAP FST caps = MAP FST params /\ ce1.ce_imm_alloca = ce.ce_imm_alloca /\
  ce1.ce_module = ce.ce_module /\ ce1.ce_is_ctor = ce.ce_is_ctor /\
  ce1.ce_module_var_type = ce.ce_module_var_type /\
  capture.cs_next_var = entry.cs_next_var + (if has_rb then 1 else 0) + LENGTH params + 1
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, emit_def, fresh_var_def, fresh_id_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_internal_param_decls _ _ _ = (pr,mid)` >> PairCases_on `pr` >>
  drule_then strip_assume_tac internal_param_decls_projection >>
  drule_then assume_tac prelock_param_counter >> gvs[]
QED

Theorem prelock_capture_operands[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  MAP FST caps = MAP FST params ==>
  ALL_DISTINCT (MAP (SND o SND) caps) /\
  (!op. MEM op (MAP (SND o SND) caps) ==>
    ?q. op = Var q /\ not_fresh_at capture q)
Proof
  strip_tac >> `LENGTH caps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  drule_then strip_assume_tac compile_internal_entry_prefix_shape >>
  conj_tac
  >- (simp[EL_ALL_DISTINCT_EL_EQ, EL_MAP, combinTheory.o_DEF] >> rpt strip_tac >>
      qpat_assum `!i. i < LENGTH params ==> SND (SND (EL i caps)) = _`
        (fn th => imp_res_tac th) >> gvs[ASCIInumbersTheory.toString_inj]) >>
  drule_then strip_assume_tac prelock_capture_layout >>
  simp[MEM_MAP, MEM_EL, PULL_EXISTS, EL_MAP, combinTheory.o_DEF] >>
  rpt strip_tac >>
  qpat_assum `!i. i < LENGTH params ==> SND (SND (EL i caps)) = _`
    (drule_then (pure_once_rewrite_tac o single)) >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> decide_tac
QED

Theorem prelock_capture_coverage[local]:
  MAP FST (caps : (string # bool # operand) list) = MAP FST params /\ internal_args_rel ce1 params penv idx argv f0 mem /\
  (!i. i < LENGTH params ==> ?q. SND (SND (EL i caps)) = Var q /\ not_fresh_at reserved q) ==>
  !n b op. MEM (n,b,op) caps ==>
    (?off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz)) /\
    (?q. op = Var q /\ not_fresh_at reserved q)
Proof
  strip_tac >> `LENGTH caps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  simp[NoAsms, MEM_EL] >> rpt gen_tac >>
  disch_then (qx_choose_then `i` strip_assume_tac) >>
  `i < LENGTH params` by decide_tac >>
  `FST (EL i caps) = FST (EL i params)` by
    (qpat_assum `MAP FST caps = MAP FST params` (mp_tac o Q.AP_TERM `EL i`) >> simp[EL_MAP]) >>
  conj_tac
  >- (qpat_assum `internal_args_rel _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [internal_args_rel_def]) >>
      qpat_assum `!i. i < LENGTH params ==> ?off sz e. _` (drule_then strip_assume_tac) >>
      qpat_assum `(n,b,op) = EL i caps` (mp_tac o Q.AP_TERM `FST`) >>
      simp[NoAsms] >> disch_then SUBST1_TAC >>
      qpat_assum `FST (EL i caps) = FST (EL i params)` (pure_once_rewrite_tac o single) >>
      qexistsl_tac [`off`,`sz`] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i. i < LENGTH params ==> ?q. SND (SND (EL i caps)) = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `(n,b,op) = EL i caps` (mp_tac o Q.AP_TERM `SND o SND`) >>
  simp[NoAsms, combinTheory.o_DEF] >> disch_then SUBST1_TAC >>
  qexists_tac `q` >> simp[]
QED

Theorem prelock_capture_open[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  entry.cs_current_insts = [] ==> ~block_is_terminated capture
Proof
  strip_tac >> drule_then mp_tac compile_internal_entry_prefix_capture_code >>
  simp[emitted_insts_def, EVERY_MEM] >> strip_tac >>
  irule prelock_open_append >> qexistsl_tac [`entry`,`capture.cs_current_insts`] >>
  simp[block_is_terminated_def, EVERY_MEM] >>
  gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >> simp[is_terminator_def]
QED

Theorem prelock_reserve_open[local]:
  (if reserve then comp_bind (compile_fixed_region_with_id ilen)
      (\ar. comp_return (SOME (SND ar).buf_operand))
    else comp_return NONE) capture = (imm,reserved) /\
  ~block_is_terminated capture ==> ~block_is_terminated reserved
Proof
  reverse (Cases_on `reserve`) >> simp[comp_bind_def, comp_return_def]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >> PairCases_on `ar` >>
  drule_then strip_assume_tac contextTheory.compile_fixed_region_with_id_result >>
  irule prelock_open_append >> qexists_tac `capture` >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem prelock_imm_not_cap[local]:
  (imm = NONE \/ ?q. imm = SOME (Var q) /\ lookup_var q s = SOME 0w /\
     ~not_fresh_at capture q /\ not_fresh_at reserved q) /\
  (!op. MEM op (MAP (SND o SND) (caps : (string # bool # operand) list)) ==>
    ?q. op = Var q /\ not_fresh_at capture q) ==>
  !q. imm = SOME (Var q) ==> not_fresh_at reserved q /\ ~MEM (Var q) (MAP (SND o SND) caps)
Proof
  strip_tac >> rpt strip_tac >> gvs[] >>
  qpat_assum `!op. MEM op _ ==> _` (drule_then strip_assume_tac) >> gvs[]
QED

(* The capture and reserve facts refer to these exact compiler cuts. *)
Theorem selected_materialize_prelock_run_mods:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  (if ctor /\ 0 < ilen then comp_bind (compile_fixed_region_with_id ilen)
      (\ar. comp_return (SOME (SND ar).buf_operand))
    else comp_return NONE) capture = (imm,reserved) /\
  entry.cs_current_insts = [] /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  (case rt of NONE => comp_return ()
   | SOME ty => if 0 < ce.ce_returns_count then
       comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
         (comp_return ()) else comp_return ()) materialized = ((),prologue) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> /\
  fn_has_code reserved materialized callee /\ fn_has_code materialized prologue callee /\
  fn_inst_ids_distinct callee /\
  (!bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  p = cx with stk updated_by CONS key /\
  d = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK s,J,N)) /\
  entered.vs_allocas = FEMPTY /\ entered.vs_inst_idx = 0 /\
  (!fn inst u. frag_reachable ctx callee entered fn inst u ==> dalloca_fmp_headroom inst u) /\
  s = t with <|vs_vars := s.vs_vars; vs_params := s.vs_params;
               vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
               vs_prev_bb := s.vs_prev_bb; vs_halted := s.vs_halted;
               vs_allocas := s.vs_allocas; vs_call_entry_fmp := s.vs_call_entry_fmp;
               vs_return_pc_token := s.vs_return_pc_token|> /\
  ~s.vs_halted /\ s.vs_current_bb = reserved.cs_current_bb /\
  s.vs_inst_idx = LENGTH reserved.cs_current_insts /\ s.vs_allocas = FEMPTY /\
  entered.vs_alloca_next = t.vs_alloca_next /\ alloca_room ctx callee entered /\
  fmp_room ctx callee s /\ lo <= t.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size callee s <= w2n s.vs_initial_fmp) /\
  ret_pc_ok ce1 reserved s /\ return_buf_frame d ce1 reserved s /\
  (!q sz. ce1.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at reserved q) /\
  (!q sz. ce1.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at reserved q) /\
  (imm = NONE \/ ?q. imm = SOME (Var q) /\ lookup_var q s = SOME 0w /\
     ~not_fresh_at capture q /\ not_fresh_at reserved q) /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
  N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm /\
  ce.ce_imm_alloca = NONE /\ ALL_DISTINCT (MAP FST caps) /\
  internal_args_rel ce1 params penv idx argv t.vs_alloca_next s.vs_memory /\
  (!i. i < LENGTH params ==> ?q. SND (SND (EL i caps)) = Var q /\ not_fresh_at reserved q) /\
  (!n off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==> MEM n (MAP FST params)) /\
  (!n op sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar op sz)) /\
  mat_pending (ce1 with ce_imm_alloca := imm) penv reserved s t.vs_alloca_next mr caps /\
  mat_inv callee (ce1 with ce_imm_alloca := imm) penv reserved s t.vs_alloca_next mr /\
  (!n1 n2 b1 sz1 b2 sz2. n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
    regions_disjoint b1 sz1 b2 sz2) /\
  s.vs_alloca_next + internal_stack_size (ce1 with ce_imm_alloca := imm)
     (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256) /\
  es1.scopes = [penv] /\
  (!n e. FLOOKUP penv n = SOME e ==> value_has_type e.type e.value) /\
  EVERY (\c. op_taint N (SND (SND c)) = {} /\
     (!q off sz e. ~FST (SND c) /\ SND (SND c) = Var q /\
       FLOOKUP ce1.ce_vars (FST c) = SOME (MemLoc off sz) /\ FLOOKUP penv (FST c) = SOME e ==>
       ptr_covers J N q s sz /\ !w mem. lookup_var q s = SOME w /\
        mem_agree_outside N.t_mem s.vs_memory mem ==> val_in_memory e.type e.value (w2n w) mem)) caps /\
  (!H. valid_horizon p st0 H es1.storage_trace ==>
     ghost_inv_at_mods (DF H) lo d (ce1 with ce_imm_alloca := imm) p es1 J N s) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     state_rel H callee ce cx (es1 with scopes := []) t) /\
  (!H. valid_horizon p st0 H es1.storage_trace ==> storage_well_formed_on p es1 (FST H)) /\
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es1 t /\
  ce.ce_modules = ce1.ce_modules /\ ce.ce_module_vars = ce1.ce_module_vars /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME tops /\
  (ce.ce_is_ctor ==> !src m n tv v off.
     ALOOKUP ce.ce_modules src = SOME m /\
     FLOOKUP ce.ce_module_vars (src,n) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                NONE => FEMPTY | SOME imms => get_source_immutables src imms) n = SOME (tv,v) ==>
     off + type_memory_size tv <= lo) /\
  immutable_alloca_sep_mods caller cenv p old t /\
  cenv.ce_modules = ce1.ce_modules /\ cenv.ce_is_ctor = ce1.ce_is_ctor /\
  cenv.ce_module_vars = ce1.ce_module_vars /\ cenv.ce_module_var_type = ce1.ce_module_var_type /\
  old.immutables = es1.immutables /\
  idx = (if has_rb then 1 else 0) /\
  (!n b sz. mr n = SOME (b,sz) ==>
    ?i off. i < LENGTH params /\ ~SND (EL i params) /\ FST (EL i params) = n /\
       FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz) /\ b = w2n (EL (idx + i) argv)) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce1.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?inst base len. MEM inst (fn_insts caller) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (base,len) /\
      base <= w2n (EL (idx + i) argv) /\ w2n (EL (idx + i) argv) + sz <= base + len) /\
  (has_rb ==> ?base len. op_prov G (HD arg_ops) = SOME (base,len) /\
     base <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= base + len /\
     base + len <= t.vs_alloca_next /\ lo <= base) /\
  (has_rb ==> !i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce1.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     loweringStateRelDefs$regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
       (w2n (EL (1 + i) argv)) sz) ==>
  ?at_pro Gpro tnpro.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
        (s,J,N) [] (OK at_pro,Gpro,tnpro)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
        (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_pro,Gpro,tnpro)) /\
    ~at_pro.vs_halted /\ at_pro.vs_current_bb = prologue.cs_current_bb /\
    at_pro.vs_inst_idx = LENGTH prologue.cs_current_insts /\
    ~block_is_terminated prologue /\ fresh_vars_wrt prologue at_pro /\
    local_ptrs_reserved body_ce prologue /\ ret_pc_ok body_ce prologue at_pro /\
    (!q sz. body_ce.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
    (!q sz. body_ce.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
    return_buf_frame d body_ce prologue at_pro /\ return_buf_sep d body_ce es1 at_pro /\
    alloca_history callee at_pro /\ allocas_from lo at_pro /\
    t.vs_alloca_next <= at_pro.vs_alloca_next /\ allocas_from t.vs_alloca_next at_pro /\
    alloca_room ctx callee at_pro /\ fmp_room ctx callee at_pro /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp at_pro) /\
    (!fn inst u. frag_reachable ctx callee at_pro fn inst u ==> dalloca_fmp_headroom inst u) /\
    (!H. valid_horizon p st0 H es1.storage_trace ==>
       stmt_state_rel H ctx callee body_ce p es1 at_pro /\
       immutable_frame_mods callee body_ce p es1 at_pro /\
       storage_well_formed_on p es1 (FST H) /\ ghost_inv_at_mods (DF H) lo d body_ce p es1 Gpro tnpro at_pro) /\
    at_pro.vs_accounts = t.vs_accounts /\ at_pro.vs_transient = t.vs_transient /\
    at_pro.vs_call_ctx = t.vs_call_ctx /\ at_pro.vs_tx_ctx = t.vs_tx_ctx /\
    at_pro.vs_block_ctx = t.vs_block_ctx /\
    (!b sz. b + sz <= t.vs_alloca_next ==>
      mem_bytes_at b sz at_pro.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!i. i < t.vs_alloca_next ==> (i IN tnpro.t_mem <=> i IN tn.t_mem)) /\
    tnpro.t_stor = tn.t_stor /\ tnpro.t_trans = tn.t_trans /\ tnpro.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `c1 = ce1 with ce_imm_alloca := imm` >>
  qabbrev_tac `cm = ce2 with ce_imm_alloca := imm` >>
  qabbrev_tac `Ds = {DF H | valid_horizon p st0 H es1.storage_trace}` >>
  `materialize_internal_params c1 caps reserved = (cm,materialized)` by
    (simp[Abbr `c1`, Abbr `cm`] >> irule prelock_materialize_imm >> first_assum ACCEPT_TAC) >>
  qpat_assum `materialize_internal_params ce1 _ _ = _`
    (fn th => mp_tac (MATCH_MP prelock_materialize_code th)) >> strip_tac >>
  drule_all_then strip_assume_tac prelock_noinvoke >>
  `!i. MEM i (DROP (LENGTH reserved.cs_current_insts) materialized.cs_current_insts) ==>
       MEM i (fn_insts callee)` by fs[DROP_LENGTH_APPEND, EVERY_MEM] >>
  `s.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `s = t with <|vs_vars := _; vs_params := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _; vs_halted := _; vs_allocas := _;
       vs_call_entry_fmp := _; vs_return_pc_token := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `s.vs_memory = t.vs_memory /\ s.vs_data_section = t.vs_data_section` by
    (qpat_assum `s = t with <|vs_vars := _; vs_params := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _; vs_halted := _; vs_allocas := _;
       vs_call_entry_fmp := _; vs_return_pc_token := _|>` (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
  `immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es1 s` by
    (simp[NoAsms, immutables_rel_mods_def, immutables_rel_def] >>
     qpat_assum `s.vs_memory = t.vs_memory` (pure_once_rewrite_tac o single) >>
     qpat_assum `s.vs_data_section = t.vs_data_section` (pure_once_rewrite_tac o single) >>
     qpat_assum `immutables_rel_mods ce _ _ es1 t` mp_tac >>
     simp[NoAsms, immutables_rel_mods_def, immutables_rel_def]) >>
  `alloca_room ctx callee s` by
    (irule alloca_room_fields >> qexists_tac `entered` >>
     qpat_assum `s.vs_allocas = FEMPTY` (pure_once_rewrite_tac o single) >>
     qpat_assum `entered.vs_allocas = FEMPTY` (pure_once_rewrite_tac o single) >>
     qpat_assum `s.vs_alloca_next = t.vs_alloca_next` (pure_once_rewrite_tac o single) >>
     qpat_assum `entered.vs_alloca_next = t.vs_alloca_next` (pure_once_rewrite_tac o single) >>
     simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac prelock_capture_open >>
  drule_all_then assume_tac prelock_reserve_open >>
  drule_then strip_assume_tac prelock_capture_layout >>
  qpat_assum `ce1.ce_module = ce.ce_module` (assume_tac o SYM) >>
  qpat_assum `ce1.ce_is_ctor = ce.ce_is_ctor` (assume_tac o SYM) >>
  drule_then strip_assume_tac compile_internal_entry_prefix_shape >>
  drule_all_then strip_assume_tac prelock_capture_operands >>
  `!n b op. MEM (n,b,op) caps ==>
     (?off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz)) /\
     (?q. op = Var q /\ not_fresh_at reserved q)` by
    (mp_tac (Q.INST [`f0` |-> `t.vs_alloca_next`, `mem` |-> `s.vs_memory`] prelock_capture_coverage) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `!n off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz) ==> MEM n (MAP FST caps)` by
    (qpat_assum `ce1.ce_vars = ce.ce_vars` (pure_once_rewrite_tac o single) >>
     qpat_assum `MAP FST caps = MAP FST params` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `!n op sz. FLOOKUP ce1.ce_vars n <> SOME (PtrVar op sz)` by
    (qpat_assum `ce1.ce_vars = ce.ce_vars` (pure_once_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `ce1.ce_imm_alloca = NONE` by
    (qpat_assum `ce1.ce_imm_alloca = ce.ce_imm_alloca` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `!q. imm = SOME (Var q) ==> not_fresh_at reserved q /\ ~MEM (Var q) (MAP (SND o SND) caps)` by
    (mp_tac (Q.INST [`s` |-> `s`, `capture` |-> `capture`] prelock_imm_not_cap) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `!D. D IN Ds ==> ghost_inv_at_mods D lo d c1 p es1 J N s` by
    (simp[NoAsms, Abbr `Ds`] >> rpt strip_tac >>
     qpat_x_assum `D = DF H` SUBST_ALL_TAC >> first_assum MATCH_MP_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `materialize_internal_params c1 _ _ = _`
    (mp_then (Pos hd) mp_tac materialize_params_full_mods) >>
  disch_then (qspecl_then [`callee`,`penv`,`s`,`t.vs_alloca_next`,`mr`,`ctx`,`lo`,`d`,
      `p`,`es1`,`MAP (op_prov G) arg_ops`,`J`,`N`,`Ds`,`explicit`] mp_tac) >>
  (impl_tac >- suspend "materialize_inputs") >>
  disch_then (qx_choose_then `raw` (qx_choose_then `at_mat` (qx_choose_then `Jm`
    (qx_choose_then `Nm` strip_assume_tac)))) >>
  suspend "after_materialize"
QED

Resume selected_materialize_prelock_run_mods[materialize_inputs]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[NoAsms, Abbr `c1`] >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt gen_tac >> disch_tac >>
  TRY (qpat_assum `!q. imm = SOME (Var q) ==> _` (drule_then strip_assume_tac) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  metis_tac[]
QED

Resume selected_materialize_prelock_run_mods[after_materialize]:
  `body_ce = cm with ce_alloca_locals := T` by simp[Abbr `cm`] >>
  `local_ptrs_reserved ce2 materialized` by
    (irule prelock_mat_reserve >> qexistsl_tac [`caps`,`ce1`,`reserved`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cm materialized` by
    (simp[NoAsms, Abbr `cm`, local_ptrs_reserved_def] >>
     `!x. imm = SOME (Var x) ==> not_fresh_at materialized x /\
       !n sz. FLOOKUP ce2.ce_vars n <> SOME (PtrVar (Var x) sz)` by
       (gen_tac >> disch_tac >>
        qpat_assum `!q. imm = SOME (Var q) ==> _` (drule_then strip_assume_tac) >>
        conj_tac >- (irule not_fresh_at_mono >> qexists_tac `reserved` >> asm_rewrite_tac[]) >>
        irule prelock_materialize_avoids >> qexistsl_tac [`caps`,`ce1`,`reserved`,`materialized`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        rpt gen_tac >> qpat_assum `!n op sz. FLOOKUP ce1.ce_vars n <> SOME (PtrVar op sz)`
          MATCH_ACCEPT_TAC) >>
     qpat_assum `local_ptrs_reserved ce2 materialized` (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     strip_tac >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!n1 n2 q sz1 sz2. FLOOKUP ce2.ce_vars n1 = _ ==> _`
       (drule_then (qspecl_then [`n2`,`sz2`] mp_tac)) >> simp[]) >>
  `local_ptrs_reserved body_ce materialized` by
    (qpat_assum `body_ce = cm with ce_alloca_locals := T` (pure_rewrite_tac o single) >>
     pure_rewrite_tac[local_ptrs_reserved_def, compile_env_accfupds] >>
     qpat_assum `local_ptrs_reserved cm materialized`
       (ACCEPT_TAC o PURE_REWRITE_RULE [local_ptrs_reserved_def])) >>
  `alloca_room ctx callee at_mat /\ fmp_room ctx callee at_mat` by
    (irule prelock_materialize_room >>
     qexistsl_tac [`DROP (LENGTH reserved.cs_current_insts) materialized.cs_current_insts`,
       `LENGTH materialized.cs_current_insts`,`raw`,`reserved`,`s`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `materialized.cs_current_insts = reserved.cs_current_insts ++ new`
       (once_rewrite_tac o single) >> simp[DROP_LENGTH_APPEND]) >>
  drule_all_then strip_assume_tac prelock_mat_cursor >>
  `local_ptrs_rel callee cm es1.scopes at_mat` by
    (qpat_assum `mat_inv callee cm _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     simp[localPtrsPropsTheory.local_ptrs_rel_inst_idx]) >>
  drule_then assume_tac prelock_scratch_code >>
  `!H. valid_horizon p st0 H es1.storage_trace ==> ghost_inv_at_mods (DF H) lo d cm p es1 Jm Nm at_mat` by
    (gen_tac >> disch_tac >> qpat_assum `!D. D IN Ds ==> ghost_inv_at_mods D _ _ cm _ _ _ _ _` irule >>
     simp[NoAsms, Abbr `Ds`] >> qexists_tac `H` >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`sa` |-> `materialized`, `sb` |-> `prologue`,
     `s` |-> `at_mat`, `func` |-> `callee`, `cenv` |-> `cm`,
     `cx` |-> `p`, `es` |-> `es1`, `G` |-> `Jm`, `tn` |-> `Nm`,
     `PG` |-> `MAP (op_prov G) arg_ops`] selected_entry_scratch_run_mods) >>
  impl_tac
  >- (conj_tac
      >- (qpat_x_assum `prologue = materialized \/ _` strip_assume_tac
          >- (disj1_tac >> first_assum ACCEPT_TAC) >>
          disj2_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          rename1 `compile_alloc_buffer n materialized = (buf,prologue)` >>
          qexistsl_tac [`n`,`buf`] >> first_assum ACCEPT_TAC) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      disch_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp at_mat /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `at_pro` (qx_choose_then `Gpro`
    (qx_choose_then `tnpro` strip_assume_tac))) >>
  suspend "finish_prelock"
QED

Resume selected_materialize_prelock_run_mods[finish_prelock]:
  `body_ce.ce_vars = cm.ce_vars` by
    (qpat_assum `body_ce = cm with ce_alloca_locals := T`
      (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
  `ce1.ce_modules = body_ce.ce_modules /\
   ce1.ce_module_vars = body_ce.ce_module_vars /\
   ce1.ce_module_var_type = body_ce.ce_module_var_type /\
   ce1.ce_module = body_ce.ce_module /\
   ce1.ce_is_ctor = body_ce.ce_is_ctor /\
   ce1.ce_return_pc = body_ce.ce_return_pc /\
   ce1.ce_return_buf = body_ce.ce_return_buf /\
   body_ce.ce_imm_alloca = imm` by
    (qpat_assum `body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>` (pure_once_rewrite_tac o single) >>
     qpat_assum `ce2 = ce1 with ce_vars := ce2.ce_vars`
       (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
  `!q. not_fresh_at materialized q ==> lookup_var q at_pro = lookup_var q at_mat` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at materialized x ==> _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`at_reserve` |-> `s`, `mat_state` |-> `raw`,
     `mat_ce` |-> `cm`, `f0` |-> `t.vs_alloca_next`,
     `idx` |-> `LENGTH materialized.cs_current_insts`]
     selected_materialize_state_frame_mods) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_assum `ce1.ce_modules = body_ce.ce_modules` (pure_once_rewrite_tac o single o SYM) >>
           qpat_assum `ce1.ce_module_vars = body_ce.ce_module_vars` (pure_once_rewrite_tac o single o SYM) >>
           qpat_assum `ce1.ce_module = body_ce.ce_module` (pure_once_rewrite_tac o single o SYM) >>
           qpat_assum `ce1.ce_is_ctor = body_ce.ce_is_ctor` (pure_once_rewrite_tac o single o SYM)) >>
      TRY (qpat_assum `ce.ce_modules = ce1.ce_modules` (pure_once_rewrite_tac o single o SYM) >>
           qpat_assum `ce.ce_module_vars = ce1.ce_module_vars` (pure_once_rewrite_tac o single o SYM) >>
           qpat_assum `ce.ce_module = ce1.ce_module` (pure_once_rewrite_tac o single o SYM) >>
           qpat_assum `ce.ce_is_ctor = ce1.ce_is_ctor` (pure_once_rewrite_tac o single o SYM)) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[]) >>
  strip_tac >>
  `!H. valid_horizon p st0 H es1.storage_trace ==>
       state_rel H callee body_ce p es1 at_pro` by
    (qpat_assum `p = cx with stk updated_by CONS key` (pure_once_rewrite_tac o single) >>
     qpat_assum `!k H. valid_horizon (cx with stk updated_by CONS k) _ H _ ==> _`
       (qspec_then `key` ACCEPT_TAC)) >>
  `!q. not_fresh_at materialized q ==> lookup_var q at_pro = lookup_var q raw` by
    (gen_tac >> disch_tac >>
     qpat_assum `!q. not_fresh_at materialized q ==> lookup_var q at_pro = lookup_var q at_mat`
       (drule_then (pure_once_rewrite_tac o single)) >>
     qpat_assum `at_mat = raw with vs_inst_idx := _` (pure_once_rewrite_tac o single) >>
     simp[NoAsms, lookup_var_def]) >>
  `raw.vs_alloca_next = at_mat.vs_alloca_next /\ raw.vs_allocas = at_mat.vs_allocas` by
    (qpat_assum `at_mat = raw with vs_inst_idx := _` (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
  mp_tac (Q.INST [`cx` |-> `p`, `es` |-> `es1`, `f0` |-> `t.vs_alloca_next`,
     `mat_ce` |-> `cm`, `mat_state` |-> `raw`, `ce_args` |-> `ce1`, `dret` |-> `d`]
     selected_materialize_separation_mods) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_assum `raw.vs_alloca_next = at_mat.vs_alloca_next` (pure_once_rewrite_tac o single) >>
           qpat_assum `raw.vs_allocas = at_mat.vs_allocas` (pure_once_rewrite_tac o single) >>
           first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_assum `ce1.ce_modules = body_ce.ce_modules` (pure_once_rewrite_tac o single o SYM) >>
      qpat_assum `ce1.ce_module_vars = body_ce.ce_module_vars` (pure_once_rewrite_tac o single o SYM) >>
      qpat_assum `ce1.ce_module_var_type = body_ce.ce_module_var_type` (pure_once_rewrite_tac o single o SYM) >>
      qpat_assum `ce1.ce_is_ctor = body_ce.ce_is_ctor` (pure_once_rewrite_tac o single o SYM) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[NoAsms] >>
      qpat_assum `raw.vs_alloca_next = at_mat.vs_alloca_next` (pure_once_rewrite_tac o single) >>
      qpat_assum `raw.vs_allocas = at_mat.vs_allocas` (pure_once_rewrite_tac o single) >>
      mp_tac (Q.INST [`mat` |-> `at_mat`,`pro` |-> `at_pro`] prelock_alloca_cases) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  strip_tac >>
  suspend "resources"
QED

Resume selected_materialize_prelock_run_mods[resources]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
      (s,J,N) [] (OK at_pro,Gpro,tnpro)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Jm`,`at_mat`,`Nm`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_pro,Gpro,tnpro)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`J`,`s`,`N`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `!D. gas_origin_ptr_path _ (entered,_,_) [] (OK at_pro,_,_)`
    (qspec_then `ARB` assume_tac) >>
  `alloca_history callee entered /\ alloca_inv entered` by
    (conj_tac >- (irule alloca_history_empty >> conj_tac >> first_assum ACCEPT_TAC) >>
     irule alloca_inv_empty_proof >> first_assum ACCEPT_TAC) >>
  `alloca_history callee at_pro` by
    (qpat_assum `gas_origin_ptr_path _ (entered,_,_) [] (OK at_pro,_,_)`
       (mp_then Any irule body_full_path_alloca_history) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!fn inst u. frag_reachable ctx callee at_pro fn inst u ==> dalloca_fmp_headroom inst u` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `gas_origin_ptr_path _ (entered,_,_) [] (OK at_pro,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (qspecl_then [`fn`,`inst`,`u`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  drule_then strip_assume_tac prelock_scratch_shape >>
  `~block_is_terminated prologue` by
    (qpat_assum `~block_is_terminated materialized ==> _` irule >>
     irule prelock_open_append >> qexistsl_tac [`reserved`,`new`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `reserved.cs_next_var <= prologue.cs_next_var` by decide_tac >>
  `local_ptrs_reserved body_ce prologue` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `materialized` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fresh_vars_wrt prologue at_pro` by
    (qpat_assum `fresh_vars_wrt materialized at_mat ==> _` irule >> first_assum ACCEPT_TAC) >>
  `!q. not_fresh_at reserved q ==> lookup_var q at_pro = lookup_var q s` by
    (gen_tac >> disch_tac >>
     `not_fresh_at materialized q` by
       (irule not_fresh_at_mono >> qexists_tac `reserved` >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!q. not_fresh_at materialized q ==> lookup_var q at_pro = lookup_var q raw`
       (drule_then (pure_once_rewrite_tac o single)) >>
     qpat_assum `mat_frame reserved s raw` (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     qpat_assum `!q. not_fresh_at reserved q ==> lookup_var q raw = _`
       (drule_then ACCEPT_TAC)) >>
  `!q w. not_fresh_at reserved q /\ lookup_var q s = SOME w ==>
     lookup_var q at_pro = SOME w` by
    (rpt strip_tac >> qpat_assum `!q. not_fresh_at reserved q ==> lookup_var q at_pro = _`
       (drule_then (pure_once_rewrite_tac o single)) >> first_assum ACCEPT_TAC) >>
  `ret_pc_ok body_ce prologue at_pro` by
    (qpat_assum `ret_pc_ok ce1 reserved s` (mp_then Any irule ret_pc_ok_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d body_ce prologue at_pro` by
    (qpat_assum `return_buf_frame d ce1 reserved s` (mp_then Any irule return_buf_frame_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (decide_tac >> NO_TAC) >> sym_tac >> first_assum ACCEPT_TAC) >>
  suspend "finish_frames"
QED

Resume selected_materialize_prelock_run_mods[finish_frames]:
  qpat_assum `at_pro with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = at_mat`
    (strip_assume_tac o SRULE [NoAsms, venom_state_component_equality]) >>
  `s.vs_memory = t.vs_memory /\ s.vs_labels = t.vs_labels` by
    (qpat_assum `s = t with <|vs_vars := _; vs_params := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _; vs_halted := _; vs_allocas := _;
       vs_call_entry_fmp := _; vs_return_pc_token := _|>` (pure_once_rewrite_tac o single) >>
     simp[NoAsms]) >>
  `raw.vs_labels = s.vs_labels` by
    (qpat_assum `mat_frame reserved s raw` (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     qpat_assum `raw = s with <|vs_vars := _; vs_memory := _; vs_allocas := _; vs_alloca_next := _|>`
       (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
  `at_pro.vs_labels = t.vs_labels` by
    (qpat_assum `at_pro.vs_labels = at_mat.vs_labels` (pure_once_rewrite_tac o single) >>
     qpat_assum `at_mat = raw with vs_inst_idx := _` (pure_once_rewrite_tac o single) >>
     simp[NoAsms, venom_state_accfupds] >>
     qpat_assum `raw.vs_labels = s.vs_labels` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `!b n. b + n <= t.vs_alloca_next ==>
     mem_bytes_at b n at_pro.vs_memory = mem_bytes_at b n t.vs_memory` by
    (qpat_assum `at_pro.vs_memory = at_mat.vs_memory` (pure_once_rewrite_tac o single) >>
     qpat_assum `at_mat = raw with vs_inst_idx := _` (pure_once_rewrite_tac o single) >>
     pure_rewrite_tac[venom_state_accfupds] >>
     qpat_assum `s.vs_memory = t.vs_memory` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `s.vs_alloca_next = t.vs_alloca_next` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `mat_frame reserved s raw` (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `!i. i < t.vs_alloca_next ==> (i IN tnpro.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i IN tnpro.t_mem <=> _` (qspec_then `i` (pure_once_rewrite_tac o single)) >>
     `i < s.vs_alloca_next /\ i < at_mat.vs_alloca_next` by decide_tac >>
     qpat_assum `!i. i < s.vs_alloca_next ==> _` (drule_then (pure_once_rewrite_tac o single)) >>
     qpat_assum `N.t_mem = tn.t_mem` (pure_once_rewrite_tac o single) >>
     `~(at_mat.vs_alloca_next <= i)` by decide_tac >>
     qpat_assum `~(at_mat.vs_alloca_next <= i)` (simp_tac bool_ss o single)) >>
  suspend "finish_horizons"
QED

Resume selected_materialize_prelock_run_mods[finish_horizons]:
  `immutable_alloca_sep callee body_ce p es1 at_pro` by
    (qpat_assum `immutable_alloca_sep_mods callee body_ce p es1 at_pro`
       (mp_then Any irule prelock_active_separation) >>
     qpat_assum `ce1.ce_modules = body_ce.ce_modules` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `ce1.ce_module = body_ce.ce_module` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `ce.ce_modules = ce1.ce_modules` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `ce.ce_module = ce1.ce_module` (pure_once_rewrite_tac o single o SYM) >>
     qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
  `immutable_base_zero body_ce at_pro` by
    (rewrite_tac[immutable_base_zero_def] >> conj_tac
     >- (qpat_assum `body_ce.ce_imm_alloca = imm` (pure_once_rewrite_tac o single) >>
         qpat_assum `imm = NONE \/ _` strip_assume_tac
         >- (qpat_assum `imm = NONE` (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
         qpat_assum `imm = SOME (Var _)` (pure_once_rewrite_tac o single) >>
         simp[NoAsms, eval_operand_def] >>
         qpat_assum `!q. imm = SOME (Var q) ==> _` (drule_then strip_assume_tac) >>
         qpat_assum `!q. not_fresh_at reserved q ==> lookup_var q at_pro = _`
           (drule_then (pure_once_rewrite_tac o single)) >> first_assum ACCEPT_TAC) >>
     qpat_assum `at_pro.vs_labels = t.vs_labels` (pure_once_rewrite_tac o single) >>
     qpat_assum `ce1.ce_is_ctor = body_ce.ce_is_ctor` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `ce.ce_is_ctor = ce1.ce_is_ctor` (pure_once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`at_pro`,`Gpro`,`tnpro`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (rpt gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `reserved` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_assum `!q sz. ce1.ce_return_buf = SOME (PtrVar (Var q) sz) ==> _` irule >>
      qexists_tac `sz` >>
      qpat_assum `ce1.ce_return_buf = body_ce.ce_return_buf` (pure_once_rewrite_tac o single) >>
      first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `reserved` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_assum `!q sz. ce1.ce_return_pc = SOME (PtrVar (Var q) sz) ==> _` irule >>
      qexists_tac `sz` >>
      qpat_assum `ce1.ce_return_pc = body_ce.ce_return_pc` (pure_once_rewrite_tac o single) >>
      first_assum ACCEPT_TAC)
  >- (disch_tac >> irule prelock_fmp_floor >> conj_tac
      >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`callee`,`ctx`] >> conj_tac >> first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon p st0 H es1.storage_trace ==> state_rel H _ _ _ _ _`
        (drule_then assume_tac) >>
      qpat_assum `!H. valid_horizon p st0 H es1.storage_trace ==> storage_well_formed_on _ _ _`
        (drule_then assume_tac) >>
      qpat_assum `!H. valid_horizon p st0 H es1.storage_trace ==> ghost_inv_at_mods (DF H) _ _ cm _ _ Gpro _ _`
        (drule_then assume_tac) >>
      rewrite_tac[stmt_state_rel_def, immutable_frame_mods_def] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- (qpat_assum `p = cx with stk updated_by CONS key` (pure_once_rewrite_tac o single) >>
          simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      qpat_assum `body_ce = cm with ce_alloca_locals := T` (pure_once_rewrite_tac o single) >>
      irule prelock_body_ghost >> first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `tnpro.t_stor = Nm.t_stor` (pure_once_rewrite_tac o single)) >>
  TRY (qpat_assum `Nm.t_stor = N.t_stor` (pure_once_rewrite_tac o single)) >>
  TRY (qpat_assum `tnpro.t_trans = Nm.t_trans` (pure_once_rewrite_tac o single)) >>
  TRY (qpat_assum `Nm.t_trans = N.t_trans` (pure_once_rewrite_tac o single)) >>
  TRY (qpat_assum `tnpro.t_imm = Nm.t_imm` (pure_once_rewrite_tac o single)) >>
  TRY (qpat_assum `Nm.t_imm = N.t_imm` (pure_once_rewrite_tac o single)) >>
  first_assum ACCEPT_TAC
QED

Finalise selected_materialize_prelock_run_mods
