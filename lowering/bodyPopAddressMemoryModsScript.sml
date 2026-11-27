(* The final three instructions of Pop on a reached memory allocation. *)
Theory bodyPopAddressMemoryMods
Ancestors
  exprSimPopNestedLocalRun exprPtrUnwrapScalarEdges emitHelperProps exprLoweringProps
  typedCopyOriginPtrBase immutableRegionLoadPtr ghostPcTransportPtr
  instSeqComposePtr logInstSeqPtr instIdxIndep fragGasSeqPtr fragExecMem
  allocasBelowFmpUpdatesProps bodyPtrDefs unitTransformDefs bodyBinopFragMemory
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  codegenRel contextCodegenRel memSafeRun blockPrefixEquiv
  finite_map list rich_list words arithmetic

Theorem pop_address_binop[local]:
  (opc = ADD /\ z = a+b \/ opc = MUL /\ z = a*b) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let i = mk_inst id opc [left;right] [out];
      u = update_var out z s;
      H = step_prov PG G i u;
      tm = step_taint i s u tn
  in
    step_inst_base i s = OK u /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn [i]
        (s with vs_inst_idx := j) H tm) /\
    op_prov H (Var out) = (if opc = ADD then first_prov G [left;right] else NONE) /\
    op_taint tm (Var out) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP H p = FLOOKUP G p /\
                       op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> simp_tac bool_ss [LET_THM] >>
  `!j. step_inst_base (mk_inst id opc [left;right] [out]) (s with vs_inst_idx := j) =
      OK (update_var out z s with vs_inst_idx := j)` by
    (gen_tac >> qpat_x_assum `opc = ADD /\ _ \/ _` strip_assume_tac >>
     gvs[] >> pure_once_rewrite_tac[GSYM update_var_idx] >>
     FIRST [irule step_ADD, irule step_MUL] >> simp[]) >>
  conj_tac
  >- (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
      simp[venom_state_fupdselfid, update_var_def]) >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_assum `!j. step_inst_base _ _ = _` (qspec_then `j` assume_tac) >>
      drule_at (Pos last) inst_seq_ptr_singleton >>
      simp[] >> disch_then irule >> irule ptr_inst_ok_copy_arith >>
      fs[allocas_from_def, allocas_below_fmp_updates] >> metis_tac[]) >>
  qpat_x_assum `opc = ADD /\ _ \/ _` strip_assume_tac >> gvs[] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame, add_selected_provenance] >>
  simp[op_prov_def, typed_copy_origin_ptr_binop_ghost_frame]
QED

Theorem pop_address_prepend[local]:
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK u /\
  (!j. inst_seq_ptr D lo ctx func PG G tn [i] (s with vs_inst_idx := j) H tm) /\
  (!j. inst_seq_ptr D lo ctx func PG H tm code (u with vs_inst_idx := j) J tr) ==>
  !j. inst_seq_ptr D lo ctx func PG G tn (i::code) (s with vs_inst_idx := j) J tr
Proof
  strip_tac >>
  irule (SIMP_RULE (srw_ss()) [run_inst_seq_def]
    (Q.INST [`xs` |-> `[i]`] inst_seq_ptr_uniform_append)) >>
  conj_tac >- simp[] >> map_every qexists [`H`,`u`,`tm`] >> simp[]
QED

Theorem pop_address_sequence[local]:
  ALL_DISTINCT [p;x3;x4;x5;x6] /\
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME root /\
  lookup_var x3 s = SOME n /\
  op_taint tn (Var p) = {} /\ op_taint tn (Var x3) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let a = mk_inst (id+6) ADD [Var p;Lit 32w] [x4];
      b = mk_inst (id+7) MUL [Var x3;Lit (n2w esz)] [x5];
      c = mk_inst (id+8) ADD [Var x4;Var x5] [x6]
  in
  ?u H tm.
    run_inst_seq [a;b;c] s = OK u /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn [a;b;c]
      (s with vs_inst_idx := j) H tm) /\
    lookup_var x6 u = SOME (w + 32w + n * n2w esz) /\
    FLOOKUP H x6 = SOME root /\ op_taint tm (Var x6) = {} /\
    (u with vs_vars := s.vs_vars) = s /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!q. ~MEM q [x4;x5;x6] ==> lookup_var q u = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint tm (Var q) = op_taint tn (Var q))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `a = mk_inst (id+6) ADD [Var p;Lit 32w] [x4]` >>
  qabbrev_tac `b = mk_inst (id+7) MUL [Var x3;Lit (n2w esz)] [x5]` >>
  qabbrev_tac `c = mk_inst (id+8) ADD [Var x4;Var x5] [x6]` >>
  qabbrev_tac `s4 = update_var x4 (w+32w) s` >>
  qabbrev_tac `s5 = update_var x5 (n*n2w esz) s4` >>
  qabbrev_tac `u = update_var x6 (w+32w+n*n2w esz) s5` >>
  qabbrev_tac `G4 = step_prov PG G a s4` >>
  qabbrev_tac `T4 = step_taint a s s4 tn` >>
  qabbrev_tac `G5 = step_prov PG G4 b s5` >>
  qabbrev_tac `T5 = step_taint b s4 s5 T4` >>
  qabbrev_tac `H = step_prov PG G5 c u` >>
  qabbrev_tac `tm = step_taint c s5 u T5` >>
  `step_inst_base a s = OK s4 /\
   (!D j. inst_seq_ptr D lo ctx func PG G tn [a] (s with vs_inst_idx := j) G4 T4) /\
   op_prov G4 (Var x4) = first_prov G [Var p;Lit 32w] /\
   op_taint T4 (Var x4) = {} /\
   T4.t_mem = tn.t_mem /\ T4.t_stor = tn.t_stor /\
   T4.t_trans = tn.t_trans /\ T4.t_imm = tn.t_imm /\
   (!q. q <> x4 ==> FLOOKUP G4 q = FLOOKUP G q /\
      op_taint T4 (Var q) = op_taint tn (Var q))` by
    (simp_tac bool_ss [Abbr `G4`, Abbr `T4`, Abbr `a`, Abbr `s4`] >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] (Q.INST [`opc` |-> `ADD`] pop_address_binop)) >>
     simp[eval_operand_def, op_taint_def]) >>
  `allocas_from lo s4 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s4) /\
   lookup_var x3 s4 = SOME n /\ op_taint T4 (Var x3) = {}` by
    (fs[Abbr `s4`, allocas_from_def, allocas_below_fmp_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `step_inst_base b s4 = OK s5 /\
   (!D j. inst_seq_ptr D lo ctx func PG G4 T4 [b] (s4 with vs_inst_idx := j) G5 T5) /\
   op_prov G5 (Var x5) = NONE /\ op_taint T5 (Var x5) = {} /\
   T5.t_mem = T4.t_mem /\ T5.t_stor = T4.t_stor /\
   T5.t_trans = T4.t_trans /\ T5.t_imm = T4.t_imm /\
   (!q. q <> x5 ==> FLOOKUP G5 q = FLOOKUP G4 q /\
      op_taint T5 (Var q) = op_taint T4 (Var q))` by
    (simp_tac bool_ss [Abbr `G5`, Abbr `T5`, Abbr `b`, Abbr `s5`] >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] (Q.INST [`opc` |-> `MUL`] pop_address_binop)) >>
     simp[eval_operand_def, op_taint_def]) >>
  `allocas_from lo s5 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s5) /\
   lookup_var x4 s5 = SOME (w+32w) /\ lookup_var x5 s5 = SOME (n*n2w esz) /\
   op_taint T5 (Var x4) = {}` by
    (fs[Abbr `s5`, Abbr `s4`, allocas_from_def, allocas_below_fmp_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `step_inst_base c s5 = OK u /\
   (!D j. inst_seq_ptr D lo ctx func PG G5 T5 [c] (s5 with vs_inst_idx := j) H tm) /\
   op_prov H (Var x6) = first_prov G5 [Var x4;Var x5] /\
   op_taint tm (Var x6) = {} /\
   tm.t_mem = T5.t_mem /\ tm.t_stor = T5.t_stor /\
   tm.t_trans = T5.t_trans /\ tm.t_imm = T5.t_imm /\
   (!q. q <> x6 ==> FLOOKUP H q = FLOOKUP G5 q /\
      op_taint tm (Var q) = op_taint T5 (Var q))` by
    (simp_tac bool_ss [Abbr `H`, Abbr `tm`, Abbr `c`, Abbr `u`] >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] (Q.INST [`opc` |-> `ADD`] pop_address_binop)) >>
     simp[eval_operand_def, op_taint_def]) >>
  map_every qexists [`u`,`H`,`tm`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >-
    (gen_tac >> irule pop_address_prepend >>
     conj_tac >- simp[Abbr `a`, mk_inst_def, is_terminator_def] >>
     map_every qexists [`G4`,`T4`,`s4`] >> simp[] >>
     irule pop_address_prepend >>
     conj_tac >- simp[Abbr `b`, mk_inst_def, is_terminator_def] >>
     map_every qexists [`G5`,`T5`,`s5`] >> simp[]) >>
  `FLOOKUP G4 x4 = SOME root /\ FLOOKUP G5 x4 = SOME root` by
    (fs[first_prov_def, op_prov_def] >> metis_tac[]) >>
  `FLOOKUP H x6 = SOME root` by fs[first_prov_def, op_prov_def] >>
  simp[Abbr `u`, Abbr `s5`, Abbr `s4`, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, venom_state_fupdselfid] >>
  metis_tac[]
QED

Theorem pop_address_tail_run[local]:
  code = [mk_inst (id+6) ADD [Var p;Lit 32w] [x4];
          mk_inst (id+7) MUL [Var x3;Lit (n2w esz)] [x5];
          mk_inst (id+8) ADD [Var x4;Var x5] [x6]] /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D lo ctx func PG G tn code s H tm /\ run_inst_seq code s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code),H,tm)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `!i t. MEM i code ==> dalloca_no_wrap i t` by
    (simp[] >> rpt gen_tac >>
     strip_tac >> gvs[mk_inst_def, dalloca_no_wrap_def]) >>
  `(ctx_has_dalloca ctx ==> !pre i post t.
     code = pre ++ i::post /\ run_inst_seq pre s = OK t ==> dalloca_no_wrap i t)` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[mk_inst_def]
QED

Theorem pop_address_memory_mods:
  let code = DROP 6 (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6);
      addr = w2n w + 32 + (len-1)*esz
  in
  s.vs_inst_idx = k+6 /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  alloca_history func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ALL_DISTINCT [p;x3;x4;x5;x6] /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
  FLOOKUP G p = SOME (root_base,span) /\
  lookup_var x3 s = SOME (n2w (len-1)) /\ op_taint tn (Var x3) = {} /\
  addr < dimword (:256) /\ addr + esz <= root_base + span ==>
  ?u z H tm.
    run_inst_seq code s = OK u /\ z = (u with vs_inst_idx := k+9) /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn code (s with vs_inst_idx := j) H tm) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,H,tm)) /\
    lookup_var x6 z = SOME (n2w addr) /\ w2n (n2w addr : bytes32) = addr /\
    FLOOKUP H x6 = SOME (root_base,span) /\ op_taint tm (Var x6) = {} /\
    ptr_covers H tm x6 z esz /\
    (z with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~z.vs_halted /\ z.vs_current_bb = s.vs_current_bb /\
    z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
    z.vs_fmp = s.vs_fmp /\ alloca_history func z /\ allocas_from lo z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!q. ~MEM q [x4;x5;x6] ==> lookup_var q z = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint tm (Var q) = op_taint tn (Var q))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  qmatch_asmsub_abbrev_tac `addr < dimword (:256)` >>
  `code = [mk_inst (id+6) ADD [Var p;Lit 32w] [x4];
           mk_inst (id+7) MUL [Var x3;Lit (n2w esz)] [x5];
           mk_inst (id+8) ADD [Var x4;Var x5] [x6]]` by
    simp[Abbr `code`, memory_pop_insts_def] >>
  `op_taint tn (Var p) = {} /\ root_base <= w2n w` by
    (qpat_x_assum `ptr_covers G tn p s 32`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >> gvs[]) >>
  dxrule (SIMP_RULE bool_ss [LET_THM] pop_address_sequence) >>
  disch_then (drule_all_then (qspecl_then [`id`,`func`,`esz`,`PG`] strip_assume_tac)) >>
  rename1 `run_inst_seq _ s = OK u` >>
  rename1 `FLOOKUP H x6 = SOME (root_base,span)` >>
  rename1 `op_taint tm (Var x6) = {}` >>
  `LENGTH code = 3` by simp[] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s H tm` by
    (gen_tac >> qpat_assum `!D j. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >>
     simp_tac bool_ss [venom_state_fupdselfid] >> simp[]) >>
  qabbrev_tac `z = u with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,H,tm)` by
    (gen_tac >> simp_tac bool_ss [Abbr `z`] >> irule pop_address_tail_run >>
     metis_tac[]) >>
  `alloca_history func z` by
    (simp_tac bool_ss [Abbr `z`] >> irule alloca_history_no_alloca_slice >>
     `u.vs_allocas = s.vs_allocas /\ u.vs_current_bb = s.vs_current_bb` by
       (qpat_assum `(u with vs_vars := s.vs_vars) = s` (mp_tac o GSYM) >>
        disch_then (fn th => conj_tac >> simp_tac (srw_ss()) [Once th])) >>
     qpat_assum `isPREFIX code _` (mp_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[mk_inst_def]) >>
  `lookup_var x6 z = SOME (n2w addr)` by
    (simp[Abbr `z`, lookup_var_set_inst_idx, Abbr `addr`] >>
     qpat_assum `lookup_var x6 u = SOME _` (mp_tac o GSYM) >>
     simp[GSYM word_add_n2w, GSYM word_mul_n2w,
          AC WORD_ADD_ASSOC WORD_ADD_COMM, WORD_MULT_COMM]) >>
  `w2n (n2w addr : bytes32) = addr` by simp[LESS_MOD] >>
  `ptr_covers H tm x6 z esz` by
    (simp[ptr_covers_def] >> fs[Abbr `addr`] >> decide_tac) >>
  `z = (u with vs_inst_idx := k+9)` by simp[Abbr `z`] >>
  `~z.vs_halted /\ z.vs_current_bb = s.vs_current_bb /\
   z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
   z.vs_fmp = s.vs_fmp /\ allocas_from lo z /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (qpat_assum `(u with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[Abbr `z`, venom_state_component_equality,
          allocas_from_def, allocas_below_fmp_def] >>
     qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (mp_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
     metis_tac[]) >>
  map_every qexists [`u`,`H`,`tm`] >>
  qpat_x_assum `z = (u with vs_inst_idx := k+9)` (pure_once_rewrite_tac o single o SYM) >>
  simp[] >> simp[Abbr `z`, lookup_var_set_inst_idx] >>
  qpat_assum `(u with vs_vars := s.vs_vars) = s` mp_tac >>
  simp[venom_state_component_equality]
QED
