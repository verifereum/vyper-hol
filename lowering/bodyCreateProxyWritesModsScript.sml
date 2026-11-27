Theory bodyCreateProxyWritesMods
Ancestors
  bodyFullAbiEncodeSetupTail bodyFullBuiltinECArithTransfers
  bodyMemEcArithTransfers stmtReasonLitFragMemory bodyPtrMakeArrayEmission
  bodyPtrEnvBuiltinsEdges ptrDisciplineEmptyTaint fragGasOriginPtrLoop
  fragGasOriginPtr fragExec exprSimCalldataSlice valueEncodingProps
  builtinCreate vyperCreate memoryReadProps venomExecSemantics venomMemProps venomState
  venomInst emitHelper emitHelperProps compileEnv ptrDiscipline words list
  codegenRel loweringStateRelDefs fragGasSeqPtr unitTransformDefs
  contextCodegenRel memSafeRun finite_map exprLoweringProps bodyPtrDefs
Libs
  blastLib

Theorem proxy_writes_address_bytes[local]:
  TAKE 20 (word_to_bytes ((word:bytes32) << 96) T) =
  word_to_bytes (w2w word:address) T
Proof
  simp[byteTheory.word_to_bytes_def, byteTheory.word_to_bytes_aux_compute,
       fcpLib.INDEX_CONV ``dimindex(:256)``,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  BBLAST_TAC
QED

Overload proxy_head[local] =
  ``0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w:bytes32``
Overload proxy_tail[local] =
  ``0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w:bytes32``

Theorem proxy_writes_initcode[local]:
  read_memory b 54 (mstore (b+39) proxy_tail
    (mstore (b+19) (word << 96) (mstore b proxy_head s))) =
  minimal_proxy_initcode (w2w word)
Proof
  mp_tac (Q.SPECL [`b`,`19`,`35`] read_memory_split) >>
  mp_tac (Q.SPECL [`b+19`,`20`,`15`] read_memory_split) >>
  simp[arithmeticTheory.ADD_ASSOC] >> rpt strip_tac >>
  asm_rewrite_tac [] >> simp[read_memory_mstore_disjoint] >>
  `!a n v s. n <= 32 ==> read_memory a n (mstore a v s) =
    TAKE n (word_to_bytes v T)` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`a`,`32`,`0`,`n`,`mstore a v s`] read_memory_subwindow) >>
     simp[read_memory_word, mload_mstore_same]) >>
  simp[proxy_writes_address_bytes] >>
  `TAKE 19 (word_to_bytes proxy_head T) =
   minimal_proxy_loader ++ minimal_proxy_forwarder_pre` by EVAL_TAC >>
  `TAKE 15 (word_to_bytes proxy_tail T) = minimal_proxy_forwarder_post` by EVAL_TAC >>
  ASM_REWRITE_TAC [minimal_proxy_initcode_def, minimal_proxy_runtime_def, APPEND_ASSOC]
QED

Theorem proxy_writes_shift[local]:
  emit_op SHL [Lit 96w;target] sa = (aligned,sb) /\ fn_has_code sa sb func /\
  eval_operand target s = SOME w /\ op_taint tn target = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x t G' tn'. aligned = Var x /\ not_fresh_at sb x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t = (update_var x (w << 96) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    lookup_var x t = SOME (w << 96) /\ op_taint tn' aligned = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s /\
         FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  strip_tac >> drule_all emit_op_fetch_boundary >> strip_tac >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME (mk_inst _ _ _ [x])` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id SHL [Lit 96w;target] [x]` >>
  qabbrev_tac `u = update_var x (w << 96) s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, exec_pure2_def,
         bind_outputs_def, eval_operand_def] >>
  `step_taint i s u tn = tn with t_var := tn.t_var |+ (x,{})` by
    (`new_site_bytes s u = {}` by
       (irule new_site_bytes_unchanged >> simp[Abbr `u`, update_var_def]) >>
     simp[Abbr `i`, mk_inst_def, step_taint_def, mem_taint_def, step_writes_def,
          source_memory_write_ranges_def, written_taint_def, range_bytes_def,
          store_taint_def, adopt_reset_def, imm_taint_def, out_taint_def,
          eval_operand_def, set_var_taint_def, taint_component_equality, shift_taint_empty]) >>
  qexistsl_tac [`x`, `u with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG G i u`, `step_taint i s u tn`] >> simp[] >>
  conj_tac
  >- (simp[not_fresh_at_def] >>
      gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def]) >>
  conj_tac
  >- (gen_tac >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
          step_prov PG G i u, step_taint i s u tn)` by
        (`ptr_inst_ok D lo 0 ctx func G tn i s` by
           (simp[Abbr `i`] >> irule ptr_inst_ok_scalar_builtin_at >>
            simp[DISJ_IMP_THM, FORALL_AND_THM] >> simp[op_taint_def]) >>
         drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
         simp[Abbr `i`, mk_inst_def, is_terminator_def,
              inst_mem_below_frontier_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, inst_dload_in_section_def,
              IgnAsm `step_taint _ _ _ _ = _`] >>
         disch_then irule >> gvs[mk_inst_def]) >>
      drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> disch_then irule >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`, update_var_def]) >>
  simp[Abbr `u`, Abbr `i`, update_var_def, lookup_var_def, op_taint_def,
       FLOOKUP_UPDATE, step_prov_def, out_prov_def, set_prov_def,
       FLOOKUP_DRESTRICT, mk_inst_def] >>
  qx_gen_tac `y` >> strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> y` by metis_tac[] >> simp[]
QED

Theorem proxy_writes_offset[local]:
  (do dst <- emit_op ADD [Var p;Lit (n2w off)];
      emit_void MSTORE [dst;value] od) sa = ((),sb) /\
  fn_has_code sa sb func /\ lookup_var p s = SOME w /\
  eval_operand value s = SOME x /\ op_taint tn value = {} /\
  not_fresh_at sa p /\ (!y. value = Var y ==> not_fresh_at sa y) /\
  ptr_covers G tn p s 96 /\ off + 32 <= 96 /\
  w2n w + 96 < dimword (:256) /\ w2n w + 96 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96 /\
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|> = s /\
    t.vs_memory = (mstore (w2n w + off) x s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n w + off <= i /\ i < w2n w + off + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s /\
         FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  strip_tac >> drule ec_scalar_store_shape >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all ec_scalar_store_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
   t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
   t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _;vs_memory := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96` by
    (qpat_assum `!y. not_fresh_at sa y ==> _` drule >> strip_tac >> gvs[ptr_covers_def]) >>
  simp[allocas_from_def, allocas_below_fmp_def] >>
  fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[LENGTH_APPEND]
QED

Theorem create_proxy_writes_mods:
  emit_void MSTORE [Var p;Lit proxy_head] m1 = ((),m2) /\
  emit_op SHL [Lit 96w;target] m2 = (aligned,m3) /\
  (do dst <- emit_op ADD [Var p;Lit 19w];
      emit_void MSTORE [dst;aligned] od) m3 = ((),m4) /\
  (do dst <- emit_op ADD [Var p;Lit 39w];
      emit_void MSTORE [dst;Lit proxy_tail] od) m4 = ((),sb) /\
  fn_has_code m1 m2 func /\ fn_has_code m2 m3 func /\
  fn_has_code m3 m4 func /\ fn_has_code m4 sb func /\
  m1.cs_next_var <= m2.cs_next_var /\ m2.cs_next_var <= m3.cs_next_var /\
  m3.cs_next_var <= m4.cs_next_var /\ m4.cs_next_var <= sb.cs_next_var /\
  not_fresh_at m1 p /\ (!y. target = Var y ==> not_fresh_at m1 y) /\
  eval_operand target s = SOME x /\ op_taint tn target = {} /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 96 /\
  w2n w + 96 < dimword (:256) /\ w2n w + 96 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = m1.cs_current_bb /\ s.vs_inst_idx = LENGTH m1.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96 /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    t.vs_memory = (mstore (w2n w + 39) proxy_tail
      (mstore (w2n w + 19) (x << 96) (mstore (w2n w) proxy_head s))).vs_memory /\
    read_memory (w2n w) 54 t = minimal_proxy_initcode (w2w x) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a k. a+k <= w2n w \/ w2n w+71 <= a ==>
           mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 71} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at m1 y ==> lookup_var y t = lookup_var y s /\
         FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `b = w2n w` >>
  `n2w b = w /\ b < dimword (:256) /\ b + 32 <= s.vs_alloca_next` by
     (simp[Abbr `b`] >> fs[] >> decide_tac) >>
  `lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s 32` by
     (simp[] >> gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Lit proxy_head) s = SOME proxy_head /\ op_taint tn (Lit proxy_head) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all abi_encode_payload_word_origin >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `s1` (qx_choose_then `t1` strip_assume_tac))) >>
  suspend "shift"
QED

Resume create_proxy_writes_mods[shift]:
  `allocas_from lo s1 /\ lo <= s1.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
   eval_operand target s1 = SOME x /\ op_taint t1 target = {}` by
    (simp[mstore_def, allocas_from_def,allocas_below_fmp_def] >>
     Cases_on `target` >> gvs[eval_operand_def, lookup_var_def, op_taint_def,
       allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all proxy_writes_shift >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `al` (qx_choose_then `s2` (qx_choose_then `G2`
       (qx_choose_then `t2` strip_assume_tac))))) >>
  suspend "middle"
QED

Resume create_proxy_writes_mods[middle]:
  `lookup_var p s2 = SOME w /\ ptr_covers G2 t2 p s2 96` by
    (`not_fresh_at m2 p` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!y. not_fresh_at m2 y ==> _` drule >> strip_tac >>
     gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def]) >>
  `allocas_from lo s2 /\ lo <= s2.vs_alloca_next /\ ~s2.vs_halted /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s2) /\
   w2n w + 96 <= s2.vs_alloca_next` by
    (`s2.vs_allocas = s.vs_allocas /\ s2.vs_alloca_next = s.vs_alloca_next /\
      s2.vs_initial_fmp = s.vs_initial_fmp /\ s2.vs_fmp = s.vs_fmp /\
      s2.vs_halted = s.vs_halted` by
       (qpat_assum `s2 = _` (fn shift =>
          qpat_assum `s1 = _` (fn store => simp[NoAsms,shift,store,mstore_def,update_var_def]))) >>
     qpat_assum `Abbrev (b = w2n w)` (fn base =>
       asm_simp_tac bool_ss [SYM (REWRITE_RULE [markerTheory.Abbrev_def] base),
         allocas_from_def,allocas_below_fmp_def]) >>
     qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (assume_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s2.vs_inst_idx = LENGTH m3.cs_current_insts /\ not_fresh_at m3 p /\
   eval_operand aligned s2 = SOME (x << 96) /\
   (!y. aligned = Var y ==> not_fresh_at m3 y)` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `m1` >>
     simp[] >> decide_tac) >>
  `19 + 32 <= 96` by decide_tac >>
  `w2n w + 96 < dimword (:256)` by fs[Abbr `b`] >>
  drule_all (Q.INST [`off` |-> `19`] proxy_writes_offset) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `s3` (qx_choose_then `G3` (qx_choose_then `t3` strip_assume_tac)))) >>
  suspend "last"
QED

Resume create_proxy_writes_mods[last]:
  `not_fresh_at m4 p /\ lo <= s3.vs_alloca_next /\ w2n w + 96 <= s3.vs_alloca_next` by
    (simp[IgnAsm `s2 = _`] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand (Lit proxy_tail) s3 = SOME proxy_tail /\ op_taint t3 (Lit proxy_tail) = {} /\
   (!y. Lit proxy_tail = Var y ==> not_fresh_at m4 y) /\ 39 + 32 <= 96` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (Q.INST [`off` |-> `39`] proxy_writes_offset) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> suspend "pack"
QED

Resume create_proxy_writes_mods[pack]:
  conj_tac
  >- (gen_tac >> metis_tac[gas_origin_ptr_path_trans]) >>
  `s2.vs_memory = (mstore b proxy_head s).vs_memory` by
    simp[update_var_def,mstore_def] >>
  `s3.vs_memory = (mstore (b+19) (x << 96) (mstore b proxy_head s)).vs_memory` by
    (qpat_assum `s3.vs_memory = _` SUBST1_TAC >>
     qpat_assum `s2.vs_memory = _` (mp_tac o MATCH_MP mstore_equal_memory) >>
     disch_then (qspecl_then [`w2n w + 19`,`x << 96`] (pure_rewrite_tac o single)) >>
     simp[Abbr `b`]) >>
  `t.vs_memory = (mstore (b+39) proxy_tail
        (mstore (b+19) (x << 96) (mstore b proxy_head s))).vs_memory` by
    (qpat_assum `t.vs_memory = _` SUBST1_TAC >>
     qpat_assum `s3.vs_memory = (mstore (b+19) _ _).vs_memory`
       (mp_tac o MATCH_MP mstore_equal_memory) >>
     disch_then (qspecl_then [`w2n w + 39`,`proxy_tail`] (pure_rewrite_tac o single)) >>
     simp[Abbr `b`]) >>
  `t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|> = s` by
    (qpat_assum `t with <|vs_vars := _;vs_memory := _;vs_inst_idx := _|> = s3`
       (mp_tac o Q.AP_TERM `\z. z with <|vs_vars := s.vs_vars;
               vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>`) >>
     qpat_assum `s3 with <|vs_vars := _;vs_memory := _;vs_inst_idx := _|> = s2`
       (mp_tac o Q.AP_TERM `\z. z with <|vs_vars := s.vs_vars;
               vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>`) >>
     qpat_assum `s2 = _` (fn sh => qpat_assum `s1 = _`
       (fn wr => simp[NoAsms,sh,wr,update_var_def,mstore_def])) >>
     metis_tac[]) >>
  `tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b + 71}` by
    (simp[pred_setTheory.EXTENSION,pred_setTheory.IN_DIFF,Abbr `b`] >>
     qx_gen_tac `i` >> Cases_on `i IN tn.t_mem` >> simp[] >> decide_tac) >>
  suspend "finish"
QED

Resume create_proxy_writes_mods[finish]:
  `read_memory b 54 t = minimal_proxy_initcode (w2w x)` by
    (pure_rewrite_tac [read_memory_def] >>
     qpat_assum `t.vs_memory = (mstore _ _ (mstore _ _ (mstore _ _ s))).vs_memory` SUBST1_TAC >>
     MATCH_ACCEPT_TAC (REWRITE_RULE [read_memory_def] proxy_writes_initcode)) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `t.vs_memory = (mstore _ _ (mstore _ _ (mstore _ _ s))).vs_memory` SUBST1_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `LENGTH (mstore (b+19) (x << 96) (mstore b proxy_head s)).vs_memory` >>
     simp[mstore_memory_nondecreasing] >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `LENGTH (mstore b proxy_head s).vs_memory` >> simp[mstore_memory_nondecreasing]) >>
  `!a k. a+k <= b \/ b+71 <= a ==> mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     `a+k <= b \/ b+32 <= a` by decide_tac >>
     `a+k <= b+19 \/ b+19+32 <= a` by decide_tac >>
     `a+k <= b+39 \/ b+39+32 <= a` by decide_tac >>
     qpat_assum `t.vs_memory = (mstore (b+39) _ _).vs_memory` SUBST1_TAC >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  simp[IgnAsm `s2 = _`, IgnAsm `t.vs_memory = _`, IgnAsm `s3.vs_memory = _`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `y` >> strip_tac >>
  `not_fresh_at m2 y /\ not_fresh_at m3 y /\ not_fresh_at m4 y` by
    (rpt conj_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `m1` >> simp[] >> decide_tac) >>
  qpat_assum `!y. not_fresh_at m4 y ==> _` drule >> strip_tac >>
  qpat_assum `!y. not_fresh_at m3 y ==> _` drule >> strip_tac >>
  qpat_assum `!y. not_fresh_at m2 y ==> _` drule >> strip_tac >>
  simp[lookup_var_def,op_taint_def,mstore_def]
QED

Finalise create_proxy_writes_mods
