Theory bodyFullBuiltinECArithTransfers
Ancestors
  bodyMemEcArithTransfers exprSimPtrLiteralOps wordLoadStorePtr
  fragGasSeqPtr bodyFullAllocGeneric exprPtrUnwrapScalarEdges loweringStateRelDefs
  bodyPtrEnvBuiltinsEdges ptrCoverage allocationPtr
  venomExecSemantics venomInst venomState finite_map words bodyPtrDefs
  ptrSafetyTransport ptrDiscipline fragExecPtr ghostPcTransportPtr instIdxIndep
  emitHelper compileEnv exprLoweringProps

Theorem ec_scalar_store_origin_ptr_path:
  (do dst <- emit_op ADD [Var bp; Lit (n2w pd)];
      emit_void MSTORE [dst; scalar] od) sa = ((),sb) /\
  lookup_var bp s = SOME bw /\ eval_operand scalar s = SOME sw /\
  ptr_covers G tn bp s nd /\ op_taint tn scalar = {} /\
  not_fresh_at sa bp /\
  (!x. scalar = Var x ==> not_fresh_at sa x) /\
  pd + 32 <= nd /\ w2n bw + nd < dimword (:256) /\
  w2n bw + nd <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_memory = (mstore (w2n bw + pd) sw s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n bw + pd <= i /\ i < w2n bw + pd + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|> = s
Proof
  strip_tac >>
  `eval_operand (Var bp) s = SOME bw` by simp[eval_operand_def] >>
  `!x. MEM (Var x) [Var bp;scalar] ==> not_fresh_at sa x` by
    (simp[] >> metis_tac[]) >>
  drule_all ec_scalar_store_run >> strip_tac >>
  drule ec_scalar_store_shape >> strip_tac >>
  `w2n (bw + n2w pd) = w2n bw + pd` by
    (`pd < dimword (:256) /\ w2n bw + pd < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `w2n (bw + n2w pd) + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all ec_scalar_store_mem_ok >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> q` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `q`]) >>
  qpat_assum `ptr_covers G tn bp s nd` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  `FLOOKUP G bp = SOME (b,sz')` by metis_tac[] >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ADD [Var bp; Lit (n2w pd)] [q]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+1) MSTORE [Var q;scalar] []` >>
  qabbrev_tac `u = update_var q (bw + n2w pd) s` >>
  qabbrev_tac `Gu = G |+ (q,(b,sz'))` >>
  qabbrev_tac `tu = tn with t_var := tn.t_var |+ (q,{})` >>
  `step_inst_base i1 s = OK u` by
    simp[Abbr `i1`, Abbr `u`, step_inst_base_opcode_eqs, exec_pure2_def,
         bind_outputs_def, eval_operand_def] >>
  `step_prov PG G i1 u = Gu /\ step_taint i1 s u tn = tu` by
    (simp[Abbr `i1`, Abbr `u`, Abbr `Gu`, Abbr `tu`] >>
     irule literal_add_ghost >> simp[]) >>
  `ptr_covers Gu tu q u 32` by
    (qpat_x_assum `step_prov _ _ _ _ = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `step_taint _ _ _ _ = _` (SUBST1_TAC o SYM) >>
     `bw + n2w pd = n2w (w2n bw + pd)` by metis_tac[wordsTheory.n2w_w2n] >>
     qunabbrev_tac `i1` >> qunabbrev_tac `u` >>
     pure_asm_rewrite_tac[] >> irule literal_add_ptr_covers >> gvs[]) >>
  `lookup_var q u = SOME (bw + n2w pd) /\
   eval_operand scalar u = SOME sw /\ op_taint tu scalar = {}` by
    (Cases_on `scalar` >>
     gvs[Abbr `u`, Abbr `tu`, eval_operand_def, update_var_def,
         lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     `q <> s'` by metis_tac[] >> simp[]) >>
  qabbrev_tac `v = mstore (w2n bw + pd) sw u` >>
  qabbrev_tac `tv = step_taint i2 u v tu` >>
  `step_inst_base i2 u = OK v` by
    simp[Abbr `i2`, Abbr `v`, step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def] >>
  `step_prov PG Gu i2 v = Gu /\ tv.t_var = tu.t_var /\
   tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\
   tv.t_mem = tu.t_mem DIFF {i | w2n bw + pd <= i /\ i < w2n bw + pd + 32}` by
    (simp[Abbr `tv`, Abbr `v`, Abbr `i2`] >>
     drule_all mstore_ghost_frame >> simp[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i1 s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[] >> qexists_tac `0` >>
     simp[Abbr `i1`, literal_add_ptr_inst_ok]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Gu tu i2
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[Abbr `u`, allocas_from_def, update_var_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[Abbr `i2`] >> irule ptr_inst_ok_mstore >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  `step_inst_base i2 (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `i2`, Abbr `v`, step_inst_base_opcode_eqs,
         exec_write2_def, eval_operand_def, lookup_var_def, mstore_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i1;i2] s Gu tv` by
    (gen_tac >> simp[inst_seq_ptr_def, Abbr `tv`]) >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx + 2`, `Gu`, `tv`] >>
  conj_tac
  >- (gen_tac >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by simp[Abbr `i1`, Abbr `i2`, mk_inst_def, is_terminator_def] >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gu tv` by simp[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >>
      simp[Abbr `i1`, Abbr `i2`, mk_inst_def]) >>
  simp[Abbr `tu`] >>
  conj_tac >- simp[Abbr `tv`, Abbr `i2`, step_taint_def, imm_taint_def, mk_inst_def] >>
  conj_tac >- (rpt strip_tac >> `x <> q` by metis_tac[] >>
      gvs[Abbr `Gu`, op_taint_def, FLOOKUP_UPDATE, lookup_var_def]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_inst_idx`) >> simp[]) >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >> simp[]
QED

Theorem ec_point_word_load_origin_ptr_path:
  (do src <- emit_op ADD [Var pp; Lit (n2w ps)];
      emit_op MLOAD [src] od) sa = (value,sm) /\
  lookup_var pp s = SOME pw /\ ptr_covers G tn pp s ns /\
  not_fresh_at sa pp /\ ps + 32 <= ns /\
  w2n pw + ns < dimword (:256) /\ w2n pw + ns <= s.vs_alloca_next /\
  (!i. w2n pw + ps <= i /\ i < w2n pw + ps + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    eval_operand value u = SOME (mem_word_at (w2n pw + ps) s.vs_memory) /\
    op_taint tu value = {} /\
    (!x. value = Var x ==> not_fresh_at sm x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    u.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sm) /\
    u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s
Proof
  strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `r = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ADD [Var pp; Lit (n2w ps)] [q]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+1) MLOAD [Var q] [r]` >>
  `value = Var r /\ sm.cs_next_var = sa.cs_next_var+2 /\
   emitted_insts sa sm = [i1;i2]` by
    (qpat_x_assum `_ sa = (value,sm)` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
          fresh_id_def, emit_def] >> strip_tac >>
     gvs[Abbr `q`, Abbr `r`, Abbr `i1`, Abbr `i2`, emitted_insts_def,
         rich_listTheory.DROP_APPEND1]) >>
  `!x. not_fresh_at sa x ==> x <> q /\ x <> r` by
    (gen_tac >> simp[not_fresh_at_def, Abbr `q`, Abbr `r`] >>
     metis_tac[arithmeticTheory.LE_REFL, arithmeticTheory.LE_ADD]) >>
  `w2n (pw + n2w ps) = w2n pw + ps` by
    (`ps < dimword (:256) /\ w2n pw + ps < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  qpat_assum `ptr_covers G tn pp s ns` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  `w = pw` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `FLOOKUP G pp = SOME (b,sz')` by metis_tac[] >>
  qabbrev_tac `v = update_var q (pw + n2w ps) s` >>
  qabbrev_tac `Gv = G |+ (q,(b,sz'))` >>
  qabbrev_tac `tv = tn with t_var := tn.t_var |+ (q,{})` >>
  `step_inst_base i1 s = OK v` by
    simp[Abbr `i1`, Abbr `v`, step_inst_base_opcode_eqs, exec_pure2_def,
         bind_outputs_def, eval_operand_def] >>
  `step_prov PG G i1 v = Gv /\ step_taint i1 s v tn = tv` by
    (simp[Abbr `i1`, Abbr `v`, Abbr `Gv`, Abbr `tv`] >>
     irule literal_add_ghost >> simp[]) >>
  `ptr_covers Gv tv q v 32` by
    (qpat_x_assum `step_prov _ _ _ _ = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `step_taint _ _ _ _ = _` (SUBST1_TAC o SYM) >>
     `pw + n2w ps = n2w (w2n pw + ps)` by simp[GSYM wordsTheory.word_add_n2w] >>
     qunabbrev_tac `i1` >> qunabbrev_tac `v` >>
     pure_asm_rewrite_tac[] >> irule literal_add_ptr_covers >> gvs[]) >>
  qabbrev_tac `w = update_var r (mload (w2n pw+ps) v) v` >>
  qabbrev_tac `Gw = step_prov PG Gv i2 w` >>
  qabbrev_tac `tw = step_taint i2 v w tv` >>
  `step_inst_base i2 v = OK w` by
    simp[Abbr `i2`, Abbr `w`, Abbr `v`, step_inst_base_opcode_eqs,
         exec_read1_def, bind_outputs_def, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i1 s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[] >> qexists_tac `0` >> simp[Abbr `i1`, literal_add_ptr_inst_ok]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Gv tv i2
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[Abbr `v`, allocas_from_def, update_var_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[Abbr `i2`] >> irule ptr_inst_ok_mload >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  `step_inst_base i2 (v with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (w with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `i2`, Abbr `w`, Abbr `v`, step_inst_base_opcode_eqs,
         exec_read1_def, bind_outputs_def, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE, mload_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i1;i2] s Gw tw` by
    (gen_tac >> simp[inst_seq_ptr_def, Abbr `tw`, Abbr `Gw`]) >>
  `run_inst_seq [i1;i2] s = OK w` by simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok [i1;i2] s` by
    (simp[Once fragExecMemTheory.run_inst_seq_mem_ok_def,
          Abbr `i1`, instMemFrontierTheory.below_frontier_no_ranges,
          memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_last, Abbr `i2`, Abbr `v`,
          instMemFrontierTheory.below_frontier_MLOAD,
          memSafeRunTheory.inst_dload_in_section_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> decide_tac) >>
  qexistsl_tac [`w with vs_inst_idx := s.vs_inst_idx+2`, `Gw`, `tw`] >>
  conj_tac
  >- (gen_tac >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sm)` by simp[Abbr `i1`, Abbr `i2`, mk_inst_def, is_terminator_def] >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sm) s Gw tw /\
       run_inst_seq_mem_ok (emitted_insts sa sm) s /\
       run_inst_seq (emitted_insts sa sm) s = OK w /\
       isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[Abbr `i1`, Abbr `i2`, mk_inst_def]) >>
  `op_taint tw (Var r) = {} /\ tw.t_mem = tv.t_mem /\
   tw.t_stor = tv.t_stor /\ tw.t_trans = tv.t_trans` by
    (qunabbrev_tac `tw` >> qunabbrev_tac `w` >> qunabbrev_tac `i2` >>
     `w2n pw + ps = w2n (pw+n2w ps)` by simp[arithmeticTheory.ADD_COMM] >>
     pop_assum SUBST1_TAC >> irule mload_ghost_clean >>
     simp[Abbr `v`, Abbr `tv`, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  simp[Abbr `tv`] >>
  conj_tac >- simp[Abbr `w`, Abbr `v`, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, valueEncodingPropsTheory.mem_word_at_eq_mload, mload_def] >>
  conj_tac >- (simp[not_fresh_at_def, Abbr `r`] >> rpt strip_tac >>
      fs[ASCIInumbersTheory.toString_11]) >>
  `q <> r` by simp[Abbr `q`, Abbr `r`, ASCIInumbersTheory.toString_11] >>
  conj_tac >- (rpt strip_tac >> `x <> q /\ x <> r` by metis_tac[] >>
      simp[Abbr `w`, Abbr `v`, Abbr `Gw`, Abbr `Gv`, Abbr `tw`, Abbr `i2`,
           lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           step_prov_def, step_taint_def, mk_inst_def, op_taint_def,
           set_prov_def, out_prov_def, FLOOKUP_DRESTRICT, set_var_taint_def]) >>
  simp[Abbr `tw`, Abbr `i2`, step_taint_def, imm_taint_def, mk_inst_def,
       Abbr `w`, Abbr `v`, update_var_def]
QED

Theorem ec_point_word_transfer_origin_ptr_path:
  (do src <- emit_op ADD [Var pp; Lit (n2w ps)];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bp; Lit (n2w pd)];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  lookup_var pp s = SOME pw /\ lookup_var bp s = SOME bw /\
  ptr_covers G tn pp s ns /\ ptr_covers G tn bp s nd /\
  not_fresh_at sa pp /\ not_fresh_at sa bp /\ ps+32 <= ns /\ pd+32 <= nd /\
  w2n pw+ns < dimword (:256) /\ w2n bw+nd < dimword (:256) /\
  w2n pw+ns <= s.vs_alloca_next /\ w2n bw+nd <= s.vs_alloca_next /\
  (!i. w2n pw+ps <= i /\ i < w2n pw+ps+32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_memory = (mstore (w2n bw+pd)
      (mem_word_at (w2n pw+ps) s.vs_memory) s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n bw+pd <= i /\ i < w2n bw+pd+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|> = s
Proof
  strip_tac >>
  Cases_on `emit_op ADD [Var pp; Lit (n2w ps)] sa` >>
  rename1 `emit_op ADD [Var pp; Lit (n2w ps)] sa = (src,sc)` >>
  Cases_on `emit_op MLOAD [src] sc` >>
  rename1 `emit_op MLOAD [src] sc = (value,sm)` >>
  `(do src <- emit_op ADD [Var pp; Lit (n2w ps)]; emit_op MLOAD [src] od) sa = (value,sm)` by
    simp[comp_bind_def] >>
  `(do dst <- emit_op ADD [Var bp; Lit (n2w pd)]; emit_void MSTORE [dst;value] od) sm = ((),sb)` by
    (qpat_x_assum `_ sa = ((),sb)` mp_tac >> simp[comp_bind_def]) >>
  drule ec_scalar_store_shape >> strip_tac >>
  drule_all emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `emit_op ADD _ sa = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ sc = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule arithmeticPropsTheory.emitted_insts_prefix_split >> simp[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  drule_all ec_point_word_load_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_halted = s.vs_halted /\
   u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `lookup_var bp u = SOME bw /\ ptr_covers Gu tu bp u nd` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sm bp` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `allocas_from lo u` by (fs[allocas_from_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (simp[GSYM rich_listTheory.DROP_DROP_T] >>
     qpat_x_assum `isPREFIX (emitted_insts sa sb) _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND, listTheory.APPEND_ASSOC] >> strip_tac >>
     qpat_x_assum `DROP s.vs_inst_idx _ = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[rich_listTheory.DROP_APPEND2]) >>
  `w2n bw + nd <= u.vs_alloca_next /\ lo <= u.vs_alloca_next /\
   ~u.vs_halted /\ lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all ec_scalar_store_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`G'`,`tn'`] >>
  conj_tac >-
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) ([] ++ []) (OK t,G',tn')` by
       metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append] >> fs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  rpt conj_tac
  >- gvs[mstore_def, write_memory_with_expansion_def]
  >- simp[] >- simp[] >- simp[] >- simp[] >- metis_tac[]
  >- simp[listTheory.LENGTH_APPEND] >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED
