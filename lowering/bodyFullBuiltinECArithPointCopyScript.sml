Theory bodyFullBuiltinECArithPointCopy
Ancestors bodyFullBuiltinECArithTransfers bodyMemEcArithTransfers
  compileEnv emitHelper exprLoweringProps ptrCoverage valueEncodingProps
  fragGasOriginPtr venomState venomInst finite_map words
  ptrDiscipline loweringStateRelDefs allocationPtr bodyPtrDefs

Theorem ec_point_copy_origin_ptr_path:
  (do src <- emit_op ADD [Var pp; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bp; Lit (n2w pd)];
      emit_void MSTORE [dst; value];
      src <- emit_op ADD [Var pp; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bp; Lit (n2w (pd+32))];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  lookup_var pp s = SOME pw /\ lookup_var bp s = SOME bw /\
  ptr_covers G tn pp s 64 /\ ptr_covers G tn bp s nd /\
  not_fresh_at sa pp /\ not_fresh_at sa bp /\ pd+64 <= nd /\
  w2n pw+64 < dimword (:256) /\ w2n bw+nd < dimword (:256) /\
  w2n pw+64 <= s.vs_alloca_next /\ w2n bw+nd <= s.vs_alloca_next /\
  (!i. w2n pw <= i /\ i < w2n pw+64 ==> i NOTIN tn.t_mem) /\
  (w2n pw+64 <= w2n bw+pd \/ w2n bw+pd+64 <= w2n pw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_memory = (mstore (w2n bw+pd+32)
      (mem_word_at (w2n pw+32) s.vs_memory)
      (mstore (w2n bw+pd) (mem_word_at (w2n pw) s.vs_memory) s)).vs_memory /\
    mem_word_at (w2n bw+pd) t.vs_memory = mem_word_at (w2n pw) s.vs_memory /\
    mem_word_at (w2n bw+pd+32) t.vs_memory = mem_word_at (w2n pw+32) s.vs_memory /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n bw+pd <= i /\ i < w2n bw+pd+64} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|> = s
Proof
  strip_tac >>
  qabbrev_tac `first = (do
    src <- emit_op ADD [Var pp; Lit 0w]; value <- emit_op MLOAD [src];
    dst <- emit_op ADD [Var bp; Lit (n2w pd)]; emit_void MSTORE [dst;value] od)` >>
  qabbrev_tac `second = (do
    src <- emit_op ADD [Var pp; Lit 32w]; value <- emit_op MLOAD [src];
    dst <- emit_op ADD [Var bp; Lit (n2w (pd+32))]; emit_void MSTORE [dst;value] od)` >>
  `comp_ignore_bind first second sa = ((),sb)` by
    fs[Abbr `first`, Abbr `second`, comp_ignore_bind_def, comp_bind_assoc] >>
  Cases_on `first sa` >> Cases_on `q` >> rename1 `first sa = ((),sm)` >>
  `second sm = ((),sb)` by fs[comp_ignore_bind_def, comp_bind_def] >>
  qunabbrev_tac `first` >> qunabbrev_tac `second` >>
  drule ec_point_word_transfer_shape >> strip_tac >>
  rev_drule ec_point_word_transfer_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule arithmeticPropsTheory.emitted_insts_prefix_split >> simp[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  `pd+32 <= nd /\
   (!i. w2n pw <= i /\ i < w2n pw+32 ==> i NOTIN tn.t_mem)` by
    (conj_tac >- decide_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all (SRULE [] (Q.INST [`ps` |-> `0`, `ns` |-> `64`]
    (SPEC_ALL ec_point_word_transfer_origin_ptr_path))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)` >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `lookup_var pp u = SOME pw /\ lookup_var bp u = SOME bw /\
   ptr_covers Gu tu pp u 64 /\ ptr_covers Gu tu bp u nd` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sm pp /\ not_fresh_at sm bp` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `allocas_from lo u` by (fs[allocas_from_def] >> metis_tac[]) >>
  `!i. w2n pw+32 <= i /\ i < w2n pw+64 ==> i NOTIN tu.t_mem` by
    (simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  qpat_x_assum `emitted_insts sa sm = [_;_;_;_]` kall_tac >>
  qpat_x_assum `emitted_insts sm sb = [_;_;_;_]` kall_tac >>
  `isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (simp[GSYM rich_listTheory.DROP_DROP_T] >>
     qpat_x_assum `isPREFIX (emitted_insts sa sb) _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND, listTheory.APPEND_ASSOC] >> strip_tac >>
     qpat_x_assum `DROP s.vs_inst_idx _ = _` SUBST1_TAC >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, DROP_PREFIX] >> REFL_TAC) >>
  `w2n pw+64 <= u.vs_alloca_next /\ w2n bw+nd <= u.vs_alloca_next /\
   lo <= u.vs_alloca_next /\ ~u.vs_halted /\
   lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `pd+32+32 <= nd /\
   (!i. w2n pw+32 <= i /\ i < w2n pw+32+32 ==> i NOTIN tu.t_mem)` by
    (conj_tac >- decide_tac >> simp[arithmeticTheory.ADD_ASSOC]) >>
  drule_all (SRULE [] (Q.INST [`ps` |-> `32`, `ns` |-> `64`]
    (SPEC_ALL ec_point_word_transfer_origin_ptr_path))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `mem_word_at (w2n pw+32) u.vs_memory =
   mem_word_at (w2n pw+32) s.vs_memory` by
    (simp[] >> irule mstore_mem_word_at_disjoint >> decide_tac) >>
  (qexistsl_tac [`t`,`G'`,`tn'`] >>
  conj_tac >-
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     simp[] >> disch_then irule >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `t.vs_memory = _` SUBST1_TAC >>
     qpat_x_assum `mem_word_at (w2n pw+32) u.vs_memory = _` SUBST1_TAC >>
     pure_rewrite_tac[mstore_def, write_memory_with_expansion_def,
       venom_state_accessors, arithmeticTheory.ADD_ASSOC] >>
     qpat_x_assum `u.vs_memory = _` (fn th =>
       rewrite_tac[REWRITE_RULE [mstore_def, write_memory_with_expansion_def,
         venom_state_accessors] th]) >>
     pure_rewrite_tac[LET_THM] >> BETA_TAC >>
     rewrite_tac[venom_state_accfupds, combinTheory.K_THM]) >>
  conj_tac >-
    (qpat_assum `t.vs_memory = _` SUBST1_TAC >>
     dep_rewrite.DEP_REWRITE_TAC[mstore_mem_word_at_disjoint] >>
     conj_tac >- decide_tac >>
     qpat_assum `u.vs_memory = _` SUBST1_TAC >>
     simp[NoAsms, mstore_mem_word_at_same]) >>
  conj_tac >-
    (qpat_assum `t.vs_memory = _` SUBST1_TAC >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC, mstore_mem_word_at_same] >>
     qpat_assum `mem_word_at (w2n pw+32) u.vs_memory = _` ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `tn'.t_mem = _` SUBST1_TAC >>
     qpat_assum `tu.t_mem = _` SUBST1_TAC >>
     simp[NoAsms, pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF] >>
     gen_tac >> Cases_on `x IN tn.t_mem` >> pop_assum (fn th => rewrite_tac[th]) >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (rpt strip_tac >> `not_fresh_at sm x` by (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     simp[NoAsms, listTheory.LENGTH_APPEND] >> decide_tac) >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[NoAsms, venom_state_component_equality])
QED
