Theory stmtForRangeMemoryStart
Ancestors
  stmtForRangeMemoryParts stmtSimDeclPath loweringSlice localPtrsProps fragGasPathMem
  stmtSimProps bodyMemoryDefs allocaHistory emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst finite_map list rich_list words

Theorem for_range_alloca_start_mem:
  !ctx func cenv cx es s0 sa d aa aid sz p pre lbl entry_lbl j.
    aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
    32 <= sz /\ sz < dimword (:256) /\
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <|bb_label := lbl; bb_instructions := pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    return_buf_frame d cenv sa s0 /\ ret_pc_ok cenv sa s0 /\
    alloca_history func s0 /\ MEM aa (fn_insts func) /\ fn_inst_ids_distinct func /\
    not_local_ptr cenv es.scopes p /\
    (!x. not_fresh_at sa x ==> x <> p) ==>
    ?ee w. gas_path_mem ctx func s0 0 (OK ee) /\
      ee.vs_current_bb = entry_lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
      stmt_state_rel ctx func cenv cx es ee /\
      lookup_var p ee = SOME w /\ FLOOKUP ee.vs_allocas aid = SOME (w2n w,sz) /\
      return_buf_frame d cenv sa ee /\ ret_pc_ok cenv sa ee /\
      alloca_history func ee /\ s0.vs_alloca_next <= ee.vs_alloca_next /\
      (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP ee.vs_allocas id = SOME ent) /\
      (!x. x <> p ==> lookup_var x ee = lookup_var x s0) /\
      ee.vs_labels = s0.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `?s1. exec_alloca aa s0 (n2w sz:bytes32) = OK s1` by
    (Cases_on `FLOOKUP s0.vs_allocas aa.inst_id`
     >- simp[exec_alloca_def, mk_inst_def] >>
     rename1 `FLOOKUP s0.vs_allocas aa.inst_id = SOME ent` >>
     PairCases_on `ent` >> simp[exec_alloca_def, mk_inst_def]) >>
  `stmt_state_rel ctx func cenv cx es s1 /\
   ?w. lookup_var p s1 = SOME w /\
       FLOOKUP s1.vs_allocas aid = SOME (w2n w,sz)` by
    (drule stmt_state_rel_exec_alloca >>
     disch_then (qspecl_then [`aa`, `p`, `n2w sz`, `s1`] mp_tac) >>
     impl_tac >- simp[mk_inst_def] >> simp[mk_inst_def]) >>
  `s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     qpat_x_assum `aa = _` SUBST1_TAC >>
     qpat_x_assum `~s0.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exec_alloca_def, mk_inst_def, AllCaseEqs(), update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `step_inst_base aa s0 = OK s1` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     gvs[step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  `gas_path_mem ctx func s0 0 (OK (jump_to entry_lbl s1))` by
    (irule for_start_zero_path_mem >> simp[] >> qexists_tac `j` >> gvs[mk_inst_def]) >>
  suspend "frames"
QED

Resume for_range_alloca_start_mem[frames]:
  `!x. x <> p ==> lookup_var x s1 = lookup_var x s0` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) exec_alloca_frames >>
     disch_then (qspec_then `p` mp_tac) >> simp[mk_inst_def]) >>
  `!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP s1.vs_allocas id = SOME ent` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) exec_alloca_frames >>
     disch_then (qspec_then `p` mp_tac) >> simp[mk_inst_def]) >>
  `s0.vs_alloca_next <= s1.vs_alloca_next` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     qpat_x_assum `aa = _` SUBST1_TAC >> POP_ASSUM_LIST (K all_tac) >>
     simp[exec_alloca_def, mk_inst_def, AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `get_instruction
     <|bb_label := lbl; bb_instructions := pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|>
     s0.vs_inst_idx = SOME aa` by
    simp[get_instruction_def, EL_APPEND] >>
  drule_all alloca_history_base_step >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  `alloca_history func (jump_to entry_lbl s1)` by
    (irule alloca_history_jump >>
     conj_tac >- simp[jump_to_def] >>
     qexists_tac `s1 with vs_inst_idx := SUC s0.vs_inst_idx` >> simp[jump_to_def]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
     lookup_var x (jump_to entry_lbl s1) = SOME v` by
    (rpt strip_tac >> `x <> p` by metis_tac[] >>
     `lookup_var x s1 = lookup_var x s0` by simp[] >>
     gvs[lookup_var_def, jump_to_def]) >>
  `return_buf_frame d cenv sa (jump_to entry_lbl s1)` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[] >> simp[jump_to_def]) >>
  `ret_pc_ok cenv sa (jump_to entry_lbl s1)` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[] >> simp[jump_to_def]) >>
  `s1.vs_labels = s0.vs_labels` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exec_alloca_def, AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`jump_to entry_lbl s1`, `w`] >>
  simp[jump_to_def, stmt_state_rel_jump_to, lookup_var_def] >>
  fs[lookup_var_def]
QED
Finalise for_range_alloca_start_mem

Theorem for_range_lit_start_mem:
  !ctx func cenv cx es s0 sa d aa aid sz p cv ev a b pre lbl entry_lbl cond_lbl j i1 i2 i3.
    aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
    32 <= sz /\ sz < dimword (:256) /\
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <|bb_label := lbl; bb_instructions := pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|> /\
    lookup_block entry_lbl func.fn_blocks =
      SOME <|bb_label := entry_lbl; bb_instructions :=
        [mk_inst i1 ASSIGN [Lit a] [cv]; mk_inst i2 ADD [Lit a; Lit (b-a)] [ev];
         mk_inst i3 JMP [Label cond_lbl] []]|> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    return_buf_frame d cenv sa s0 /\ ret_pc_ok cenv sa s0 /\
    alloca_history func s0 /\ MEM aa (fn_insts func) /\ fn_inst_ids_distinct func /\
    ALL_DISTINCT [p;cv;ev] /\
    not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes cv /\
    not_local_ptr cenv es.scopes ev /\
    (!x. not_fresh_at sa x ==> x <> p /\ x <> cv /\ x <> ev) ==>
    ?cc w. gas_path_mem ctx func s0 0 (OK cc) /\
      cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
      stmt_state_rel ctx func cenv cx es cc /\
      lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
      lookup_var p cc = SOME w /\ FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
      return_buf_frame d cenv sa cc /\ ret_pc_ok cenv sa cc /\
      alloca_history func cc /\ s0.vs_alloca_next <= cc.vs_alloca_next /\
      (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
      (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0)
Proof
  rpt gen_tac >> strip_tac >>
  `?ee w. gas_path_mem ctx func s0 0 (OK ee) /\
      ee.vs_current_bb = entry_lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
      stmt_state_rel ctx func cenv cx es ee /\
      lookup_var p ee = SOME w /\ FLOOKUP ee.vs_allocas aid = SOME (w2n w,sz) /\
      return_buf_frame d cenv sa ee /\ ret_pc_ok cenv sa ee /\
      alloca_history func ee /\ s0.vs_alloca_next <= ee.vs_alloca_next /\
      (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP ee.vs_allocas id = SOME ent) /\
      (!x. x <> p ==> lookup_var x ee = lookup_var x s0) /\
      ee.vs_labels = s0.vs_labels` by
    (irule for_range_alloca_start_mem >>
     qpat_assum `aa = _` (fn th => rewrite_tac[GSYM th]) >> simp[] >>
     conj_tac >- metis_tac[] >> qexists_tac `j` >> simp[]) >>
  `gas_path_mem ctx func ee 0
     (OK (jump_to cond_lbl (update_var ev (a+(b-a)) (update_var cv a ee))))` by
    (irule for_entry_zero_path_mem >> simp[] >>
     qexistsl_tac [`i1`, `i2`, `i3`] >> simp[]) >>
  `a + (b-a) = b` by wordsLib.WORD_DECIDE_TAC >>
  qabbrev_tac `cc = jump_to cond_lbl (update_var ev b (update_var cv a ee))` >>
  `gas_path_mem ctx func s0 0 (OK cc)` by
    (drule_all gas_path_mem_then >> simp[Abbr `cc`]) >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0` by
    (rpt strip_tac >>
     `x <> p /\ x <> cv /\ x <> ev` by
       (qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
     `lookup_var x ee = lookup_var x s0` by simp[] >>
     pop_assum mp_tac >>
     simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  `alloca_history func cc` by
    (irule alloca_history_jump >>
     conj_tac >- simp[Abbr `cc`, jump_to_def] >>
     qexists_tac `ee` >> simp[Abbr `cc`, jump_to_def, update_var_def]) >>
  `s0.vs_alloca_next <= cc.vs_alloca_next /\
   (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent)` by
    simp[Abbr `cc`, jump_to_def, update_var_def] >>
  `return_buf_frame d cenv sa cc` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `ret_pc_ok cenv sa cc` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  qexistsl_tac [`cc`, `w`] >>
  gvs[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
