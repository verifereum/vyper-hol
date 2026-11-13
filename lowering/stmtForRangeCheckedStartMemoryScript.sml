Theory stmtForRangeCheckedStartMemory
Ancestors
  stmtForRangeMemoryStart stmtForRangeChecksMemory bodyMemoryDefs localPtrsProps
  stmtSimProps exprSimProps compileEnv loweringStateRelDefs exprLoweringProps fragGasMode fragGasPathMem allocaHistory
  venomExecSemantics venomState venomInst finite_map list rich_list words

Theorem for_range_checked_start_mem:
  !ctx func cenv cx es s0 sa d aa aid sz p pre lbl entry_lbl cond_lbl j
   op1 op2 a b cmp cv rv g1 z1 g2 z2 ev bound i.
    aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
    32 <= sz /\ sz < dimword (:256) /\
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <|bb_label := lbl; bb_instructions := pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|> /\
    lookup_block entry_lbl func.fn_blocks =
      SOME <|bb_label := entry_lbl; bb_instructions :=
        [mk_inst i ASSIGN [op1] [cv];
         mk_inst (i+1) SUB [op2;op1] [rv];
         mk_inst (i+2) cmp [op1;op2] [g1];
         mk_inst (i+3) ISZERO [Var g1] [z1];
         mk_inst (i+4) ASSERT [Var z1] [];
         mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
         mk_inst (i+6) ISZERO [Var g2] [z2];
         mk_inst (i+7) ASSERT [Var z2] [];
         mk_inst (i+8) ADD [op1;Var rv] [ev];
         mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    return_buf_frame d cenv sa s0 /\ ret_pc_ok cenv sa s0 /\
    alloca_history func s0 /\ MEM aa (fn_insts func) /\ fn_inst_ids_distinct func /\
    eval_operand op1 s0 = SOME a /\ eval_operand op2 s0 = SOME b /\
    MEM cmp [SGT;GT] /\ ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev] /\
    (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) /\
    (!x. MEM x [p;cv;rv;g1;z1;g2;z2;ev] ==> not_local_ptr cenv es.scopes x) /\
    (!x. not_fresh_at sa x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) ==>
    (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
       w2n (b-a) > w2n (n2w bound : bytes32)) ==>
      ?t. gas_marked_path T ctx func s0 0 (Abort Revert_abort t)) /\
    (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
     ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
      ?cc w. gas_path_mem ctx func s0 0 (OK cc) /\
        cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
        stmt_state_rel ctx func cenv cx es cc /\
        lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
        lookup_var p cc = SOME w /\ FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
        return_buf_frame d cenv sa cc /\ ret_pc_ok cenv sa cc /\
        alloca_history func cc /\ s0.vs_alloca_next <= cc.vs_alloca_next /\
        (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
        (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0))
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
     conj_tac >-
       (strip_tac >> qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
     qexists_tac `j` >> simp[]) >>
  `eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`eval_operand op1 s0 = SOME a`, `eval_operand op2 s0 = SOME b`,
        `!x. op1 = Var x \/ op2 = Var x ==> _`,
        `!x. x <> p ==> lookup_var x ee = lookup_var x s0`,
        `ee.vs_labels = s0.vs_labels`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `op1` >> Cases_on `op2` >>
     simp[eval_operand_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
       w2n (b-a) > w2n (n2w bound : bytes32) ==>
       ?t. gas_marked_path T ctx func ee 0 (Abort Revert_abort t)) /\
    (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
     ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
      ?vs. lookup_var cv (ee with vs_vars := vs) = SOME a /\
           lookup_var ev (ee with vs_vars := vs) = SOME (a+(b-a)) /\
           (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
             lookup_var x (ee with vs_vars := vs) = lookup_var x ee) /\
           gas_marked_path T ctx func ee 0
             (OK (jump_to cond_lbl (ee with vs_vars := vs))))` by
    (irule for_entry_checked_path_mem >> simp[] >>
     conj_tac >- (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT]) >>
     qexistsl_tac [`i`,`op1`,`op2`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!x. op1 = Var x \/ op2 = Var x ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  conj_tac
  >- (disch_tac >>
      qpat_x_assum `_ ==> ?t. gas_marked_path _ _ _ _ _ (Abort _ _)` mp_tac >>
      simp[] >> strip_tac >>
      qexists_tac `t` >>
      `gas_marked_path T ctx func s0 0 (OK ee)` by simp[gas_marked_path_def] >>
      drule_all gas_marked_path_then >> simp[]) >>
  strip_tac >> qpat_x_assum `_ /\ _ ==> ?vs. _` drule_all >> strip_tac >>
  suspend "success"
QED

Resume for_range_checked_start_mem[success]:
  `stmt_state_rel ctx func cenv cx es (ee with vs_vars := vs)` by
    (irule stmt_state_rel_vars_frame >> simp[] >>
     qpat_assum `!x. MEM x _ ==> not_local_ptr _ _ x` mp_tac >>
     qpat_assum `!x. ~MEM x _ ==> lookup_var _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt disch_tac >> conj_tac
     >- (qx_genl_tac [`nm`,`en`,`q`,`sz`] >> strip_tac >>
         first_x_assum irule >> strip_tac >>
         qpat_x_assum `!x. MEM x _ ==> _` (qspec_then `q` mp_tac) >>
         simp[not_local_ptr_def] >> metis_tac[]) >>
     qx_gen_tac `q` >> strip_tac >> first_x_assum irule >> strip_tac >>
     qpat_x_assum `!x. MEM x _ ==> _` (qspec_then `q` mp_tac) >>
     simp[not_local_ptr_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==>
       lookup_var x (ee with vs_vars := vs) = lookup_var x s0` by
    (rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >>
     simp[] >> strip_tac >>
     qpat_x_assum `!x. ~MEM x _ ==> lookup_var _ _ = _` drule >> simp[]) >>
  qabbrev_tac `cc = jump_to cond_lbl (ee with vs_vars := vs)` >>
  `gas_path_mem ctx func s0 0 (OK cc)` by
    (`gas_marked_path T ctx func s0 0 (OK ee)` by simp[gas_marked_path_def] >>
     `gas_marked_path T ctx func ee 0 (OK cc)` by simp[Abbr `cc`] >>
     drule_all gas_marked_path_then >> simp[gas_marked_path_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x (ee with vs_vars := vs) = _` mp_tac >>
     unabbrev_all_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[lookup_var_def, jump_to_def]) >>
  `return_buf_frame d cenv sa cc` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[Abbr `cc`, jump_to_def]) >>
  `ret_pc_ok cenv sa cc` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `alloca_history func cc` by
    (irule alloca_history_jump >> conj_tac >- simp[Abbr `cc`,jump_to_def] >>
     qexists_tac `ee` >> simp[Abbr `cc`,jump_to_def]) >>
  `lookup_var p (ee with vs_vars := vs) = SOME w` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT] >> strip_tac >>
     qpat_x_assum `!x. ~MEM x _ ==> lookup_var _ _ = _` (qspec_then `p` mp_tac) >>
     simp[]) >>
  qexistsl_tac [`cc`, `w`] >> simp[] >>
  qpat_x_assum `lookup_block entry_lbl _ = _` kall_tac >>
  qpat_x_assum `lookup_block s0.vs_current_bb _ = _` kall_tac >>
  qpat_x_assum `MEM cmp _` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  fs[Abbr `cc`, stmt_state_rel_jump_to, lookup_var_def, jump_to_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Finalise for_range_checked_start_mem
