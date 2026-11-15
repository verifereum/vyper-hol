Theory forPtrCheckedEntryGhost
Ancestors
  forPtrCheckedScalar instSeqPtrLo bodyPtrSignedConvertClamp instSeqComposePtr
  emitHelperProps exprLoweringProps venomExecProofs ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map pred_set list

Theorem for_checked_entry_ghost_packet:
  code = [mk_inst i ASSIGN [op1] [cv];
    mk_inst (i+1) SUB [op2;op1] [rv];
    mk_inst (i+2) cmp [op1;op2] [g1];
    mk_inst (i+3) ISZERO [Var g1] [z1];
    mk_inst (i+4) ASSERT [Var z1] [];
    mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
    mk_inst (i+6) ISZERO [Var g2] [z2];
    mk_inst (i+7) ASSERT [Var z2] [];
    mk_inst (i+8) ADD [op1;Var rv] [ev]] /\
  MEM cmp [SGT;GT] /\ eval_operand op1 ee = SOME a /\
  eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  ~ctx_has_dalloca ctx /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  k = (if bad1 then 4 else if bad2 then 7 else 9) /\
  ws = (if bad1 then [cv;rv;g1;z1]
        else if bad2 then [cv;rv;g1;z1;g2;z2]
        else [cv;rv;g1;z1;g2;z2;ev]) /\
  Gf = DRESTRICT G (COMPL (set ws)) /\
  tf = (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) ws) ==>
  (!D lo. allocas_from lo ee /\ lo <= ee.vs_alloca_next ==>
    inst_seq_ptr D lo ctx func PG G tn (TAKE k code) ee Gf tf) /\
  ((bad1 \/ bad2) ==> op_taint tf (Var (if bad1 then z1 else z2)) = {})
Proof
  strip_tac >> reverse conj_tac
  >- (Cases_on `bad1` >> Cases_on `bad2` >>
      gvs[op_taint_def, FLOOKUP_UPDATE, FUPDATE_LIST_THM]) >>
  rpt gen_tac >> strip_tac >>
  irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >>
  simp[] >>
  Cases_on `bad1` >> simp[] >>
  `step_inst_base (mk_inst i ASSIGN [op1] [cv]) ee =
     OK (update_var cv a ee)` by simp[step_inst_base_def,mk_inst_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) for_checked_scalar_seq_cons >>
  simp[] >> disch_then (fn th => rewrite_tac[th]) >>
  qabbrev_tac `e1 = update_var cv a ee with vs_inst_idx := SUC ee.vs_inst_idx` >>
  `eval_operand op1 e1 = SOME a /\ eval_operand op2 e1 = SOME b` by
    (simp[Abbr `e1`,instIdxIndepTheory.eval_op_inst_idx] >>
     conj_tac >> irule eval_operand_update_var_mstore >> simp[] >> metis_tac[MEM]) >>
  `step_inst_base (mk_inst (i+1) SUB [op2;op1] [rv]) e1 =
     OK (update_var rv (b-a) e1)` by (irule step_SUB >> simp[]) >>
  dxrule_at (Pat `step_inst_base _ _ = _`) for_checked_scalar_seq_cons >>
  simp[] >>
  strip_tac >>
  `!op. MEM op [op2;op1] ==>
     op_taint (tn with t_var := tn.t_var |+ (cv,{})) op = {} /\
     op_prov (DRESTRICT G (COMPL {cv})) op = NONE` by
    (rw[] >> metis_tac[for_checked_clean_operand_overwrite]) >>
  simp[] >>
  qabbrev_tac `e2 = update_var rv (b-a) e1 with vs_inst_idx := SUC e1.vs_inst_idx` >>
  `eval_operand op1 e2 = SOME a /\ eval_operand op2 e2 = SOME b` by
    (simp[Abbr `e2`,instIdxIndepTheory.eval_op_inst_idx] >>
     conj_tac >> irule eval_operand_update_var_mstore >> simp[] >> metis_tac[MEM]) >>
  qabbrev_tac `p1 = [mk_inst (i+2) cmp [op1;op2] [g1];
                    mk_inst (i+3) ISZERO [Var g1] [z1]]` >>
  qabbrev_tac `w1 = bool_to_word (if cmp = SGT then word_gt a b else w2n a > w2n b)` >>
  qabbrev_tac `e4 = update_var z1 (bool_to_word (w1 = 0w)) (update_var g1 w1 e2)` >>
  `run_inst_seq p1 e2 = OK e4` by
    (`step_inst_base (mk_inst (i+2) cmp [op1;op2] [g1]) e2 =
        OK (update_var g1 w1 e2)` by
       (Cases_on `cmp = SGT`
        >- (qspecl_then [`op1`,`op2`,`a`,`b`] mp_tac step_SGT >>
            simp[Abbr `w1`] >> gvs[]) >>
        `cmp = GT` by gvs[MEM] >>
        qspecl_then [`op1`,`op2`,`a`,`b`] mp_tac step_GT >>
        simp[Abbr `w1`] >> gvs[]) >>
     simp[Abbr `p1`,Once run_inst_seq_def] >>
     irule run_inst_seq_sing_ok >>
     simp[Abbr `e4`] >> irule step_ISZERO >>
     simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `!op. MEM op [op1;op2] ==>
     op_taint (tn with t_var := tn.t_var |+ (cv,{}) |+ (rv,{})) op = {} /\
     op_prov (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {rv})) op = NONE` by
    (rw[] >> simp[for_checked_operand_taint_update,
                  for_checked_operand_prov_restrict]) >>
  `inst_seq_ptr D 0 ctx func PG
     (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {rv}))
     (tn with t_var := tn.t_var |+ (cv,{}) |+ (rv,{})) p1 e2
     (DRESTRICT (DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {cv}))
        (COMPL {rv})) (COMPL {g1})) (COMPL {z1}))
     (tn with t_var := tn.t_var |+ (cv,{}) |+ (rv,{}) |+ (g1,{}) |+ (z1,{}))` by
    (simp[Abbr `p1`] >>
     irule (SRULE [GSYM arithmeticTheory.ADD_ASSOC] (Q.INST
       [`id` |-> `i+2`,
        `G` |-> `DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {rv})`,
        `tn` |-> `tn with t_var := tn.t_var |+ (cv,{}) |+ (rv,{})`]
       (SPEC_ALL scalar_iszero_certificate))) >>
     gvs[MEM]) >>
  gvs[DRESTRICT_DRESTRICT,FUPDATE_LIST_THM,GSYM COMPL_UNION,
      INSERT_UNION_EQ,EMPTY_UNION] >>
  drule_at (Pat `run_inst_seq _ _ = _`) inst_seq_ptr_append_ok >>
  simp[Abbr `p1`,mk_inst_def,is_terminator_def] >>
  disch_then irule >>
  gvs[mk_inst_def] >>
  goal_assum (drule_at Any) >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G4 t4 _ s4 _ _` >>
  `eval_operand (Var z1) s4 = SOME 1w` by
    simp[Abbr `s4`,Abbr `e4`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `op_taint t4 (Var z1) = {}` by simp[Abbr `t4`,op_taint_def,FLOOKUP_UPDATE] >>
  `inst_seq_ptr D 0 ctx func PG G4 t4 [mk_inst (i+4) ASSERT [Var z1] []] s4 G4 t4` by
    (irule clamp_assert_certificate >> simp[] >> goal_assum (drule_at Any)) >>
  `run_inst_seq [mk_inst (i+4) ASSERT [Var z1] []] s4 = OK s4` by
    (irule run_inst_seq_sing_ok >> simp[mk_inst_def] >>
     drule step_assert_behavior >> simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) inst_seq_ptr_append_ok >>
  simp[mk_inst_def,is_terminator_def] >> disch_then irule >>
  gvs[mk_inst_def] >> goal_assum (drule_at Any) >>
  qabbrev_tac `s5 = s4 with vs_inst_idx := s4.vs_inst_idx + 1` >>
  `eval_operand (Var rv) s5 = SOME (b-a)` by
    simp[Abbr `s5`,Abbr `s4`,Abbr `e4`,Abbr `e2`,
         eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  qabbrev_tac `p2 = [mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
                    mk_inst (i+6) ISZERO [Var g2] [z2]]` >>
  qabbrev_tac `w2 = bool_to_word (w2n (b-a) > w2n (n2w bound : bytes32))` >>
  qabbrev_tac `e7 = update_var z2 (bool_to_word (w2 = 0w)) (update_var g2 w2 s5)` >>
  `run_inst_seq p2 s5 = OK e7` by
    (`step_inst_base (mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2]) s5 =
       OK (update_var g2 w2 s5)` by
       (qspecl_then [`Var rv`,`Lit (n2w bound)`,`b-a`,`n2w bound`] mp_tac step_GT >>
        simp[Abbr `w2`] >> disch_then irule >> gvs[eval_operand_def]) >>
     simp[Abbr `p2`,Once run_inst_seq_def] >> irule run_inst_seq_sing_ok >>
     simp[Abbr `e7`,Abbr `w1`] >> irule step_ISZERO >>
     simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `inst_seq_ptr D 0 ctx func PG G4 t4 p2 s5
      (DRESTRICT (DRESTRICT G4 (COMPL {g2})) (COMPL {z2}))
      (t4 with t_var := t4.t_var |+ (g2,{}) |+ (z2,{}))` by
    (simp[Abbr `p2`] >>
     irule (SRULE [GSYM arithmeticTheory.ADD_ASSOC] (Q.INST
       [`id` |-> `i+5`, `G` |-> `G4`, `tn` |-> `t4`]
       (SPEC_ALL scalar_iszero_certificate))) >>
     simp[Abbr `G4`,Abbr `t4`,op_prov_def,op_taint_def,FLOOKUP_UPDATE,
          FLOOKUP_DRESTRICT,eval_operand_def]) >>
  Cases_on `w2n (b-a) > w2n (n2w bound : bytes32)` >>
  gvs[Abbr `G4`,Abbr `t4`,Abbr `w2`,DRESTRICT_DRESTRICT,
      FUPDATE_LIST_THM,GSYM COMPL_UNION,INSERT_UNION_EQ,EMPTY_UNION] >>
  gvs[Abbr `p2`,mk_inst_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) inst_seq_ptr_append_ok >>
  simp[is_terminator_def] >> disch_then irule >>
  goal_assum (drule_at Any) >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G7 t7 _ s7 _ _` >>
  `eval_operand (Var z2) s7 = SOME 1w` by
    simp[Abbr `s7`,Abbr `e7`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `op_taint t7 (Var z2) = {}` by simp[Abbr `t7`,op_taint_def,FLOOKUP_UPDATE] >>
  `inst_seq_ptr D 0 ctx func PG G7 t7 [mk_inst (i+7) ASSERT [Var z2] []] s7 G7 t7` by
    (irule clamp_assert_certificate >> simp[] >> goal_assum (drule_at Any)) >>
  `run_inst_seq [mk_inst (i+7) ASSERT [Var z2] []] s7 = OK s7` by
    (irule run_inst_seq_sing_ok >> simp[mk_inst_def] >>
     drule step_assert_behavior >> simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) inst_seq_ptr_append_ok >>
  simp[mk_inst_def,is_terminator_def] >> disch_then irule >>
  gvs[mk_inst_def] >> goal_assum (drule_at Any) >>
  qabbrev_tac `s8 = s7 with vs_inst_idx := s7.vs_inst_idx + 1` >>
  `eval_operand op1 s8 = SOME a /\ eval_operand (Var rv) s8 = SOME (b-a)` by
    (Cases_on `op1` >>
     gvs[Abbr `s8`,Abbr `s7`,Abbr `e7`,Abbr `s5`,Abbr `s4`,Abbr `e4`,
         Abbr `e2`,Abbr `e1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (i+8) ADD [op1;Var rv] [ev]) s8 =
     OK (update_var ev (a+(b-a)) s8)` by (irule step_ADD >> simp[]) >>
  `!op. MEM op [op1;Var rv] ==>
     op_taint t7 op = {} /\ op_prov G7 op = NONE` by
    (rw[] >> simp[Abbr `t7`,Abbr `G7`,for_checked_operand_taint_update,
                  for_checked_operand_prov_restrict,op_taint_def,op_prov_def,
                  FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  drule_at (Pat `step_inst_base _ _ = _`) for_checked_scalar_seq_cons >>
  simp[mk_inst_def] >> disch_then (fn th => rewrite_tac[th]) >>
  simp[fragGasSeqPtrTheory.inst_seq_ptr_def,Abbr `G7`,Abbr `t7`,DRESTRICT_DRESTRICT,
       GSYM COMPL_UNION,INSERT_UNION_EQ,FUPDATE_LIST_THM]
QED
