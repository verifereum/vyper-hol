(* Lift a reached initializer prefix or an empty terminal revert. *)
Theory groupedRejectTerminal
Ancestors
  ptrDiscipline fragGasOriginPtr list fragExec fragGasOrigin fragGasPath fragGasPathPtr
  gasEvents ptrSafeRun oracleExecProps pred_set opcodeClass venomExecSemantics venomInst
  venomState callRejectMemory[ignore_grammar] venomExecProofs compileEnv vyperContext finite_map
  rich_list words pair arithmetic relation vyperAST
Libs
  runtimeDefaultRejectSyntaxLib

val _ = Parse.hide "tops";

Theorem entry_default_terminal_empty_abort[local]:
  ~MEM inst.inst_opcode
    [INVOKE; STOP; RETURN; SINK; RET; RETFMP; DRET;
     INVALID; ASSERT_UNREACHABLE; CREATE; CREATE2; RETURNDATACOPY;
     CALL; STATICCALL; DELEGATECALL; SSTORE; TSTORE; LOG; SELFDESTRUCT] /\
  (inst.inst_opcode = REVERT ==> inst.inst_operands = [Lit 0w; Lit 0w]) /\
  exit_result r /\ step_inst fuel ctx inst s = r ==>
  ?z. r = Abort Revert_abort z /\ z.vs_returndata = []
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `r` >> gvs[exit_result_def, step_inst_non_invoke]
  >- (drule step_inst_base_halt_opcodes >> simp[])
  >- (drule step_inst_base_abort_opcodes >> strip_tac >> gvs[] >>
      qpat_x_assum `step_inst_base inst s = _` mp_tac >>
      simp[step_inst_base_opcode_eqs, eval_operand_def, AllCaseEqs(),
           revert_state_def, set_returndata_def] >> rpt strip_tac >> gvs[]) >>
  drule step_inst_base_intret_opcodes >> simp[]
QED

Theorem entry_nonconsuming_ptr_step_any_dead[local]:
  ~MEM inst.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL;
    CREATE; CREATE2] /\
  (!t. step_inst fuel ctx inst s <> Halt t) /\
  ptr_safe_step D lo fuel ctx func PG G tn inst s ==>
  ptr_safe_step D' lo fuel ctx func PG G tn inst s
Proof
  strip_tac >> fs[] >>
  `!t. step_inst fuel ctx inst s = OK t ==> t.vs_requests = s.vs_requests` by
    (rpt strip_tac >> drule_all step_inst_noninvoke_oracle >> simp[]) >>
  fs[ptr_safe_step_def, ptr_inst_ok_def] >> rpt strip_tac >> res_tac >> fs[]
QED

Theorem entry_nonconsuming_origin_edge[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~MEM inst.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL;
    CREATE; CREATE2] /\
  (!t. r <> Halt t) /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) marks (r,G',tn') ==>
  gas_origin_ptr_edge (D',lo,EMPTY,ctx,func,PG) (s,G,tn) (MAP (K F) marks) (r,G',tn')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`fuel`,`run_bb`,`run_inst`,`middle`]
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `run_bb = bb` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  `run_inst = inst` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  `!t. step_inst fuel ctx inst s <> Halt t` by
    (rpt strip_tac >> gvs[exit_result_def]) >>
  `ptr_safe_step D' lo fuel ctx func PG G tn inst s` by
    (irule entry_nonconsuming_ptr_step_any_dead >> simp[] >> qexists_tac `D` >> simp[]) >>
  rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
  >- (simp[gas_origin_edge_def] >> qexists_tac `fuel` >>
      fs[MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  simp[gas_path_ptr_edge_def] >> qexists_tac `fuel` >>
  fs[gas_events_length] >> metis_tac[]
QED

Theorem entry_origin_edge_erase:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) marks (r,G',tn') ==>
  gas_path_edge ctx func s (LENGTH marks) r
Proof
  rewrite_tac[gas_origin_ptr_edge_def] >>
  disch_then (ACCEPT_TAC o MATCH_MP gas_path_ptr_edge_erase o CONJUNCT2)
QED

Theorem entry_exit_edge_empty_revert[local]:
  gas_path_edge ctx fn s n r /\ exit_result r /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~MEM inst.inst_opcode
    [INVOKE; STOP; RETURN; SINK; RET; RETFMP; DRET;
     INVALID; ASSERT_UNREACHABLE; CREATE; CREATE2; RETURNDATACOPY;
     CALL; STATICCALL; DELEGATECALL; SSTORE; TSTORE; LOG; SELFDESTRUCT] /\
  (inst.inst_opcode = REVERT ==> inst.inst_operands = [Lit 0w; Lit 0w]) ==>
  ?z. r = Abort Revert_abort z /\ z.vs_returndata = []
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `gas_path_edge _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_path_edge_def]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choosel_then
    [`fuel`,`run_bb`,`run_inst`,`middle`] (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `run_bb = bb` by metis_tac[optionTheory.SOME_11] >> pop_assum SUBST_ALL_TAC >>
  `run_inst = inst` by metis_tac[optionTheory.SOME_11] >> pop_assum SUBST_ALL_TAC >>
  `?fuel. step_inst fuel ctx inst s = r` by
    (qpat_x_assum `(?t. middle = OK t /\ ~is_terminator _ /\ _) \/ _`
       strip_assume_tac >>
     gvs[exit_result_def, step_inst_non_invoke] >>
     metis_tac[venomExecProofsTheory.step_inst_base_OK_preserves_halted]) >>
  metis_tac[entry_default_terminal_empty_abort]
QED

Theorem entry_replay_default_through_cut:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,H,tz) /\
  (!t. r = OK t ==> at_cut t) /\
  P s /\
  (!u v n. P u /\ ~at_cut u /\ gas_path_edge ctx fn u n (OK v) ==> P v) /\
  (!u bb i. P u /\ ~at_cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> safe i) /\
  (!i. safe i ==> ^default_opcode i.inst_opcode) ==>
  (?z J tj tags. z.vs_returndata = [] /\
    !D'. gas_origin_ptr_path (D',lo,EMPTY,ctx,fn,PG)
      (s,G,tn) tags (Abort Revert_abort z,J,tj)) \/
  (?t J tj tags. P t /\ at_cut t /\
    !D'. gas_origin_ptr_path (D',lo,EMPTY,ctx,fn,PG)
      (s,G,tn) tags (OK t,J,tj))
Proof
  qsuff_tac `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
    !s G tn.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\
      (!t. FST out = OK t ==> at_cut t) /\
      P s /\
      (!u v n. P u /\ ~at_cut u /\ gas_path_edge ctx fn u n (OK v) ==> P v) /\
      (!u bb i. P u /\ ~at_cut u /\
        lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb u.vs_inst_idx = SOME i ==> safe i) /\
      (!i. safe i ==> ^default_opcode i.inst_opcode) ==>
      (?z J tj tags. z.vs_returndata = [] /\
        !D'. gas_origin_ptr_path (D',lo,EMPTY,ctx,fn,PG)
          (s,G,tn) tags (Abort Revert_abort z,J,tj)) \/
      (?t J tj tags. P t /\ at_cut t /\
        !D'. gas_origin_ptr_path (D',lo,EMPTY,ctx,fn,PG)
          (s,G,tn) tags (OK t,J,tj))`
  >- (strip_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_x_assum `!cx st marks out. _`
        (qspecl_then [`(D,lo,explicit,ctx,fn,PG)`,`(s,G,tn)`,`marks`,`(r,H,tz)`] mp_tac) >>
      asm_simp_tac bool_ss [pairTheory.FST, pairTheory.PAIR_EQ] >> metis_tac[]) >>
  ho_match_mp_tac gas_origin_ptr_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  gvs[pairTheory.PAIR_EQ, exit_result_def]
  >- (disj2_tac >> qexistsl_tac [`s`,`G`,`tn`,`[]`] >> simp[gas_origin_ptr_path_rules])
  >- suspend "continue"
  >> suspend "abort"
QED

Resume entry_replay_default_through_cut[continue]:
  `gas_path_edge ctx fn s (LENGTH left) (OK mid)` by
    metis_tac[entry_origin_edge_erase] >>
  `~s.vs_halted` by
    (qpat_assum `gas_path_edge ctx fn s _ _`
      (ACCEPT_TAC o cj 1 o REWRITE_RULE [gas_path_edge_def])) >>
  Cases_on `at_cut s`
  >- (disj2_tac >> qexistsl_tac [`s`,`G`,`tn`,`[]`] >> simp[gas_origin_ptr_path_rules]) >>
  `P mid` by metis_tac[] >>
  `!D'. gas_origin_ptr_edge (D',lo,EMPTY,ctx,fn,PG) (s,G,tn)
      (MAP (K F) left) (OK mid,G1,tn1)` by
    (gen_tac >> qpat_assum `gas_origin_ptr_edge _ _ _ _`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_edge_common_fuel) >>
     `safe inst` by metis_tac[] >>
     `^default_opcode inst.inst_opcode` by
       (BETA_TAC >> simp[] >>
        qpat_assum `!i. safe i ==> _` (drule_then ACCEPT_TAC)) >>
     mp_tac (Q.INST [`func` |-> `fn`,`bb` |-> `bb`,`inst` |-> `inst`,
       `r` |-> `OK mid`,`marks` |-> `left`,`G'` |-> `G1`,`tn'` |-> `tn1`]
       entry_nonconsuming_origin_edge) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> fs[]) >>
     simp[]) >>
  qpat_x_assum `P mid /\ _ ==> (?z J tj tags. _) \/ _` mp_tac >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN strip_assume_tac))
  >- (qmatch_asmsub_rename_tac
        `gas_origin_ptr_path _ (mid,G1,tn1) tail (Abort Revert_abort z,J,tj)` >>
      disj1_tac >> qexistsl_tac [`z`,`J`,`tj`,`MAP (K F) left ++ tail`] >>
      simp[] >> metis_tac[cj 2 gas_origin_ptr_path_rules]) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (mid,G1,tn1) tail (OK t,J,tj)` >>
  disj2_tac >> qexistsl_tac [`t`,`J`,`tj`,`MAP (K F) left ++ tail`] >>
  simp[] >> metis_tac[cj 2 gas_origin_ptr_path_rules]
QED

Resume entry_replay_default_through_cut[abort]:
  `gas_path_edge ctx fn s (LENGTH marks) r` by
    metis_tac[entry_origin_edge_erase] >>
  `~s.vs_halted` by
    (qpat_assum `gas_path_edge ctx fn s _ _`
      (ACCEPT_TAC o cj 1 o REWRITE_RULE [gas_path_edge_def])) >>
  Cases_on `at_cut s`
  >- (disj2_tac >> qexistsl_tac [`s`,`G`,`tn`,`[]`] >> simp[gas_origin_ptr_path_rules]) >>
  qpat_assum `gas_origin_ptr_edge _ _ _ _`
    (qx_choosel_then [`fuel`,`bb`,`inst`,`middle`]
      (fn th => map_every assume_tac (List.take (CONJUNCTS th, 2))) o
      cj 2 o MATCH_MP gas_origin_ptr_edge_common_fuel) >>
  `safe inst` by metis_tac[] >>
  `^default_opcode inst.inst_opcode` by
    (BETA_TAC >> simp[] >>
     qpat_assum `!i. safe i ==> _` (drule_then ACCEPT_TAC)) >>
  `?z. r = Abort Revert_abort z /\ z.vs_returndata = []` by
    (mp_tac (Q.INST [`n` |-> `LENGTH (marks:bool list)`]
       entry_exit_edge_empty_revert) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> fs[]) >>
     simp[]) >>
  `!D'. gas_origin_ptr_edge (D',lo,EMPTY,ctx,fn,PG) (s,G,tn)
    (MAP (K F) marks) (r,G',tn')` by
    (gen_tac >> mp_tac (Q.INST [`func` |-> `fn`] entry_nonconsuming_origin_edge) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> fs[exit_result_def]) >>
     simp[]) >>
  qpat_x_assum `r = Abort Revert_abort z` SUBST_ALL_TAC >>
  disj1_tac >> qexistsl_tac [`z`,`G'`,`tn'`,`MAP (K F) marks`] >>
  simp[] >> metis_tac[cj 3 gas_origin_ptr_path_rules]
QED

Finalise entry_replay_default_through_cut
