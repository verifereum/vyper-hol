(* The bounded return follows the actual successful target evaluation. *)
Theory gasFocusLowerDloadSuccessfulReturn
Ancestors
  gasFocusLowerDloadNonInvokeNext gasFocusLowerDloadInvokeFirstBody
  gasFocusLowerDloadOkDestination gasFocusLowerDloadIntRetPoint
  gasFocusLowerDloadCallReturn lowerDloadSafetyRunInduction
  lowerDloadReturnAlignment gasCount o1SafeUpto venomExecSemantics
  venomExecProofs venomInst venomState finite_map list
Libs
  lowerDloadReturnPackageLib

(* The fixed stage inputs remain free in these ML quotations. Only the
   function, continuation and saved-frame data vary through a nested call. *)
val ret_point = ``\stk fn gn cs fs0 f0 A0 bb t.
  ?PG G tn inst s t0 A frames N X p h.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A frames /\
    gn = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\
    lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
    ld_return_cont C fn cs s /\
    s.vs_gas_readings = t0.vs_gas_readings /\
    t0.vs_gas_readings = t.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames``;

val ret_terminal = ``\stk fn cs fs0 f0 A0 rt u.
  ?sf rs cs' Ar fr tnr rinst se te PG' G' Nr.
    run_blocks sf C fn cs = IntRet rs cs' /\
    ld_sync lo P C vs stk PG' G' tnr fn rinst se te Ar fr Nr /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 Ar fr /\
    rinst.inst_opcode = RET /\
    step_inst 0 C rinst se = IntRet rs cs' /\
    step_inst 0 C' rinst te = IntRet rt u /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo Ar tnr cs' u /\ ld_nonghost tnr cs' u /\
    (!a. a IN ld_slots Ar fs0 ==>
      FLOOKUP (DRESTRICT Ar (ld_slots Ar fs0)) a = FLOOKUP Ar a) /\
    cs'.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH cs'.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) fr``;

val bounded_result = ``\z. (?v. z = OK v /\ gas_cut n vs v) \/
                            (?rt v. z = IntRet rt v /\ gas_cut n vs v)``;

val bounded_entry = ``\gn Point q.
  !m bb sp z. lookup_block q.vs_current_bb gn.fn_blocks = SOME bb /\
    eval_phis q bb.bb_instructions = OK sp /\
    run_block_non_phis m C' bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = z /\
    ^bounded_result z ==>
    Point bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)``;

val ret_step = ``\k ctx ti t z.
  ctx = C' ==>
  !stk fn gn cs fs0 f0 A0 bb.
    ^ret_point stk fn gn cs fs0 f0 A0 bb t /\
    get_instruction bb t.vs_inst_idx = SOME ti ==>
    case z of
      OK q => if is_terminator ti.inst_opcode then
        ~q.vs_halted ==> ^bounded_entry gn (^ret_point stk fn gn cs fs0 f0 A0) q
      else (!z'. run_block_non_phis k C' bb (q with vs_inst_idx := SUC t.vs_inst_idx) = z' /\
                 ^bounded_result z' ==>
                 ^ret_point stk fn gn cs fs0 f0 A0 bb (q with vs_inst_idx := SUC t.vs_inst_idx))
    | IntRet rt u => gas_cut n vs u ==> ^ret_terminal stk fn cs fs0 f0 A0 rt u
    | _ => T``;

val ret_body = ``\(k:num) ctx bb t z.
  ctx = C' ==>
  !stk fn gn cs fs0 f0 A0.
    ^ret_point stk fn gn cs fs0 f0 A0 bb t ==>
    case z of
      OK q => gas_cut n vs q ==> ^bounded_entry gn (^ret_point stk fn gn cs fs0 f0 A0) q
    | IntRet rt u => gas_cut n vs u ==> ^ret_terminal stk fn cs fs0 f0 A0 rt u
    | _ => T``;

val ret_run = ``\(k:num) ctx gn q z.
  ctx = C' ==>
  !stk fn cs fs0 f0 A0.
    case z of
      IntRet rt u => gas_cut n vs u /\ ^bounded_entry gn (^ret_point stk fn gn cs fs0 f0 A0) q ==>
        ^ret_terminal stk fn cs fs0 f0 A0 rt u
    | _ => T``;

val return_induction = ISPECL [ret_step, ret_body, ret_run] ld_successful_run_induction;

Theorem ld_focus_successful_run[local]:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY pre_fmp_ops C.ctx_functions /\ o1_safe_upto D lo n C vs /\
  callee_first names C.ctx_functions /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  (!g. MEM g C.ctx_functions ==> ir_supply_covers_fn (Sigma g.fn_name) g) ==>
  (!fuel ctx ti t z. step_inst fuel ctx ti t = z /\
    ((?v. z = OK v) \/ (?rt v. z = IntRet rt v)) ==> ^ret_step fuel ctx ti t z) /\
  (!fuel ctx bb t z. run_block_non_phis fuel ctx bb t = z /\
    ((?v. z = OK v) \/ (?rt v. z = IntRet rt v)) ==> ^ret_body fuel ctx bb t z) /\
  (!fuel ctx gn t z. run_blocks fuel ctx gn t = z /\
    ((?v. z = OK v) \/ (?rt v. z = IntRet rt v)) ==> ^ret_run fuel ctx gn t z)
Proof
  strip_tac >> match_mp_tac return_induction >> rpt conj_tac
  >- suspend "base"
  >- suspend "invoke"
  >- suspend "next"
  >- suspend "term"
  >- suspend "ret"
  >- suspend "jump"
  >> suspend "return"
QED

(* A successor supplier gives the same point along with its successful fetch.
   Keep the supplied witnesses together when forgetting that extra fetch. *)
val choose_successor =
  let val ws = [`PG1`,`G1`,`tn1`,`i`,`s1`,`b1`,`A1`,`frames1`,`N1`,`Y`,`p1`,`h1`]
  in qx_choosel_then (ws @ [`j`])
       (fn th => qexistsl_tac ws >> strip_assume_tac th >>
                 rpt conj_tac >> first_assum ACCEPT_TAC)
  end;

Resume ld_focus_successful_run[base]:
  BETA_TAC >> map_every qx_gen_tac [`fuel`,`ctx`,`ti`,`t`,`z`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (DISJ_CASES_THEN2 (qx_choose_then `q` SUBST_ALL_TAC)
      (qx_choose_then `rt` (qx_choose_then `u` SUBST_ALL_TAC))))) >>
  disch_then SUBST_ALL_TAC >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC
  >- (rpt gen_tac >> strip_tac >>
      `step_inst fuel C' ti t = OK q` by fs[step_inst_non_invoke] >>
      Cases_on `is_terminator ti.inst_opcode`
      >- (qpat_assum `is_terminator _` (fn th => rewrite_tac[th]) >>
          disch_tac >> rpt gen_tac >>
          disch_then (map_every assume_tac o CONJUNCTS) >>
          drule_all (BETA_RULE (REWRITE_RULE [LET_THM] ld_focus_ok_destination_point)) >>
          disch_then choose_successor) >>
      qpat_assum `~is_terminator _` (fn th => rewrite_tac[th]) >>
      gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `ir_supply_covers_fn (HD frames).lf_supply fn` by
        (drule_all ld_sync_supply_covered >> simp[]) >>
      drule_all (BETA_RULE (REWRITE_RULE [LET_THM] ld_focus_noninvoke_body_next)) >>
      disch_then choose_successor) >>
  rpt gen_tac >> rpt strip_tac >>
  drule_all (BETA_RULE ld_focus_point_intret_terminal) >> strip_tac >>
  goal_assum (drule_at (Pat `run_blocks _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ld_focus_successful_run[invoke]:
  BETA_TAC >> rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  map_every qx_gen_tac [`fuel`,`ctx`,`ti`,`t`,`nm`,`ops`,`calleeT`,`argsT`,`ct`,`rt`,`uc`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disch_then SUBST_ALL_TAC >>
  qpat_x_assum `C' = C' ==> !a b c d e f. _`
    (mk_asm "callee_ih" o REWRITE_RULE [REFL_CLAUSE]) >>
  rpt gen_tac >> strip_tac >>
  `~is_terminator ti.inst_opcode` by fs[is_terminator_def] >>
  qpat_assum `~is_terminator _` (fn th => rewrite_tac[th]) >>
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE ld_focus_invoke_first_body_point) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choosel_then
    [`f`,`fs`,`callee`,`argsS`,`cs'`,`saved`,`fc`,`PG1`,`tn1`,`i`,`Y`,`m`,`b`,`cp'`,`tp`,`j`]
    (map_every assume_tac o CONJUNCTS))) >>
  asm_x "callee_ih" (qspecl_then [`saved::stk`,`callee`,`cs'`,`f::fs`,`fc`,`A`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `bb' = b` by metis_tac[optionTheory.SOME_11] >>
     `sp = cp'` by metis_tac[exec_result_11] >>
     `sp with vs_inst_idx := phi_prefix_length bb'.bb_instructions = tp` by fs[] >>
     pop_assum SUBST1_TAC >> qpat_x_assum `bb' = b` SUBST_ALL_TAC >>
     qexistsl_tac [`PG1`,`FEMPTY`,`tn1`,`i`,`cs'`,`ct`,`A`,`fc::f::fs`,
                   `SUC N`,`Y`,`ct.vs_inst_idx`,`0`] >>
     rpt conj_tac
     >>~- ([`_ = ld_image (HD _)`], rewrite_tac[HD] >> first_assum ACCEPT_TAC)
     >>~- ([`ld_envelope (HD _).lf_supply _ _ _ _ _`],
            rewrite_tac[HD] >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`frames = f::fs`,`X = [inst]`,`ti = inst`,`t0 = t`,`saved = _`] >>
  qpat_assum `gn = ld_image _` (assume_tac o PURE_REWRITE_RULE [HD]) >>
  qpat_assum `ld_envelope (HD (f::fs)).lf_supply _ _ _ _ _`
    (assume_tac o PURE_REWRITE_RULE [HD]) >>
  `?nexti. active_inst gn nexti (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (`^ld_probe_guard C' fuel bb (u with vs_inst_idx := SUC t.vs_inst_idx)` by
       (BETA_TAC >> qexists_tac `z'` >> simp[] >> metis_tac[]) >>
     pop_assum (qx_choose_then `nexti` assume_tac o MATCH_MP
       (BETA_RULE ld_successful_body_fetch) o BETA_RULE) >>
     qexists_tac `nexti` >> rewrite_tac[contextCodegenRelTheory.active_inst_def] >>
     qexists_tac `bb` >>
     qpat_assum `lookup_block t.vs_current_bb gn.fn_blocks = SOME bb`
       (fn th => map_every (fn r => assume_tac (MATCH_MP r th))
         [venomExecProofsTheory.lookup_block_MEM, venomExecProofsTheory.lookup_block_label]) >>
     drule o1LowerDloadRunnerBoundaryTheory.ld_invoke_bind_control >> strip_tac >>
     qpat_x_assum `get_instruction bb (u with vs_inst_idx := _).vs_inst_idx = SOME nexti`
       mp_tac >> simp[get_instruction_def]) >>
  drule_all (BETA_RULE ld_focus_invoke_pop_correlated) >>
  disch_then (qx_choosel_then
    [`PG2`,`G2`,`tn2`,`inst1`,`s1`,`t1`,`A1`,`frames1`,`N1`,`Y1`,`p1`,`h1`]
    (map_every assume_tac o CONJUNCTS)) >>
  `t1.vs_inst_idx = p1` by
    (qpat_x_assum `ld_sync _ _ _ _ stk _ _ _ _ inst s t _ _ _` kall_tac >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
       (drule_all lowerDloadSafetyAmbientTheory.ld_sync_fn_shape >>
        metis_tac[lowerDloadSafetyAmbientTheory.o1_fn_shape_components]) >>
     Cases_on `frames1` >- fs[] >>
     qpat_assum `ld_envelope _ _ s1 _ _ _`
       (assume_tac o PURE_REWRITE_RULE [HD]) >>
     drule_all lowerDloadExpansionEndpointTheory.ld_sync_envelope_position >> simp[]) >>
  qexistsl_tac [`PG2`,`G2`,`tn2`,`inst1`,`s1`,`t1`,`A1`,`frames1`,`N1`,`Y1`,`p1`,`h1`] >>
  `ld_return_cont C fn cs s1` by
    (qpat_assum `!caller_cs. ld_return_cont _ _ caller_cs s ==> _`
      (qspec_then `cs` mp_tac) >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ld_focus_successful_run[next]:
  map_every qx_gen_tac [`fuel`,`ctx`,`bb`,`t`,`ti`,`u`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  BETA_TAC >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `^ret_step fuel C' ti t (OK u)`
    (mk_asm "step" o BETA_RULE) >>
  qpat_x_assum `^ret_body fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) z`
    (mk_asm "body" o BETA_RULE) >>
  qpat_x_assum `(?v. z = OK v) \/ (?rt v. z = IntRet rt v)`
    (DISJ_CASES_THEN2 (qx_choose_then `q` SUBST_ALL_TAC)
      (qx_choose_then `rt` (qx_choose_then `q` SUBST_ALL_TAC))) >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  map_every qx_gen_tac [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`] >>
  disch_then (mk_asm "point") >> disch_tac >>
  asm_x "body" (mp_tac o REWRITE_RULE [REFL_CLAUSE]) >>
  disch_then (qspecl_then [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`] mp_tac) >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  (impl_tac >-
    (asm_x "step" (mp_tac o REWRITE_RULE [REFL_CLAUSE]) >>
     disch_then (qspecl_then [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`,`bb`] mp_tac) >>
     rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
     (impl_tac >- (conj_tac >- asm "point" ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
     simp[] >> metis_tac[])) >>
  simp[]
QED

Resume ld_focus_successful_run[term]:
  map_every qx_gen_tac [`fuel`,`ctx`,`bb`,`t`,`ti`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  BETA_TAC >> disch_then SUBST_ALL_TAC >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  map_every qx_gen_tac [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`] >>
  disch_then (mk_asm "point") >>
  qpat_x_assum `^ret_step fuel C' ti t (OK u)`
    (qspecl_then [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`,`bb`] mp_tac o
     REWRITE_RULE [REFL_CLAUSE] o BETA_RULE) >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  (impl_tac >- (conj_tac >- asm "point" ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  simp[] >> disch_then (fn th => disch_tac >> ACCEPT_TAC th)
QED

Resume ld_focus_successful_run[ret]:
  map_every qx_gen_tac [`fuel`,`ctx`,`bb`,`t`,`ti`,`rt`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  BETA_TAC >> disch_then SUBST_ALL_TAC >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  map_every qx_gen_tac [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`] >>
  disch_then (mk_asm "point") >>
  qpat_x_assum `^ret_step fuel C' ti t (IntRet rt u)`
    (qspecl_then [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`,`bb`] mp_tac o
     REWRITE_RULE [REFL_CLAUSE] o BETA_RULE) >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  (impl_tac >- (conj_tac >- asm "point" ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume ld_focus_successful_run[jump]:
  map_every qx_gen_tac [`fuel`,`ctx`,`gn`,`t`,`bb`,`sp`,`u`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  BETA_TAC >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `(?v. z = OK v) \/ (?rt v. z = IntRet rt v)`
    (DISJ_CASES_THEN2 (qx_choose_then `q` SUBST_ALL_TAC)
      (qx_choose_then `rt` (qx_choose_then `q` SUBST_ALL_TAC)))
  >- simp[] >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  map_every qx_gen_tac [`stk`,`fn`,`cs`,`fs0`,`f0`,`A0`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "entry")) >>
  `LENGTH q.vs_gas_readings <= LENGTH u.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`gn`,`u`] mp_tac (cj 3 gas_count_suffix) >>
     simp[gas_count_suffix_def] >>
     disch_then SUBST1_TAC >> simp[LENGTH_DROP]) >>
  `gas_cut n vs u` by
    (qpat_assum `gas_cut n vs q` mp_tac >>
     rewrite_tac[gas_cut_def] >> decide_tac) >>
  qpat_x_assum `^ret_run fuel C' gn u (IntRet rt q)`
    (qspecl_then [`stk`,`fn`,`cs`,`fs0`,`f0`,`A0`] mp_tac o
     REWRITE_RULE [TypeBase.case_def_of ``:exec_result``,REFL_CLAUSE] o BETA_RULE) >>
  BETA_TAC >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `^ret_body fuel C' bb (sp with vs_inst_idx := _) (OK u)`
       (qspecl_then [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`] mp_tac o
        REWRITE_RULE [TypeBase.case_def_of ``:exec_result``,REFL_CLAUSE] o BETA_RULE) >>
     BETA_TAC >>
     (impl_tac >-
       (asm_x "entry" (qspecl_then [`fuel`,`bb`,`sp`,`OK u`] mp_tac) >> simp[])) >>
     disch_then (fn th => first_assum (fn cut => ACCEPT_TAC (MP th cut))))) >>
  disch_then ACCEPT_TAC
QED

Resume ld_focus_successful_run[return]:
  map_every qx_gen_tac [`fuel`,`ctx`,`gn`,`t`,`bb`,`sp`,`rt`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  BETA_TAC >> disch_then SUBST_ALL_TAC >>
  rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  map_every qx_gen_tac [`stk`,`fn`,`cs`,`fs0`,`f0`,`A0`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "entry")) >>
  qpat_x_assum `^ret_body fuel C' bb (sp with vs_inst_idx := _) (IntRet rt u)`
    (qspecl_then [`stk`,`fn`,`gn`,`cs`,`fs0`,`f0`,`A0`] mp_tac o
     REWRITE_RULE [TypeBase.case_def_of ``:exec_result``,REFL_CLAUSE] o BETA_RULE) >>
  BETA_TAC >>
  (impl_tac >-
    (asm_x "entry" (qspecl_then [`fuel`,`bb`,`sp`,`IntRet rt u`] mp_tac) >> simp[])) >>
  disch_then (fn th => first_assum (fn cut => ACCEPT_TAC (MP th cut)))
QED
Finalise ld_focus_successful_run

Theorem ld_focus_successful_return:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY pre_fmp_ops C.ctx_functions /\ o1_safe_upto D lo n C vs /\
  callee_first names C.ctx_functions /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  (!g. MEM g C.ctx_functions ==> ir_supply_covers_fn (Sigma g.fn_name) g) /\
  run_blocks fuel C' gn ct = IntRet rt u /\ gas_cut n vs u /\
  lookup_block ct.vs_current_bb gn.fn_blocks = SOME bb /\
  eval_phis ct bb.bb_instructions = OK sp /\
  ^ret_point stk fn gn cs fs0 f0 A0 bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
  ^ret_terminal stk fn cs fs0 f0 A0 rt u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (cj 3 ld_focus_successful_run) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`fuel`,`C'`,`gn`,`ct`,`IntRet rt u`] mp_tac) >>
  (impl_tac >- simp[]) >>
  BETA_TAC >> rewrite_tac[TypeBase.case_def_of ``:exec_result``,REFL_CLAUSE] >>
  disch_then (qspecl_then [`stk`,`fn`,`cs`,`fs0`,`f0`,`A0`] mp_tac) >>
  BETA_TAC >> BETA_TAC >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     map_every qx_gen_tac [`m`,`b`,`s`,`z`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `b = bb` by metis_tac[optionTheory.SOME_11] >>
     pop_assum SUBST_ALL_TAC >>
     `s = sp` by metis_tac[exec_result_11] >>
     pop_assum SUBST_ALL_TAC >>
     first_assum (ACCEPT_TAC o BETA_RULE))) >>
  CONV_TAC (RAND_CONV (DEPTH_CONV BETA_CONV)) >>
  disch_then ACCEPT_TAC
QED
