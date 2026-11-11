Theory bodyPtrBopInBoundedLoop
Ancestors bodyPtrBopInBoundedLayout bodyPtrBopInLoopSearch
  bodyPtrBopInHeaderControl bodyPtrBopInLoopControl
  bodyPtrBopInLoopContract fragGasPathPtr venomExecSemantics venomInst
  venomState ptrDiscipline finite_map words rich_list

Theorem membership_bounded_condition_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
  s.vs_inst_idx = 0 /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand len s = SOME (n2w k) /\
  op_prov G len = NONE /\ op_taint tn len = {} ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\ t.vs_current_bb =
      (if (n2w i:bytes32) = n2w k then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))
Proof
  strip_tac >> drule_all membership_bounded_condition_lookup >> strip_tac >>
  `(!x. not_fresh_at sa x ==> x <> "%" ++ toString (sa.cs_next_var+4))` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `4` mp_tac) >> simp[]) >>
  irule membership_eq_branch_control >>
  simp[get_instruction_def] >>
  fs[membership_loop_registers_def, eval_operand_def] >>
  qexistsl_tac [`Var ("%" ++ toString (sa.cs_next_var+1))`, `len`,
    `"%" ++ toString (sa.cs_next_var+4)`, `sa.cs_next_id+7`] >>
  simp[eval_operand_def]
QED

Theorem membership_bounded_compared_control:
  !needle arr len stride skip is_ctor imm loc cap is_in sa op sb.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) ==>
  !fn ctx s G0 tn0 s0 G tn i r a w D PG.
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+6+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) s = SOME a /\
  op_prov G (Var ("%" ++ toString (sa.cs_next_var+6+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
  op_taint tn (Var ("%" ++ toString (sa.cs_next_var+6+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {} /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\
  op_taint tn needle = {} ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if a = w then
      fresh_label_output "in_found" (sa.cs_next_label+3) else
      fresh_label_output "in_incr" (sa.cs_next_label+4))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule (GEN_ALL membership_bounded_compare_lookup) >>
  disch_then (qspecl_then [`if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1`,
    `fn`, `if 0 < skip then 1 else 0`] mp_tac) >>
  simp[] >> strip_tac >>
  drule membership_drop_pair_lookup >> strip_tac >>
  `(!x. not_fresh_at sa x ==>
    x <> "%" ++ toString (sa.cs_next_var+7+(if 0 < skip then 1 else 0)+
      (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `7+(if 0 < skip then 1 else 0)+
       (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)` mp_tac) >> simp[]) >>
  irule membership_eq_branch_control >> simp[] >>
  qexistsl_tac [`Var ("%" ++ toString (sa.cs_next_var+6+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))`,
    `needle`, `"%" ++ toString (sa.cs_next_var+7+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))`,
    `sa.cs_next_id+11+(if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)`] >>
  gvs[] >> Cases_on `0 < skip` >>
  Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> gvs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem membership_bounded_found_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3) /\
  s.vs_inst_idx = 0 /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i 1w G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  strip_tac >>
  drule (GEN_ALL membership_bounded_found_lookup) >>
  disch_then (qspecl_then [`if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1`,
    `fn`, `if 0 < skip then 1 else 0`] mp_tac) >>
  simp[] >> strip_tac >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i 1w G' tn' t /\
    t = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5))
      (update_var ("%" ++ toString sa.cs_next_var) 1w s)` by
    (irule membership_found_frame >> simp[get_instruction_def] >>
     conj_tac
     >- (qexists_tac `sa.cs_next_id+13+(if 0 < skip then 1 else 0)+
           (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)` >> simp[]) >>
     goal_assum (drule_at Any)) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def]
QED

Theorem membership_bounded_increment_control:
  !needle arr len stride skip is_ctor imm loc cap is_in sa op sb.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) ==>
  !fn ctx s G0 tn0 s0 G tn i r D PG.
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
  s.vs_inst_idx = 0 /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa (SUC i) r G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule (GEN_ALL membership_bounded_increment_lookup) >>
  disch_then (qspecl_then [`if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1`,
    `fn`, `if 0 < skip then 1 else 0`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD _ [tmp]` >>
  `(!x. not_fresh_at sa x ==> x <> tmp)` by
    (simp[Abbr `tmp`, loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `8+(if 0 < skip then 1 else 0)+
       (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)` mp_tac) >> simp[]) >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa (SUC i) r G' tn' t /\
    t = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
      (update_var ("%" ++ toString (sa.cs_next_var+1)) (n2w (SUC i))
        (update_var tmp (n2w (SUC i)) s))` by
    (irule membership_increment_frame >> simp[get_instruction_def] >>
     conj_tac >- (gvs[Abbr `tmp`] >> metis_tac[]) >>
     conj_tac >- (simp[Abbr `tmp`] >> Cases_on `0 < skip` >>
       Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]) >>
     qexists_tac `sa.cs_next_id+15+(if 0 < skip then 1 else 0)+
       (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)` >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def]
QED

Theorem membership_bounded_loop_init:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand len s = SOME (n2w n) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  n <= cap /\ cap < dimword (:256) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    membership_loop_registers sa 0 0w G' tn' t /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    t.vs_inst_idx = 0
Proof
  strip_tac >> drule_all membership_bounded_entry_lookup >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block entry fn.fn_blocks = SOME entry_bb` >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `result = "%" ++ toString sa.cs_next_var` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to entry s))` by
    (irule membership_jump_path >> metis_tac[]) >>
  qabbrev_tac `s1 = jump_to entry s` >>
  `gas_path_ptr D 0 ctx fn PG G tn s1 0 (DRESTRICT G (COMPL {idx}))
    (tn with t_var := set_var_taint tn.t_var [idx] {})
    (OK (update_var idx 0w s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule membership_assign_literal_path >>
     simp[Abbr `s1`, Abbr `idx`, jump_to_def, get_instruction_def] >>
     metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ s1 _ G1 tn1 (OK s2)` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s2 0 (DRESTRICT G1 (COMPL {result}))
    (tn1 with t_var := set_var_taint tn1.t_var [result] {})
    (OK (update_var result 0w s2 with vs_inst_idx := SUC s2.vs_inst_idx))` by
    suspend "assign_result" >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ s2 _ G2 tn2 (OK s3)` >>
  `membership_loop_frame sa G tn s G2 tn2 s3 /\
   membership_loop_registers sa 0 0w G2 tn2 s3 /\ ~s3.vs_halted /\
   s3.vs_current_bb = entry /\ s3.vs_inst_idx = 2` by
    suspend "init_frame" >>
  `eval_operand len s3 = SOME (n2w n) /\ op_prov G2 len = NONE /\
   op_taint tn2 len = {}` by metis_tac[membership_loop_frame_operand] >>
  `?G3 tn3 s4. gas_path_ptr D 0 ctx fn PG G2 tn2 s3 0 G3 tn3 (OK s4) /\
    s4 = (update_var ("%" ++ toString (sa.cs_next_var+3)) 1w
      (update_var ("%" ++ toString (sa.cs_next_var+2)) 0w s3)
      with vs_inst_idx := 5) /\
    tn3 = (tn2 with t_var := tn2.t_var |+
      ("%" ++ toString (sa.cs_next_var+2),{}) |+
      ("%" ++ toString (sa.cs_next_var+3),{})) /\
    FLOOKUP G3 ("%" ++ toString (sa.cs_next_var+3)) = NONE /\
    (!x. x <> "%" ++ toString (sa.cs_next_var+2) /\
         x <> "%" ++ toString (sa.cs_next_var+3) ==>
         FLOOKUP G3 x = FLOOKUP G2 x)` by
    suspend "capacity" >>
  `gas_path_ptr D 0 ctx fn PG G3 tn3 s4 0 G3 tn3
    (OK (jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) s4))` by
    (irule membership_jump_path >>
     simp[get_instruction_def, update_var_def] >> metis_tac[]) >>
  `membership_loop_frame sa G tn s G3 tn3
    (jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) s4) /\
   membership_loop_registers sa 0 0w G3 tn3
    (jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) s4)` by
    suspend "capacity_frame" >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[jump_to_def, update_var_def]
QED

Resume membership_bounded_loop_init[assign_result]:
  irule (SRULE [] (Q.INST [`s` |-> `s2`, `G` |-> `G1`, `tn` |-> `tn1`]
    membership_assign_literal_path)) >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `result`, Abbr `entry`,
    update_var_def, jump_to_def, get_instruction_def] >> metis_tac[]
QED

Resume membership_bounded_loop_init[init_frame]:
  simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `G1`,
    Abbr `tn2`, Abbr `tn1`, Abbr `idx`, Abbr `result`,
    membership_loop_frame_def, membership_loop_registers_def, op_prov_def,
    jump_to_def, update_var_def, lookup_var_def, FLOOKUP_DRESTRICT,
    op_taint_def, set_var_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString (sa.cs_next_var+1)) /\
   x <> STRING #"%" (toString sa.cs_next_var)` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.ADD_0]) >> simp[]
QED

Resume membership_bounded_loop_init[capacity]:
  `get_instruction entry_bb s3.vs_inst_idx = SOME
     (mk_inst (sa.cs_next_id+3) GT [len;Lit (n2w cap)]
       ["%" ++ toString (sa.cs_next_var+2)]) /\
   get_instruction entry_bb (SUC s3.vs_inst_idx) = SOME
     (mk_inst (sa.cs_next_id+4) ISZERO
       [Var ("%" ++ toString (sa.cs_next_var+2))]
       ["%" ++ toString (sa.cs_next_var+3)]) /\
   get_instruction entry_bb (s3.vs_inst_idx+2) = SOME
     (mk_inst (sa.cs_next_id+5) ASSERT
       [Var ("%" ++ toString (sa.cs_next_var+3))] [])` by
    simp[get_instruction_def] >>
  `lookup_block s3.vs_current_bb fn.fn_blocks = SOME entry_bb` by simp[] >>
  drule_all membership_capacity_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[]
QED

Resume membership_bounded_loop_init[capacity_frame]:
  fs[membership_loop_frame_def, membership_loop_registers_def, op_prov_def] >>
  simp[membership_loop_frame_def, membership_loop_registers_def,
    jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    op_taint_def, op_prov_def] >>
  conj_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          `x <> "%" ++ toString (sa.cs_next_var+2) /\
           x <> "%" ++ toString (sa.cs_next_var+3)` by
            (fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
             conj_tac >> qpat_x_assum `!n. sa.cs_next_var <= n ==> x <> _` irule >> simp[]) >>
          qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
          fs[lookup_var_def, op_taint_def]) >>
      qpat_x_assum `s3 = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[Abbr `idx`, Abbr `result`, lookup_var_def, op_taint_def]
QED

Finalise membership_bounded_loop_init

Theorem membership_bounded_load_compare_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_element_load_contract D ctx fn PG sa
    (2+(if 0 < skip then 1 else 0)+(if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))
    (Var ("%" ++ toString (sa.cs_next_var+6+(if 0 < skip then 1 else 0)+
      (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) ws G0 tn0 s0 /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s0 = SOME w /\ op_prov G0 needle = NONE /\
  op_taint tn0 needle = {} /\ i < LENGTH ws /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i 0w G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i 0w G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\ t.vs_current_bb =
      (if EL i ws = w then fresh_label_output "in_found" (sa.cs_next_label+3)
       else fresh_label_output "in_incr" (sa.cs_next_label+4))
Proof
  strip_tac >>
  qpat_x_assum `membership_element_load_contract _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [membership_element_load_contract_def]) >>
  disch_then (qspecl_then [`i`, `G`, `tn`, `s`] mp_tac) >> simp[] >> strip_tac >>
  `eval_operand needle t = SOME w /\ op_prov G' needle = NONE /\
    op_taint tn' needle = {}` by metis_tac[membership_loop_frame_operand] >>
  drule membership_bounded_compared_control >>
  disch_then (drule_all o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []) >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`G''`, `tn''`, `t'`] >> simp[]
QED

Theorem membership_bounded_search_suffix:
  !i G tn s.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_element_load_contract D ctx fn PG sa
    (2+(if 0 < skip then 1 else 0)+(if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))
    (Var ("%" ++ toString (sa.cs_next_var+6+(if 0 < skip then 1 else 0)+
      (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) ws G0 tn0 s0 /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s0 = SOME w /\ op_prov G0 needle = NONE /\
  op_taint tn0 needle = {} /\
  eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
  op_prov G0 len = NONE /\ op_taint tn0 len = {} /\
  LENGTH ws < dimword (:256) /\ i <= LENGTH ws /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i 0w G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
  s.vs_inst_idx = 0 ==>
  ?G' tn' t j. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) G' tn' t /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  measureInduct_on `LENGTH ws - i` >> rpt strip_tac >>
  `eval_operand len s = SOME (n2w (LENGTH ws)) /\
    op_prov G len = NONE /\ op_taint tn len = {}` by
    metis_tac[membership_loop_frame_operand] >>
  drule_all membership_bounded_condition_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  Cases_on `i = LENGTH ws`
  >- (gvs[bool_to_word_def] >>
      qexistsl_tac [`G'`, `tn'`, `t`, `LENGTH ws`] >> simp[]) >>
  `(n2w i:bytes32) <> n2w (LENGTH ws)` by
    (`i < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  gvs[] >> `i < LENGTH ws` by decide_tac >>
  drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []
    membership_bounded_load_compare_control) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `DROP i ws = EL i ws :: DROP (SUC i) ws` by
    metis_tac[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `EL i ws = w`
  >- suspend "found" >>
  gvs[] >> suspend "incr"
QED

Resume membership_bounded_search_suffix[found]:
  gvs[] >> drule_all membership_bounded_found_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `i` >> simp[]
QED

Resume membership_bounded_search_suffix[incr]:
  drule membership_bounded_increment_control >> disch_then drule_all >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC i` mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `j` >> simp[]
QED

Finalise membership_bounded_search_suffix

Theorem membership_bounded_notin_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    eval_operand op t = SOME (bool_to_word (r = 0w)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 1
Proof
  strip_tac >> drule_all membership_bounded_notin_exit_lookup >> strip_tac >>
  drule membership_bounded_loop_exit >> simp[] >> strip_tac >>
  `(!x. not_fresh_at sa x ==>
    x <> "%" ++ toString (sa.cs_next_var+9+delta+width))` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `9+delta+width` mp_tac) >> simp[]) >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+9+delta+width))) t =
      SOME (bool_to_word (r = 0w)) /\
    op_prov G' (Var ("%" ++ toString (sa.cs_next_var+9+delta+width))) = NONE /\
    op_taint tn' (Var ("%" ++ toString (sa.cs_next_var+9+delta+width))) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx` by
    (irule membership_iszero_frame >>
     fs[membership_loop_registers_def] >> simp[eval_operand_def] >>
     conj_tac >- gvs[] >>
     qexistsl_tac [`Var ("%" ++ toString sa.cs_next_var)`,
       `sa.cs_next_id+18+delta+width`] >>
     simp[get_instruction_def] >>
     Cases_on `bb.bb_instructions` >> gvs[eval_operand_def]) >>
  gvs[] >> qexistsl_tac [`G'`, `tn'`, `t`] >> simp[]
QED

Theorem membership_bounded_finish_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i (bool_to_word b) G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
  s.vs_inst_idx = 0 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    eval_operand op t = SOME (bool_to_word (if is_in then b else ~b)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule membership_bounded_loop_exit >> strip_tac >>
  Cases_on `is_in`
  >- (gvs[] >> qexistsl_tac [`G`, `tn`, `s`] >>
      fs[membership_loop_registers_def] >> simp[eval_operand_def] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  fs[] >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    eval_operand op t = SOME (bool_to_word (bool_to_word b = 0w)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 1` by
    (irule membership_bounded_notin_control >> simp[] >> conj_tac
     >- (goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
     qexists_tac `i` >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >> Cases_on `b` >> gvs[bool_to_word_def]
QED

Theorem membership_bounded_loop_conditional:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_element_load_contract D ctx fn PG sa
    (2+(if 0 < skip then 1 else 0)+(if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))
    (Var ("%" ++ toString (sa.cs_next_var+6+(if 0 < skip then 1 else 0)+
      (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) ws G tn s /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} /\
  eval_operand len s = SOME (n2w (LENGTH ws)) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\ LENGTH ws <= cap /\ cap < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all membership_bounded_loop_init >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  `LENGTH ws < dimword (:256)` by decide_tac >> fs[] >>
  mp_tac (GEN_ALL (Q.SPEC `0` membership_bounded_search_suffix)) >>
  disch_then (drule_all o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  drule_all membership_bounded_finish_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
