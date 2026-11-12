Theory bodyPtrBopInBoundedAddress
Ancestors bodyPtrBopInBoundedLayout bodyPtrBopInElementLoad
  bodyPtrBopInLoopContract exprLoweringProps fragExec venomExecSemantics
  venomInst ptrDiscipline fragGasPathPtr words finite_map arithmetic
  loweringStateRelDefs venomState

(* One lookup exposes exactly the arithmetic prefix and the runtime load. *)
Theorem membership_bounded_address_lookup[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ delta = (if 0 < skip then 1 else 0) ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
         fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME
      (mk_inst (sa.cs_next_id+9) MUL
        [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)]
        ["%" ++ toString (sa.cs_next_var+5)]) /\
    (0 < skip ==> get_instruction bb 1 = SOME
      (mk_inst (sa.cs_next_id+10) ADD
        [Lit (n2w skip);Var ("%" ++ toString (sa.cs_next_var+5))]
        ["%" ++ toString (sa.cs_next_var+6)])) /\
    get_instruction bb (1+delta) = SOME
      (mk_inst (sa.cs_next_id+10+delta) ADD
        [arr;Var ("%" ++ toString (sa.cs_next_var+5+delta))]
        ["%" ++ toString (sa.cs_next_var+6+delta)]) /\
    get_instruction bb (2+delta) = SOME
      (mk_inst (sa.cs_next_id+11+delta)
        (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
          LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)
        [Var ("%" ++ toString (sa.cs_next_var+6+delta))]
        ["%" ++ toString (sa.cs_next_var+7+delta)])
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `0 < skip` >> Cases_on `loc` >> simp[get_instruction_def]
QED

Theorem membership_bounded_compiled_load_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ delta = (if 0 < skip then 1 else 0) ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
         fn.fn_blocks = SOME bb /\
    get_instruction bb (2+delta) = SOME
      (mk_inst (sa.cs_next_id+11+delta)
        (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
          LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)
        [Var ("%" ++ toString (sa.cs_next_var+6+delta))]
        ["%" ++ toString (sa.cs_next_var+7+delta)])
Proof
  metis_tac[membership_bounded_address_lookup]
QED

Theorem membership_bounded_product_path[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ dst = "%" ++ toString (sa.cs_next_var+5) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (n2w (stride*i)) s with vs_inst_idx := 1) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all (SRULE [] (Q.INST [`delta` |-> `if 0 < skip then 1 else 0`] membership_bounded_address_lookup)) >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+9) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)]
      ["%" ++ toString (sa.cs_next_var+5)])` by simp[] >>
  `~not_fresh_at sa ("%" ++ toString (sa.cs_next_var+5))` by
    simp[not_fresh_at_def] >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) s = SOME (n2w i) /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_framed_path >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  simp[eval_operand_def, op_taint_def] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[GSYM word_mul_n2w, WORD_MULT_COMM] >>
  goal_assum (drule_at Any) >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
    update_var_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem membership_bounded_offset_path[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 1 /\
  lookup_var ("%" ++ toString (sa.cs_next_var+5)) s = SOME (n2w (stride*i)) /\
  FLOOKUP G ("%" ++ toString (sa.cs_next_var+5)) = NONE /\
  op_taint tn (Var ("%" ++ toString (sa.cs_next_var+5))) = {} /\
  delta = (if 0 < skip then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 1+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (n2w (skip+stride*i)) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> Cases_on `0 < skip`
  >- (drule_all membership_bounded_address_lookup >> strip_tac >>
      `get_instruction bb s.vs_inst_idx = SOME
        (mk_inst (sa.cs_next_id+10) ADD
          [Lit (n2w skip);Var ("%" ++ toString (sa.cs_next_var+5))]
          ["%" ++ toString (sa.cs_next_var+6)])` by simp[] >>
      `~not_fresh_at sa ("%" ++ toString (sa.cs_next_var+6))` by
        simp[not_fresh_at_def] >>
      drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_framed_path >>
      disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
      simp[eval_operand_def, op_taint_def] >> disch_then drule_all >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      goal_assum (drule_at Any) >>
      gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, GSYM word_add_n2w,
        MULT_COMM, op_taint_def] >>
      simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
        op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  `skip = 0` by decide_tac >>
  qexistsl_tac [`G`, `tn`, `s`] >>
  gvs[cj 1 gas_path_ptr_rules]
QED

Theorem membership_bounded_address_path[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 1+delta /\
  off = "%" ++ toString (sa.cs_next_var+5+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) /\
  lookup_var off s = SOME offset /\ FLOOKUP G off = NONE /\
  op_taint tn (Var off) = {} /\ eval_operand arr s = SOME bw /\
  op_taint tn arr = {} ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (bw+offset) s with vs_inst_idx := 2+delta) /\
    FLOOKUP G' dst = op_prov G arr /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_bounded_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+10+delta) ADD
      [arr;Var ("%" ++ toString (sa.cs_next_var+5+delta))]
      ["%" ++ toString (sa.cs_next_var+6+delta)])` by gvs[] >>
  `~not_fresh_at sa ("%" ++ toString (sa.cs_next_var+6+delta))` by
    simp[not_fresh_at_def] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_framed_path >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  gvs[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[ADD1] >> goal_assum (drule_at Any) >>
  Cases_on `op_prov G arr` >>
  gvs[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]
QED

Theorem membership_bounded_runtime_address_prefix:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
  op_taint tn0 arr = {} /\ (!x. arr = Var x ==> not_fresh_at sa x) /\
  delta = (if 0 < skip then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP G' dst = op_prov G0 arr /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all (SRULE [] (GEN_ALL membership_bounded_product_path)) >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G1 tn1 p` >>
  `~p.vs_halted /\ p.vs_inst_idx = 1 /\
   p.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
   lookup_var ("%" ++ toString (sa.cs_next_var+5)) p = SOME (n2w (stride*i))` by
    simp[Abbr `p`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  drule (SRULE [] (GEN_ALL membership_bounded_offset_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ _ _ _`)) >>
  fs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `q` strip_assume_tac)))) >>
  drule_all membership_loop_frame_operand >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_bounded_address_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ _ _ _`)) >>
  fs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G3 tn3 t` >>
  qexistsl_tac [`G3`, `tn3`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[update_var_def] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G1 tn1 p _ G2 tn2 _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G2 tn2 q _ G3 tn3 _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >>
  disch_then (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[]
QED
