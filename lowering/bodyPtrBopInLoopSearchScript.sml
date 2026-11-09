Theory bodyPtrBopInLoopSearch
Ancestors bodyPtrBopInLoopContract bodyPtrBopInLoopSegments bodyPtrBopInLoopCode
  bodyPtrBopInLiteralSuffix fragGasSeqPtr ptrSafeRun venomExecSemantics
  contextCodegenRel codegenRel fragGasPathPtr
  venomInst venomState ptrDiscipline finite_map words pred_set

Theorem membership_frame_scalar_jump:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. not_fresh_at sa x ==> x <> dst) /\
  (!x. x <> dst ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (tn' with t_var := tn.t_var) = tn ==>
  membership_loop_frame sa G0 tn0 s0 G' tn'
    (jump_to lbl (update_var dst w s))
Proof
  strip_tac >> fs[membership_loop_frame_def, taint_component_equality] >>
  reverse conj_tac
  >- (qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >>
      simp[jump_to_def, update_var_def]) >>
  rpt strip_tac >> `x <> dst` by metis_tac[] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[lookup_var_def]
QED

Theorem membership_eq_branch_frame:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [a;b] [dst]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) JNZ [Var dst;Label lt;Label lf] []) /\
  eval_operand a s = SOME aw /\ eval_operand b s = SOME bw /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  (!x. not_fresh_at sa x ==> x <> dst) /\
  dst <> "%" ++ toString (sa.cs_next_var+1) /\
  dst <> "%" ++ toString sa.cs_next_var ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to (if aw = bw then lt else lf)
        (update_var dst (bool_to_word (aw = bw)) s))) /\
    membership_loop_frame sa G0 tn0 s0 G' tn'
      (jump_to (if aw = bw then lt else lf)
        (update_var dst (bool_to_word (aw = bw)) s)) /\
    membership_loop_registers sa i r G' tn'
      (jump_to (if aw = bw then lt else lf)
        (update_var dst (bool_to_word (aw = bw)) s))
Proof
  strip_tac >> drule_all membership_eq_branch_path >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> conj_tac
  >- (drule_all membership_frame_scalar_jump >> simp[]) >>
  fs[membership_loop_registers_def, op_prov_def] >>
  simp[membership_loop_registers_def, jump_to_def, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE, op_prov_def] >> metis_tac[lookup_var_def]
QED

Theorem membership_condition_frame:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
  s.vs_inst_idx = 0 /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand len s = SOME (n2w k) /\
  op_prov G len = NONE /\ op_taint tn len = {} ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to (if (n2w i:bytes32) = n2w k then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))
        (update_var ("%" ++ toString (sa.cs_next_var+2))
          (bool_to_word ((n2w i:bytes32) = n2w k)) s))) /\
    membership_loop_frame sa G0 tn0 s0 G' tn'
      (jump_to (if (n2w i:bytes32) = n2w k then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))
        (update_var ("%" ++ toString (sa.cs_next_var+2))
          (bool_to_word ((n2w i:bytes32) = n2w k)) s)) /\
    membership_loop_registers sa i r G' tn'
      (jump_to (if (n2w i:bytes32) = n2w k then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))
        (update_var ("%" ++ toString (sa.cs_next_var+2))
          (bool_to_word ((n2w i:bytes32) = n2w k)) s))
Proof
  strip_tac >> drule_all membership_compiled_condition_lookup >> strip_tac >>
  `(!x. not_fresh_at sa x ==> x <> "%" ++ toString (sa.cs_next_var+2))` by
    (simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
  irule membership_eq_branch_frame >>
  simp[venomInstTheory.get_instruction_def] >>
  fs[membership_loop_registers_def, eval_operand_def] >>
  qexistsl_tac [`Var ("%" ++ toString (sa.cs_next_var+1))`, `len`,
    `sa.cs_next_id+4`] >> simp[eval_operand_def]
QED

Theorem membership_found_frame:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME
    (mk_inst id ASSIGN [Lit 1w] ["%" ++ toString sa.cs_next_var]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) JMP [Label exit] []) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i 1w G' tn' t /\
    t = jump_to exit (update_var ("%" ++ toString sa.cs_next_var) 1w s)
Proof
  strip_tac >> drule_all membership_found_path >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (drule membership_frame_scalar_jump >>
      disch_then irule >>
      simp[FLOOKUP_DRESTRICT, op_taint_def, set_var_taint_def,
        FLOOKUP_UPDATE, compileEnvTheory.not_fresh_at_def] >>
      metis_tac[arithmeticTheory.ADD_0]) >>
  fs[membership_loop_registers_def, op_prov_def] >>
  simp[membership_loop_registers_def, jump_to_def, update_var_def,
    lookup_var_def, FLOOKUP_DRESTRICT, op_prov_def, op_taint_def,
    set_var_taint_def, FLOOKUP_UPDATE] >> fs[lookup_var_def, op_taint_def]
QED

(* Increment instructions operate only on provenance-free scalar words. *)
Theorem membership_increment_check:
  (opc = ADD \/ opc = ASSIGN) /\
  (!a. MEM a ops ==> op_taint tn a = {} /\ op_prov G a = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def,
    source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF, update_var_def] >>
  metis_tac[]
QED

Theorem membership_increment_ghost:
  (opc = ADD /\ ops = [a;Lit off] \/ opc = ASSIGN /\ ops = [a]) /\
  op_prov G a = NONE /\ op_taint tn a = {} ==>
  step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >> gvs[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
    set_prov_def, mk_inst_def] >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
      EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, out_taint_def, mem_taint_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, range_bytes_def,
    taint_component_equality, DRESTRICT_UNIV, set_var_taint_def,
    mk_inst_def, op_taint_def] >>
  Cases_on `eval_operand a s` >> fs[op_taint_def]
QED

Theorem membership_increment_edge:
  (opc = ADD /\ ops = [a;Lit off] \/ opc = ASSIGN /\ ops = [a]) /\
  op_prov G a = NONE /\ op_taint tn a = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule membership_increment_check >>
     gvs[] >> rpt conj_tac >> rpt strip_tac >>
     gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `~is_terminator (mk_inst id opc ops [out]).inst_opcode /\
   (mk_inst id opc ops [out]).inst_opcode <> INVOKE` by
    (gvs[mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
      tn with t_var := tn.t_var |+ (out,{})` by
    (irule membership_increment_ghost >> metis_tac[]) >>
  simp[mk_inst_def] >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED

Theorem membership_increment_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var idx;Lit 1w] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) ASSIGN [Var tmp] [idx]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (id+2) JMP [Label cond] []) /\
  lookup_var idx s = SOME v /\ op_prov G (Var idx) = NONE /\
  op_taint tn (Var idx) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {idx}))
    (tn with t_var := tn.t_var |+ (tmp,{}) |+ (idx,{}))
    (OK (jump_to cond (update_var idx (v+1w) (update_var tmp (v+1w) s))))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var idx;Lit 1w] [tmp]) s =
    OK (update_var tmp (v+1w) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {tmp}))
    (tn with t_var := tn.t_var |+ (tmp,{}))
    (OK (update_var tmp (v+1w) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule membership_increment_edge >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `OK s1` >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {tmp}))
    (tn with t_var := tn.t_var |+ (tmp,{})) s1 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {idx}))
    (tn with t_var := tn.t_var |+ (tmp,{}) |+ (idx,{}))
    (OK (update_var idx (v+1w) s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    suspend "assign" >>
  qmatch_asmsub_abbrev_tac `OK s2` >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {idx}))
    (tn with t_var := tn.t_var |+ (tmp,{}) |+ (idx,{})) s2 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {idx}))
    (tn with t_var := tn.t_var |+ (tmp,{}) |+ (idx,{}))
    (OK (jump_to cond s2))` by
    (irule bodyPtrBopInLoopControlTheory.membership_jump_path >>
     simp[Abbr `s2`, Abbr `s1`, update_var_def] >> metis_tac[]) >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `s2`, Abbr `s1`, jump_to_def, update_var_def]
QED

Resume membership_increment_path[assign]:
  irule (SRULE [] (Q.INST [`tn` |-> `tn with t_var := tn.t_var |+ (tmp,{})`]
    membership_increment_edge)) >>
  simp[Abbr `s1`, update_var_def, op_prov_def, FLOOKUP_DRESTRICT,
    op_taint_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`Var tmp`, `id+1`] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    step_inst_base_opcode_eqs, mk_inst_def]
QED

Finalise membership_increment_path

Theorem membership_increment_frame:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME
    (mk_inst id ADD [Var ("%" ++ toString (sa.cs_next_var+1));Lit 1w] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) ASSIGN [Var tmp] ["%" ++ toString (sa.cs_next_var+1)]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (id+2) JMP [Label cond] []) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  (!x. not_fresh_at sa x ==> x <> tmp) /\
  tmp <> "%" ++ toString sa.cs_next_var ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa (SUC i) r G' tn' t /\
    t = jump_to cond (update_var ("%" ++ toString (sa.cs_next_var+1))
      (n2w (SUC i)) (update_var tmp (n2w (SUC i)) s))
Proof
  strip_tac >>
  `lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i) /\
   op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def] >>
  drule_all membership_increment_path >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD1, word_add_n2w] >> conj_tac
  >- suspend "frame" >>
  fs[membership_loop_registers_def, op_prov_def] >>
  simp[membership_loop_registers_def, jump_to_def, update_var_def,
    lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    op_prov_def, op_taint_def] >> fs[lookup_var_def, op_taint_def]
QED

Resume membership_increment_frame[frame]:
  fs[membership_loop_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `x <> tmp /\ x <> "%" ++ toString (sa.cs_next_var+1)` by
        (fs[compileEnvTheory.not_fresh_at_def] >> metis_tac[]) >>
      simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
        FLOOKUP_DRESTRICT, op_taint_def] >>
      fs[lookup_var_def, op_taint_def]) >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >>
  simp[jump_to_def, update_var_def]
QED

Finalise membership_increment_frame


Theorem membership_drop_pair_lookup:
  DROP pc bb.bb_instructions = [a;b] ==>
  get_instruction bb pc = SOME a /\
  get_instruction bb (SUC pc) = SOME b
Proof
  rewrite_tac[get_instruction_def] >>
  qspec_tac (`bb.bb_instructions`, `xs`) >> qid_spec_tac `pc` >>
  Induct >> Cases_on `xs` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem membership_eq_branch_control:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [a;b] [dst]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) JNZ [Var dst;Label lt;Label lf] []) /\
  eval_operand a s = SOME aw /\ eval_operand b s = SOME bw /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  (!x. not_fresh_at sa x ==> x <> dst) /\
  dst <> "%" ++ toString (sa.cs_next_var+1) /\
  dst <> "%" ++ toString sa.cs_next_var ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\ t.vs_current_bb = (if aw = bw then lt else lf)
Proof
  strip_tac >> drule_all membership_eq_branch_frame >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def]
QED

Theorem membership_compared_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  s.vs_inst_idx = 2+delta+width /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+delta+width))) s = SOME a /\
  op_prov G (Var ("%" ++ toString (sa.cs_next_var+4+delta+width))) = NONE /\
  op_taint tn (Var ("%" ++ toString (sa.cs_next_var+4+delta+width))) = {} /\
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
  strip_tac >> drule_all membership_compiled_compare_lookup >> strip_tac >>
  drule membership_drop_pair_lookup >> strip_tac >>
  `(!x. not_fresh_at sa x ==>
    x <> "%" ++ toString (sa.cs_next_var+5+delta+width))` by
    (simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `5+delta+width` mp_tac) >> simp[]) >>
  irule membership_eq_branch_control >> simp[] >>
  qexistsl_tac [`Var ("%" ++ toString (sa.cs_next_var+4+delta+width))`,
    `needle`, `"%" ++ toString (sa.cs_next_var+5+delta+width)`, 
    `sa.cs_next_id+8+delta+width`] >>
  gvs[] >> Cases_on `0 < skip` >>
  Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> gvs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem membership_condition_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
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
  strip_tac >> drule_all membership_condition_frame >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def]
QED

Theorem membership_found_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
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
  drule membership_compiled_found_lookup >>
  disch_then (qspecl_then
    [`if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1`,
     `fn`, `if 0 < skip then 1 else 0`] mp_tac) >>
  simp[] >> strip_tac >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i 1w G' tn' t /\
    t = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5))
      (update_var ("%" ++ toString sa.cs_next_var) 1w s)` by
    (irule membership_found_frame >> simp[get_instruction_def] >>
     conj_tac
     >- (qexists_tac `sa.cs_next_id+10+(if 0 < skip then 1 else 0)+
           (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)` >> simp[]) >>
     goal_assum (drule_at Any)) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def]
QED

Theorem membership_increment_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
  s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa (SUC i) r G' tn' t /\ ~t.vs_halted /\
    t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)
Proof
  strip_tac >> drule_all membership_compiled_increment_lookup >> strip_tac >>
  `(!x. not_fresh_at sa x ==>
    x <> "%" ++ toString (sa.cs_next_var+6+delta+width))` by
    (simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `6+delta+width` mp_tac) >> simp[]) >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa (SUC i) r G' tn' t /\
    t = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
      (update_var ("%" ++ toString (sa.cs_next_var+1)) (n2w (SUC i))
        (update_var ("%" ++ toString (sa.cs_next_var+6+delta+width))
          (n2w (SUC i)) s))` by
    (irule membership_increment_frame >> simp[get_instruction_def] >>
     conj_tac >- (gvs[] >> metis_tac[]) >>
     qexists_tac `sa.cs_next_id+12+delta+width` >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def]
QED

Theorem membership_iszero_control:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ISZERO [arg] [dst]) /\
  eval_operand arg s = SOME a /\ op_prov G arg = NONE /\ op_taint tn arg = {} ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand (Var dst) t = SOME (bool_to_word (a = 0w)) /\
    op_prov G' (Var dst) = NONE /\ op_taint tn' (Var dst) = {} /\
    tn' = tn with t_var := tn.t_var |+ (dst,{}) /\
    (!x. x <> dst ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t = (update_var dst (bool_to_word (a = 0w)) s
      with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule membership_iszero_step >>
  disch_then (qspecl_then [`dst`, `id`] assume_tac) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ISZERO [arg] [dst]) s` by
    (irule membership_scalar_check >> simp[] >>
     goal_assum (drule_at Any) >> simp[update_var_def]) >>
  `~is_terminator (mk_inst id ISZERO [arg] [dst]).inst_opcode /\
    (mk_inst id ISZERO [arg] [dst]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> simp[mk_inst_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1 (OK t)` >>
  `tn1 = tn with t_var := tn.t_var |+ (dst,{})` by
    (simp[Abbr `tn1`, GSYM mk_inst_def] >> irule membership_scalar_ghost_frame >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G1 tn1 (OK t)` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[Abbr `t`, update_var_def]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def,
    op_prov_def, op_taint_def, FLOOKUP_UPDATE] >>
  simp[Abbr `G1`, GSYM mk_inst_def] >> conj_tac
  >- (irule membership_scalar_provenance >> simp[]) >>
  rpt strip_tac >> simp[stmtAppendStorageRunPtrTheory.scalar_step_old_prov]
QED

Theorem membership_iszero_frame:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ISZERO [arg] [dst]) /\
  eval_operand arg s = SOME a /\ op_prov G arg = NONE /\ op_taint tn arg = {} /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. not_fresh_at sa x ==> x <> dst) ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    eval_operand (Var dst) t = SOME (bool_to_word (a = 0w)) /\
    op_prov G' (Var dst) = NONE /\ op_taint tn' (Var dst) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx
Proof
  strip_tac >> drule_all membership_iszero_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  reverse conj_tac >- gvs[update_var_def] >>
  fs[membership_loop_frame_def] >> reverse conj_tac
  >- (qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >>
      simp[update_var_def]) >>
  rpt strip_tac >> `x <> dst` by metis_tac[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[lookup_var_def]
QED

Theorem membership_notin_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) F sa = (op,sb) /\
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
  strip_tac >> drule_all membership_compiled_notin_exit_lookup >> strip_tac >>
  drule membership_compiled_loop_exit >> simp[] >> strip_tac >>
  `(!x. not_fresh_at sa x ==>
    x <> "%" ++ toString (sa.cs_next_var+7+delta+width))` by
    (simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `7+delta+width` mp_tac) >> simp[]) >>
  `?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+7+delta+width))) t =
      SOME (bool_to_word (r = 0w)) /\
    op_prov G' (Var ("%" ++ toString (sa.cs_next_var+7+delta+width))) = NONE /\
    op_taint tn' (Var ("%" ++ toString (sa.cs_next_var+7+delta+width))) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx` by
    (irule membership_iszero_frame >>
     fs[membership_loop_registers_def] >> simp[eval_operand_def] >>
     conj_tac >- gvs[] >>
     qexistsl_tac [`Var ("%" ++ toString sa.cs_next_var)`,
       `sa.cs_next_id+15+delta+width`] >>
     simp[get_instruction_def] >>
     Cases_on `bb.bb_instructions` >> gvs[eval_operand_def]) >>
  gvs[] >> qexistsl_tac [`G'`, `tn'`, `t`] >> simp[]
QED


(* Compile-first interfaces fix every compiler parameter before runtime matching. *)
Theorem membership_compared_control_forward:
  !needle arr len stride skip is_ctor imm loc is_in sa op sb.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) ==>
  !fn ctx s G0 tn0 s0 G tn i r a w D PG.
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) s = SOME a /\
  op_prov G (Var ("%" ++ toString (sa.cs_next_var+4+
    (if 0 < skip then 1 else 0)+
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
  op_taint tn (Var ("%" ++ toString (sa.cs_next_var+4+
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
  rpt strip_tac >> irule membership_compared_control >> simp[] >>
  goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ = _`)) >>
  gvs[]
QED

Theorem membership_increment_control_forward:
  !needle arr len stride skip is_ctor imm loc is_in sa op sb.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) ==>
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
  rpt strip_tac >> irule membership_increment_control >> simp[] >>
  goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ = _`)) >>
  gvs[]
QED

(* Exercises the normalized boundary at the actual callback endpoint. *)
Theorem membership_load_compare_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc ws G0 tn0 s0 /\
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
  qpat_x_assum `membership_load_contract _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [membership_load_contract_def]) >>
  disch_then (qspecl_then [`i`, `G`, `tn`, `s`] mp_tac) >> simp[] >> strip_tac >>
  `eval_operand needle t = SOME w /\ op_prov G' needle = NONE /\
    op_taint tn' needle = {}` by metis_tac[membership_loop_frame_operand] >>
  drule membership_compared_control_forward >>
  disch_then (drule_all o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []) >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`G''`, `tn''`, `t'`] >> simp[]
QED

Theorem membership_search_suffix:
  !i G tn s.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc ws G0 tn0 s0 /\
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
  drule_all membership_condition_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  Cases_on `i = LENGTH ws`
  >- (gvs[bool_to_word_def] >>
      qexistsl_tac [`G'`, `tn'`, `t`, `LENGTH ws`] >> simp[]) >>
  `(n2w i:bytes32) <> n2w (LENGTH ws)` by
    (`i < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  gvs[] >> `i < LENGTH ws` by decide_tac >>
  drule_all membership_load_compare_control >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `DROP i ws = EL i ws :: DROP (SUC i) ws` by
    metis_tac[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `EL i ws = w`
  >- suspend "found" >>
  gvs[] >> suspend "incr"
QED

Resume membership_search_suffix[found]:
  gvs[] >> drule_all membership_found_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `i` >> simp[]
QED

Resume membership_search_suffix[incr]:
  drule membership_increment_control_forward >> disch_then drule_all >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC i` mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `j` >> simp[]
QED

Finalise membership_search_suffix

Theorem membership_search_initialized:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc ws G tn s /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} /\
  eval_operand len s = SOME (n2w (LENGTH ws)) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\ LENGTH ws < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t j. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    membership_loop_registers sa j (bool_to_word (MEM w ws)) G' tn' t /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  strip_tac >> drule_all membership_loop_contract_init >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> strip_tac >>
  mp_tac (GEN_ALL (Q.SPEC `0` membership_search_suffix)) >>
  disch_then (drule_all o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `j` >> simp[]
QED

Theorem membership_finish_control:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
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
  strip_tac >> drule membership_compiled_loop_exit >> strip_tac >>
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
    (irule membership_notin_control >> simp[] >> conj_tac
     >- (goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
     qexists_tac `i` >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >> Cases_on `b` >> gvs[bool_to_word_def]
QED

Theorem membership_loop_conditional:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc ws G tn s /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} /\
  eval_operand len s = SOME (n2w (LENGTH ws)) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\ LENGTH ws < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all membership_search_initialized >> strip_tac >>
  drule_all membership_finish_control >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
