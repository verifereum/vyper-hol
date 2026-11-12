(* Runtime immutable loads: DLOAD has no memory/slot taint dependency. *)
Theory bodyPtrBopInCodeLoad
Ancestors bodyPtrBopInElementLoad bodyPtrBopInSlotLoad bodyPtrBopInCodeContents
  bodyPtrBopInLoopContract bodyPtrBopInBaseBoundary
  exprSimUnwrap exprSimProps
  venomExecSemantics venomInst venomState ptrSafeRun ptrDiscipline
  fragGasSeqPtr fragGasPathPtr stmtAppendStorageRunPtr finite_map arithmetic
  codegenRel contextCodegenRel

Theorem membership_positioned_dload_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id DLOAD [arr_op] [out]) /\
  eval_operand arr_op s = SOME w /\ op_taint tn arr_op = {} /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) ==>
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out value s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id DLOAD [arr_op] [out]) s =
    OK (update_var out value s)` by
    (irule (cj 1 membership_code_header_operand_step) >> simp[] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id DLOAD [arr_op] [out]) s` by
    (irule (cj 2 membership_code_header_operand_step) >> simp[] >> metis_tac[]) >>
  `~is_terminator (mk_inst id DLOAD [arr_op] [out]).inst_opcode /\
   (mk_inst id DLOAD [arr_op] [out]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  `step_taint (mk_inst id DLOAD [arr_op] [out]) s
     (update_var out value s) tn = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      update_var_def, mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      new_site_bytes_def, FLOOKUP_DEF, range_bytes_def,
      taint_component_equality, DRESTRICT_UNIV, pred_setTheory.EXTENSION,
      SF CONJ_ss, eval_operand_def]) >>
  qexists_tac `step_prov PG G (mk_inst id DLOAD [arr_op] [out]) (update_var out value s)` >>
  simp[bodyPtrBopInLoadOutputTheory.scalar_load_output_prov, scalar_step_old_prov] >>
  gvs[mk_inst_def] >> drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> simp[update_var_def, cj 1 gas_path_ptr_rules]
QED

Theorem membership_code_load_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocCode) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 2+delta /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst value s with vs_inst_idx := 3+delta) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+8+delta) DLOAD [Var src] [dst])` by gvs[] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_dload_path >>
  gvs[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  qexists_tac `tn with t_var := tn.t_var |+
    ("%" ++ toString (sa.cs_next_var+5+(if 0 < skip then 1 else 0)),{})` >>
  fs[ADD1, op_taint_def, FLOOKUP_UPDATE] >> reverse conj_tac
  >- (irule membership_registers_scalar_update >> simp[] >>
      qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]) >>
  irule membership_frame_scalar_update >>
  conj_tac >- simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem membership_frame_data_section:
  membership_loop_frame sa G0 tn0 s0 G tn s ==>
  s.vs_data_section = s0.vs_data_section
Proof
  simp[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> strip_tac >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem membership_code_array_read:
  stmt_state_rel ctx fn cenv cx es s0 /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ety bd) (Value (ArrayV av)) bw es s0 /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
  membership_loop_frame sa G0 tn0 s0 G tn t ==>
  word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n (bw+n2w (prefix+32*i)))
      t.vs_data_section ++ REPLICATE 32 0w)) = typed_val_to_w256 tv v
Proof
  strip_tac >> drule_all membership_array_immutable_dload >> strip_tac >>
  drule membership_frame_data_section >> strip_tac >>
  full_simp_tac bool_ss [arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM]
QED

Theorem membership_code_array_element_prefix:
  compile_array_membership_loop needle arr_op len 32 prefix
    (compile_ptr_load F imm LocCode) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ety bd) (Value (ArrayV av)) bw es s0 /\
  eval_operand arr_op s0 = SOME bw /\ op_taint tn0 arr_op = {} /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule (SRULE [] (GEN_ALL membership_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)
    (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_code_array_read)) >>
  disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_code_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED

Theorem membership_code_array_element_prefix_source:
  compile_array_membership_loop needle arr_op len 32 prefix
    (compile_ptr_load F imm LocCode) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
  membership_loop_frame sa Gh tnh sh G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ (!x. arr_op = Var x ==> not_fresh_at early x) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ety bd) (Value (ArrayV av)) bw es s0 /\
  eval_operand arr_op s0 = SOME bw /\ op_taint tn0 arr_op = {} /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa Gh tnh sh G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `(!x. arr_op = Var x ==> not_fresh_at sa x)` by metis_tac[] >>
  `eval_operand arr_op sh = SOME bw /\ op_taint tnh arr_op = {}` by
    (qpat_assum `membership_loop_frame early G0 tn0 s0 Gh tnh sh`
       (mp_then Any mp_tac membership_loop_frame_operand) >>
     disch_then (qspec_then `arr_op` mp_tac) >> simp[]) >>
  drule (SRULE [] (GEN_ALL membership_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  `membership_loop_frame early G0 tn0 s0 G1 tn1 q` by
    metis_tac[membership_loop_frame_source] >>
  qpat_assum `membership_loop_frame early G0 tn0 s0 G1 tn1 q`
    (mp_then (Pat `membership_loop_frame _ _ _ _ _ _ _`) mp_tac
      (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_code_array_read))) >>
  disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_code_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame sa Gh tnh sh G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa Gh tnh sh G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED
