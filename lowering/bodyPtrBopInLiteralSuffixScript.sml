Theory bodyPtrBopInLiteralSuffix
Ancestors exprSimBopInLiteralWord
  bodyPtrBopInLiteralBoundary bodyPtrAttributeAdd stmtAppendStorageRunPtr
  decoderGhostFramePtr fragGasSeqPtr emitHelperProps ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState compileEnv loweringStateRelDefs codegenRel contextCodegenRel
  list finite_map words ghostPcTransportPtr instIdxIndep instSeqComposePtr
  bodyPtrBopInLiteralRun fragExec exprLoweringProps exprLowering
  exprSimWordBuiltins freshWrites arithmetic rich_list

(* The literal suffix uses only these non-memory scalar instructions.
   The concrete successful execution is kept explicit so this boundary works
   for unary ISZERO as well as the binary comparisons and combinations. *)
Theorem membership_scalar_check:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK s' /\
  s'.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  rpt strip_tac >> gvs[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def,
                        FLOOKUP_DEF] >> metis_tac[]
QED

Theorem membership_scalar_provenance:
  MEM opc [EQ; OR; AND; ISZERO; GT] ==>
  FLOOKUP (step_prov PG G (mk_inst id opc ops [out]) s') out = NONE
Proof
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT] >> rpt strip_tac >> gvs[FLOOKUP_DRESTRICT]
QED

Theorem membership_scalar_ghost_frame:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  (LENGTH ops = 1 \/ LENGTH ops = 2) ==>
  step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV] >>
  Cases_on `eval_operand h s` >> simp[]
QED

Theorem membership_scalar_path:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  (LENGTH ops = 1 \/ LENGTH ops = 2) /\
  emit_op opc ops sa = (dst,sb) /\ fn_has_code sa sb fn /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc ops [out]) s =
    OK (update_var out w s)) ==>
  ?out G' tn' t.
    dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    eval_operand dst t = SOME w /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn' = tn with t_var := tn.t_var |+ (out,{}) /\
    (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id opc ops
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s)`,
    `step_taint (mk_inst sa.cs_next_id opc ops
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn`,
    `update_var (STRING #"%" (toString sa.cs_next_var)) w s
       with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[IgnAsm `s.vs_inst_idx = _`] >>
  conj_tac
  >- (`~is_terminator opc /\ opc <> GAS /\ opc <> INVOKE` by
        (gvs[is_terminator_def]) >>
      irule attribute_emit_op_path_ptr >> simp[] >>
      gen_tac >> irule membership_scalar_check >>
      simp[update_var_def] >> metis_tac[]) >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def,
                   FLOOKUP_UPDATE] >>
  simp[op_prov_def] >>
  conj_tac >- (irule membership_scalar_provenance >> simp[]) >>
  `step_taint (mk_inst sa.cs_next_id opc ops
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn =
     tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{})` by
    (irule membership_scalar_ghost_frame >> simp[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE, scalar_step_old_prov]
QED

Theorem membership_binary_step:
  (opc = EQ /\ f = (\a b. bool_to_word (a = b)) \/
   opc = OR /\ f = word_or \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id opc [left;right] [out]) s =
    OK (update_var out (f a b) s)
Proof
  strip_tac >> gvs[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem membership_iszero_step:
  eval_operand arg s = SOME a ==>
  step_inst_base (mk_inst id ISZERO [arg] [out]) s =
    OK (update_var out (bool_to_word (a = 0w)) s)
Proof
  strip_tac >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def]
QED

Theorem membership_scalar_uniform:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  (LENGTH ops = 1 \/ LENGTH ops = 2) /\
  emit_op opc ops sa = (dst,sb) /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id opc ops
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s) ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
           (s with vs_inst_idx := k) G' tn') /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G tn [i]` >>
  qmatch_goalsub_abbrev_tac `op_prov _ (Var out)` >>
  `step_inst_base i s = OK (update_var out w s)` by simp[Abbr `i`, Abbr `out`] >>
  `step_taint i s (update_var out w s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (simp[Abbr `i`, Abbr `out`] >> irule membership_scalar_ghost_frame >> simp[]) >>
  `~is_terminator i.inst_opcode` by
    gvs[Abbr `i`, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`step_prov PG G i (update_var out w s)`,
                `step_taint i s (update_var out w s) tn`] >>
  conj_tac >-
    (gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
                    exec_result_map_def] >>
     simp[Abbr `i`, Abbr `out`] >> irule membership_scalar_check >>
     simp[step_inst_inst_idx_indep, exec_result_map_def, update_var_def] >>
     metis_tac[]) >>
  simp[op_prov_def] >> conj_tac >-
    (simp[Abbr `i`, Abbr `out`] >> irule membership_scalar_provenance >> simp[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `p <> out` by fs[Abbr `out`, not_fresh_at_def] >>
  simp[Abbr `i`, Abbr `out`, scalar_step_old_prov]
QED

Theorem membership_scalar_update:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  step_inst_base (mk_inst id opc ops [out]) s = OK t ==>
  ?w. t = update_var out w s
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  strip_tac >> gvs[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem membership_scalar_uniform_run:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  (LENGTH ops = 1 \/ LENGTH ops = 2) /\
  emit_op opc ops sa = (dst,sb) /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
           (s with vs_inst_idx := k) G' tn') /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_at (Pat `step_inst_base _ _ = _`) membership_scalar_update >>
  simp[] >> strip_tac >>
  qpat_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[GSYM th]) >>
  irule membership_scalar_uniform >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem membership_operand_ghost_frame:
  fresh_vars_wrt sa s /\ eval_operand x s = SOME v /\
  (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  op_prov G' x = op_prov G x /\ op_taint tn' x = op_taint tn x
Proof
  strip_tac >> Cases_on `x` >> simp[op_prov_def, op_taint_def] >>
  `not_fresh_at sa s'` by
    (irule fresh_vars_wrt_not_fresh_at >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum drule >> simp[op_prov_def, op_taint_def]
QED

Theorem membership_clean_operand_frame:
  fresh_vars_wrt sa s /\ eval_operand x s = SOME v /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  op_prov G' x = NONE /\ op_taint tn' x = {}
Proof
  strip_tac >> drule_all membership_operand_ghost_frame >> simp[]
QED

Theorem membership_scalar_nonterminators:
  !is. EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) is ==>
       EVERY (\i. ~is_terminator i.inst_opcode) is
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem membership_shape_nonterminators[local]:
  !is. EVERY (\i. (i.inst_opcode = EQ \/ i.inst_opcode = OR \/
                   i.inst_opcode = AND \/ i.inst_opcode = ISZERO) /\
         (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
         LENGTH i.inst_outputs = 1) is ==>
       EVERY (\i. ~is_terminator i.inst_opcode) is
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem membership_defined_from_rel[local]:
  !s cs vs. LIST_REL (\c v. eval_operand c s = SOME v) cs vs ==>
    EVERY (\c. ?v. eval_operand c s = SOME v) cs
Proof
  gen_tac >> Induct >> rpt strip_tac >> gvs[LIST_REL_CONS1] >> metis_tac[]
QED

Theorem membership_defined_from_bool_rel[local]:
  !s cs bs. LIST_REL (\c b. eval_operand c s = SOME (bool_to_word b)) cs bs ==>
    EVERY (\c. ?v. eval_operand c s = SOME v) cs
Proof
  gen_tac >> Induct >> rpt strip_tac >> gvs[LIST_REL_CONS1] >> metis_tac[]
QED

Theorem membership_clean_spec[local]:
  !sa s x v G tn G' tn'.
    fresh_vars_wrt sa s /\ eval_operand x s = SOME v /\
    op_prov G x = NONE /\ op_taint tn x = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) ==>
    op_prov G' x = NONE /\ op_taint tn' x = {}
Proof
  rpt gen_tac >> strip_tac >>
  drule_all membership_clean_operand_frame >> simp[]
QED

Theorem membership_clean_list_frame[local]:
  !sa s G tn G' tn' xs.
    fresh_vars_wrt sa s /\ EVERY (\x. ?v. eval_operand x s = SOME v) xs /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) ==>
    EVERY (\x. op_prov G' x = NONE /\ op_taint tn' x = {}) xs
Proof
  ntac 6 gen_tac >> Induct >> simp[] >> rpt strip_tac
  >- (drule_all membership_clean_operand_frame >> simp[])
  >- (drule_all membership_clean_operand_frame >> simp[]) >>
  first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem membership_defined_mono[local]:
  !s t xs.
    EVERY (\x. ?v. eval_operand x s = SOME v) xs /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
    EVERY (\x. ?v. eval_operand x t = SOME v) xs
Proof
  rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem membership_op_uniform[local]:
  !D ctx fn PG opc ops sa dst sb s t G tn.
    emit_op opc ops sa = (dst,sb) /\ MEM opc [EQ; OR; AND; ISZERO; GT] /\
    (LENGTH ops = 1 \/ LENGTH ops = 2) /\
    EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) ops /\
    ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) G' tn') /\
      op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
      (tn' with t_var := tn.t_var) = tn /\
      (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `EVERY _ _` (assume_tac o SRULE [EVERY_MEM]) >>
  irule membership_scalar_uniform_run >> metis_tac[]
QED

Theorem membership_op_facts[local]:
  !opc ops sa dst sb.
    emit_op opc ops sa = (dst,sb) /\ MEM opc [EQ; OR; AND; ISZERO] ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule emit_op_extends >> drule emitted_insts_emit_op >> rpt strip_tac >>
  gvs[mk_inst_def, is_terminator_def]
QED

(* Composition of two uniform pointer segments of straight scalar code. *)
Theorem membership_uniform_trans[local]:
  !D ctx fn PG G tn G1 tn1 G2 tn2 sa sm sb s t.
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
    run_inst_seq (emitted_insts sa sm) s = OK t /\
    sa.cs_next_var <= sm.cs_next_var /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
       (s with vs_inst_idx := k) G1 tn1) /\
    (tn1 with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G1 p = FLOOKUP G p /\
       op_taint tn1 (Var p) = op_taint tn (Var p)) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sm sb)
       (t with vs_inst_idx := k) G2 tn2) /\
    (tn2 with t_var := tn1.t_var) = tn1 /\
    (!p. not_fresh_at sm p ==> FLOOKUP G2 p = FLOOKUP G1 p /\
       op_taint tn2 (Var p) = op_taint tn1 (Var p)) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := k) G2 tn2) /\
    (tn2 with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G2 p = FLOOKUP G p /\
       op_taint tn2 (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (pop_assum SUBST1_TAC >> irule inst_seq_ptr_uniform_append >>
      metis_tac[]) >>
  conj_tac >- gvs[taint_component_equality] >>
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sm p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem literal_eqs_next_var[local]:
  !xs needle sa cs sb.
    emit_membership_eqs needle xs sa = (cs,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  Induct >> rpt gen_tac
  >- simp[emit_membership_eqs_def, comp_return_def] >>
  simp[emit_membership_eqs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem literal_or_next_var[local]:
  !cs acc sa op sb.
    fold_membership_or acc cs sa = (op,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  Induct >> rpt gen_tac
  >- simp[fold_membership_or_def, comp_return_def] >>
  simp[fold_membership_or_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem literal_and_next_var[local]:
  !cs acc sa op sb.
    fold_membership_and acc cs sa = (op,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  Induct >> rpt gen_tac
  >- simp[fold_membership_and_def, comp_return_def] >>
  simp[fold_membership_and_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem literal_in_next_var:
  !xs needle sa dst sb.
    compile_list_membership_in needle xs sa = (dst,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> simp[compile_list_membership_in_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_membership_eqs needle xs sa = (cs, sm)` >>
  drule literal_eqs_next_var >> strip_tac >>
  Cases_on `cs` >> gvs[comp_return_def] >>
  drule literal_or_next_var >> strip_tac >> decide_tac
QED

(* The equalities read only clean operands and produce clean results. *)
Theorem literal_eqs_uniform[local]:
  !D ctx fn PG xs ws needle w sa cs sb s G tn.
    emit_membership_eqs needle xs sa = (cs,sb) /\
    LIST_REL (\x v. eval_operand x s = SOME v) xs ws /\
    eval_operand needle s = SOME w /\ fresh_vars_wrt sa s /\
    op_prov G needle = NONE /\ op_taint tn needle = {} /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) G' tn') /\
      EVERY (\c. op_prov G' c = NONE /\ op_taint tn' c = {}) cs /\
      (tn' with t_var := tn.t_var) = tn /\
      (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  ntac 4 gen_tac >> Induct >> rpt gen_tac
  >- (simp[emit_membership_eqs_def, comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_refl] >> qexistsl_tac [`G`, `tn`] >>
      simp[inst_seq_ptr_def]) >>
  Cases_on `ws` >> simp[emit_membership_eqs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op EQ _ sa = (c,s1)` >>
  rename1 `emit_membership_eqs needle xs s1 = (cs1,sb)` >>
  rename1 `eval_operand h s = SOME hv` >>
  mp_tac (Q.SPECL [`needle`, `h`, `w`, `hv`, `sa`, `c`, `s1`, `s`]
    emit_op_EQ_correct) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s1) s = OK ss1` >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `EQ`, `[needle; h]`, `sa`, `c`,
    `s1`, `s`, `ss1`, `G`, `tn`] membership_op_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G1`, `tn1`] strip_assume_tac) >>
  `op_prov G1 needle = NONE /\ op_taint tn1 needle = {}` by
    (mp_tac (Q.SPECL [`sa`, `s`, `needle`, `w`, `G`, `tn`, `G1`, `tn1`] membership_clean_spec) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  rename1 `LIST_REL _ xs ts` >>
  `EVERY (\x. ?v. eval_operand x s = SOME v) xs` by
    (irule membership_defined_from_rel >> first_assum (irule_at Any)) >>
  `EVERY (\x. op_prov G1 x = NONE /\ op_taint tn1 x = {}) xs` by
    (mp_tac (Q.SPECL [`sa`, `s`, `G`, `tn`, `G1`, `tn1`, `xs`] membership_clean_list_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `LIST_REL (\x v. eval_operand x ss1 = SOME v) xs ts` by
    (irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand needle ss1 = SOME w` by
    (qpat_x_assum `!op w. eval_operand op s = SOME w ==> _` drule >> simp[]) >>
  first_x_assum (qspecl_then [`ts`, `needle`, `w`, `s1`, `cs1`, `sb`, `ss1`,
    `G1`, `tn1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G2`, `tn2`] strip_assume_tac) >>
  `op_prov G2 c = NONE /\ op_taint tn2 c = {}` by
    (mp_tac (Q.SPECL [`s1`, `ss1`, `c`, `bool_to_word ((w:256 word) = hv)`, `G1`, `tn1`, `G2`, `tn2`] membership_clean_spec) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  mp_tac (Q.SPECL [`EQ`, `[needle; h]`, `sa`, `c`, `s1`] membership_op_facts) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule literal_eqs_shape >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G`, `tn`, `G1`, `tn1`, `G2`, `tn2`,
    `sa`, `s1`, `sb`, `s`, `ss1`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`] >> simp[]
QED

Theorem literal_or_uniform[local]:
  !D ctx fn PG cs acc sa op sb s G tn.
    fold_membership_or acc cs sa = (op,sb) /\
    EVERY (\c. ?v. eval_operand c s = SOME v) cs /\
    (?a. eval_operand acc s = SOME a) /\ fresh_vars_wrt sa s /\
    op_prov G acc = NONE /\ op_taint tn acc = {} /\
    EVERY (\c. op_prov G c = NONE /\ op_taint tn c = {}) cs /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) G' tn') /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      (tn' with t_var := tn.t_var) = tn /\
      (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  ntac 4 gen_tac >> Induct >> rpt gen_tac
  >- (simp[fold_membership_or_def, comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_refl] >> qexistsl_tac [`G`, `tn`] >>
      simp[inst_seq_ptr_def]) >>
  simp[fold_membership_or_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op OR _ sa = (r,s1)` >>
  rename1 `eval_operand h s = SOME hv` >>
  mp_tac (Q.SPECL [`acc`, `h`, `a`, `hv`, `sa`, `r`, `s1`, `s`]
    emit_op_OR_correct) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s1) s = OK ss1` >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `OR`, `[acc; h]`, `sa`, `r`,
    `s1`, `s`, `ss1`, `G`, `tn`] membership_op_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G1`, `tn1`] strip_assume_tac) >>
  `EVERY (\x. op_prov G1 x = NONE /\ op_taint tn1 x = {}) cs` by
    (mp_tac (Q.SPECL [`sa`, `s`, `G`, `tn`, `G1`, `tn1`, `cs`] membership_clean_list_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `EVERY (\c. ?v. eval_operand c ss1 = SOME v) cs` by
    (mp_tac (Q.SPECL [`s`, `ss1`, `cs`] membership_defined_mono) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  first_x_assum (qspecl_then [`r`, `s1`, `op`, `sb`, `ss1`, `G1`, `tn1`]
    mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G2`, `tn2`] strip_assume_tac) >>
  mp_tac (Q.SPECL [`OR`, `[acc; h]`, `sa`, `r`, `s1`] membership_op_facts) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule literal_or_shape >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G`, `tn`, `G1`, `tn1`, `G2`, `tn2`,
    `sa`, `s1`, `sb`, `s`, `ss1`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem literal_and_uniform[local]:
  !D ctx fn PG cs acc sa op sb s G tn.
    fold_membership_and acc cs sa = (op,sb) /\
    EVERY (\c. ?v. eval_operand c s = SOME v) cs /\
    (?a. eval_operand acc s = SOME a) /\ fresh_vars_wrt sa s /\
    op_prov G acc = NONE /\ op_taint tn acc = {} /\
    EVERY (\c. op_prov G c = NONE /\ op_taint tn c = {}) cs /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) G' tn') /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      (tn' with t_var := tn.t_var) = tn /\
      (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  ntac 4 gen_tac >> Induct >> rpt gen_tac
  >- (simp[fold_membership_and_def, comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_refl] >> qexistsl_tac [`G`, `tn`] >>
      simp[inst_seq_ptr_def]) >>
  simp[fold_membership_and_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ISZERO _ sa = (z,s1)` >>
  rename1 `emit_op AND _ s1 = (r,s2)` >>
  rename1 `eval_operand h s = SOME hv` >>
  mp_tac (Q.SPECL [`h`, `hv`, `sa`, `z`, `s1`, `s`]
    emit_op_ISZERO_correct) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s1) s = OK ss1` >>
  `eval_operand acc ss1 = SOME a` by
    (qpat_x_assum `!op w. eval_operand op s = SOME w ==> _` drule >> simp[]) >>
  mp_tac (Q.SPECL [`acc`, `z`, `a`, `bool_to_word ((hv:256 word) = 0w)`, `s1`, `r`,
    `s2`, `ss1`] emit_op_AND_correct) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts s1 s2) ss1 = OK ss2` >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `ISZERO`, `[h]`, `sa`, `z`,
    `s1`, `s`, `ss1`, `G`, `tn`] membership_op_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G1`, `tn1`] strip_assume_tac) >>
  `op_prov G1 acc = NONE /\ op_taint tn1 acc = {}` by
    (mp_tac (Q.SPECL [`sa`, `s`, `acc`, `a`, `G`, `tn`, `G1`, `tn1`] membership_clean_spec) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `AND`, `[acc; z]`, `s1`, `r`,
    `s2`, `ss1`, `ss2`, `G1`, `tn1`] membership_op_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G2`, `tn2`] strip_assume_tac) >>
  `EVERY (\x. op_prov G1 x = NONE /\ op_taint tn1 x = {}) cs` by
    (mp_tac (Q.SPECL [`sa`, `s`, `G`, `tn`, `G1`, `tn1`, `cs`] membership_clean_list_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `EVERY (\c. ?v. eval_operand c ss1 = SOME v) cs` by
    (mp_tac (Q.SPECL [`s`, `ss1`, `cs`] membership_defined_mono) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `EVERY (\x. op_prov G2 x = NONE /\ op_taint tn2 x = {}) cs` by
    (mp_tac (Q.SPECL [`s1`, `ss1`, `G1`, `tn1`, `G2`, `tn2`, `cs`] membership_clean_list_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `EVERY (\c. ?v. eval_operand c ss2 = SOME v) cs` by
    (mp_tac (Q.SPECL [`ss1`, `ss2`, `cs`] membership_defined_mono) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  first_x_assum (qspecl_then [`r`, `s2`, `op`, `sb`, `ss2`, `G2`, `tn2`]
    mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G3`, `tn3`] strip_assume_tac) >>
  mp_tac (Q.SPECL [`ISZERO`, `[h]`, `sa`, `z`, `s1`] membership_op_facts) >>
  (impl_tac >- simp[]) >> strip_tac >>
  mp_tac (Q.SPECL [`AND`, `[acc; z]`, `s1`, `r`, `s2`] membership_op_facts) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule literal_and_shape >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G1`, `tn1`, `G2`, `tn2`, `G3`, `tn3`,
    `s1`, `s2`, `sb`, `ss1`, `ss2`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G`, `tn`, `G1`, `tn1`, `G3`, `tn3`,
    `sa`, `s1`, `sb`, `s`, `ss1`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`G3`, `tn3`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem literal_in_uniform:
  !xs ws needle w sa dst sb s G tn.
    compile_list_membership_in needle xs sa = (dst,sb) /\
    LIST_REL (\x v. eval_operand x s = SOME v) xs ws /\
    eval_operand needle s = SOME w /\ fresh_vars_wrt sa s /\
    op_prov G needle = NONE /\ op_taint tn needle = {} /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) G' tn') /\
      op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
      (tn' with t_var := tn.t_var) = tn /\
      (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> simp[compile_list_membership_in_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_membership_eqs needle xs sa = (cs, sm)` >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `xs`, `ws`, `needle`, `w`, `sa`,
    `cs`, `sm`, `s`, `G`, `tn`] literal_eqs_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G1`, `tn1`] strip_assume_tac) >>
  Cases_on `cs` >> gvs[comp_return_def]
  >- (qexistsl_tac [`G1`, `tn1`] >> simp[op_prov_def, op_taint_def]) >>
  rename1 `fold_membership_or c rest sm = (dst,sb)` >>
  drule_all literal_eqs_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK tt` >>
  `EVERY (\x. ?v. eval_operand x tt = SOME v) (c::rest)` by
    (irule membership_defined_from_bool_rel >> first_assum (irule_at Any)) >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `rest`, `c`, `sm`, `dst`, `sb`,
    `tt`, `G1`, `tn1`] literal_or_uniform) >>
  (impl_tac >- fs[]) >>
  disch_then (qx_choosel_then [`G2`, `tn2`] strip_assume_tac) >>
  drule literal_eqs_shape >> strip_tac >>
  drule membership_shape_nonterminators >> strip_tac >>
  drule literal_or_shape >> strip_tac >>
  drule literal_eqs_next_var >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G`, `tn`, `G1`, `tn1`, `G2`, `tn2`,
    `sa`, `sm`, `sb`, `s`, `tt`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem literal_notin_next_var:
  !xs needle sa dst sb.
    compile_list_membership_notin needle xs sa = (dst,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> simp[compile_list_membership_notin_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_membership_eqs needle xs sa = (cs, sm)` >>
  drule literal_eqs_next_var >> strip_tac >>
  Cases_on `cs` >> gvs[comp_return_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac literal_and_next_var >>
  gvs[]
QED


Theorem membership_neq_uniform:
  emit_op EQ [needle;x] sa = (eq_res,sm) /\
  emit_op ISZERO [eq_res] sm = (dst,sb) /\
  run_inst_seq (emitted_insts sa sm) s = OK s1 /\
  run_inst_seq (emitted_insts sm sb) s1 = OK s2 /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?G1 tn1.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
      (s with vs_inst_idx := k) G1 tn1) /\
    op_prov G1 eq_res = NONE /\ op_taint tn1 eq_res = {} /\
    (tn1 with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G1 p = FLOOKUP G p /\
      op_taint tn1 (Var p) = op_taint tn (Var p))` by
    (irule membership_scalar_uniform_run >> goal_assum (drule_at Any) >>
     conj_tac >- (goal_assum (drule_at Any)) >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[]) >>
  `?G2 tn2.
    (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sm sb)
      (s1 with vs_inst_idx := k) G2 tn2) /\
    op_prov G2 dst = NONE /\ op_taint tn2 dst = {} /\
    (tn2 with t_var := tn1.t_var) = tn1 /\
    (!p. not_fresh_at sm p ==> FLOOKUP G2 p = FLOOKUP G1 p /\
      op_taint tn2 (Var p) = op_taint tn1 (Var p))` by
    (irule membership_scalar_uniform_run >> goal_assum (drule_at Any) >>
     conj_tac >- (goal_assum (drule_at Any)) >>
     goal_assum (drule_at Any) >> simp[]) >>
  suspend "append"
QED

Resume membership_neq_uniform[append]:
  imp_res_tac emit_op_extends >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`] >> simp[] >> conj_tac
  >- (irule inst_seq_ptr_uniform_append >> conj_tac
      >- (qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
      imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  conj_tac >- gvs[taint_component_equality] >>
  imp_res_tac emitted_insts_emit_op >> rpt strip_tac >>
  `not_fresh_at sm p` by (gvs[not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Finalise membership_neq_uniform

Theorem literal_notin_uniform:
  !xs ws needle w sa dst sb s G tn.
    compile_list_membership_notin needle xs sa = (dst,sb) /\
    LIST_REL (\x v. eval_operand x s = SOME v) xs ws /\
    eval_operand needle s = SOME w /\ fresh_vars_wrt sa s /\
    op_prov G needle = NONE /\ op_taint tn needle = {} /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) G' tn') /\
      op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
      (tn' with t_var := tn.t_var) = tn /\
      (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> simp[compile_list_membership_notin_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_membership_eqs needle xs sa = (cs, sm)` >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `xs`, `ws`, `needle`, `w`, `sa`,
    `cs`, `sm`, `s`, `G`, `tn`] literal_eqs_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G1`, `tn1`] strip_assume_tac) >>
  Cases_on `cs` >> gvs[comp_return_def, comp_bind_def]
  >- (qexistsl_tac [`G1`, `tn1`] >> simp[op_prov_def, op_taint_def]) >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ISZERO [c] sm = (z,s1)` >>
  rename1 `fold_membership_and z rest s1 = (dst,sb)` >>
  drule_all literal_eqs_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK tt` >>
  `EVERY (\x. ?v. eval_operand x tt = SOME v) (c::rest)` by
    (irule membership_defined_from_bool_rel >> first_assum (irule_at Any)) >>
  qpat_x_assum `EVERY _ (c::rest)` (strip_assume_tac o SRULE []) >>
  rename1 `eval_operand c tt = SOME cv` >>
  mp_tac (Q.SPECL [`c`, `cv`, `sm`, `z`, `s1`, `tt`]
    emit_op_ISZERO_correct) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm s1) tt = OK ss1` >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `ISZERO`, `[c]`, `sm`, `z`,
    `s1`, `tt`, `ss1`, `G1`, `tn1`] membership_op_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G2`, `tn2`] strip_assume_tac) >>
  `EVERY (\x. op_prov G2 x = NONE /\ op_taint tn2 x = {}) rest` by
    (mp_tac (Q.SPECL [`sm`, `tt`, `G1`, `tn1`, `G2`, `tn2`, `rest`] membership_clean_list_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `EVERY (\x. ?v. eval_operand x ss1 = SOME v) rest` by
    (mp_tac (Q.SPECL [`tt`, `ss1`, `rest`] membership_defined_mono) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `rest`, `z`, `s1`, `dst`, `sb`,
    `ss1`, `G2`, `tn2`] literal_and_uniform) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G3`, `tn3`] strip_assume_tac) >>
  drule literal_eqs_shape >> strip_tac >>
  drule membership_shape_nonterminators >> strip_tac >>
  drule literal_eqs_next_var >> strip_tac >>
  mp_tac (Q.SPECL [`ISZERO`, `[c]`, `sm`, `z`, `s1`] membership_op_facts) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule literal_and_shape >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G1`, `tn1`, `G2`, `tn2`, `G3`, `tn3`,
    `sm`, `s1`, `sb`, `tt`, `ss1`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `ctx`, `fn`, `PG`, `G`, `tn`, `G1`, `tn1`, `G3`, `tn3`,
    `sa`, `sm`, `sb`, `s`, `tt`] membership_uniform_trans) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`G3`, `tn3`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem membership_scalar_run_path:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) (emitted_insts sa sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) G' tn') /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  (u with vs_vars := s.vs_vars) = s /\
  (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM] >>
     rpt strip_tac >> res_tac >> gvs[]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> strip_tac >>
  drule_all membership_scalar_run_frame >> strip_tac >> simp[] >>
  gvs[venom_state_component_equality, same_blocks_def]
QED

Theorem literal_in_path:
  compile_list_membership_in needle xs sa = (dst,sb) /\
  LIST_REL (\x v. eval_operand x s = SOME v) xs ws /\
  eval_operand needle s = SOME w /\ fresh_vars_wrt sa s /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (u with vs_vars := s.vs_vars) = s /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst t = SOME (bool_to_word (MEM w ws)) /\
    fresh_vars_wrt sb t /\ op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!x v. eval_operand x s = SOME v ==> eval_operand x t = SOME v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_in_run >> strip_tac >>
  drule_all literal_in_uniform >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule literal_in_code >> strip_tac >>
  drule_all membership_scalar_run_path >> strip_tac >>
  qexistsl_tac [`tt`, `tt with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  simp[eval_op_inst_idx, fresh_vars_wrt_def] >> gvs[fresh_vars_wrt_def]
QED

Theorem literal_notin_path:
  compile_list_membership_notin needle xs sa = (dst,sb) /\
  LIST_REL (\x v. eval_operand x s = SOME v) xs ws /\
  eval_operand needle s = SOME w /\ fresh_vars_wrt sa s /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (u with vs_vars := s.vs_vars) = s /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst t = SOME (bool_to_word (~MEM w ws)) /\
    fresh_vars_wrt sb t /\ op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!x v. eval_operand x s = SOME v ==> eval_operand x t = SOME v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_notin_run >> strip_tac >>
  drule_all literal_notin_uniform >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule literal_notin_code >> strip_tac >>
  drule_all membership_scalar_run_path >> strip_tac >>
  qexistsl_tac [`tt`, `tt with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  simp[eval_op_inst_idx, fresh_vars_wrt_def] >> gvs[fresh_vars_wrt_def]
QED
