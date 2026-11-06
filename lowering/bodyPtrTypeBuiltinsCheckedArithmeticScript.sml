Theory bodyPtrTypeBuiltinsCheckedArithmetic
Ancestors
  bodyPtrTypeBuiltinsScalarCompose bodyPtrTypeBuiltinsScalarChecks
  bodyPtrTypeBuiltinsScalarArithmetic
  bodyPtrTypeBuiltinsClamp bodyPtrTypeBuiltinsScalarOps exprLowering exprLoweringProps
  compileEnv emitHelperProps ASCIInumbers rich_list
  fragGasSeqPtr instSeqComposePtr fragExec instIdxIndep exprSendPtr
  venomExecSemantics venomState venomInst ptrDiscipline finite_map list arithmetic

Theorem scalar_signed_byte_prefix_runs:
  (run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = OK t \/
   run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = Abort err t) ==>
  ?u v. run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a]] s = OK u /\
    run_inst_seq [mk_inst (id+1) EQ [x;Var a] [b]] u = OK v /\
    (?value. eval_operand (Var b) v = SOME value)
Proof
  simp[run_inst_seq_def, AllCaseEqs(), convert_scalar_no_abort] >> strip_tac >> (
  qpat_assum `step_inst_base (mk_inst _ EQ _ _) _ = OK _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[])
QED

Theorem scalar_signed_byte_pure_certificate:
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a]] s = OK u /\
  run_inst_seq [mk_inst (id+1) EQ [x;Var a] [b]] u = OK v ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b]]
      (s with vs_inst_idx := k) H th) /\
    op_prov H (Var b) = NONE /\ op_taint th (Var b) = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `MEM SIGNEXTEND [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
   op_prov G (Lit w) = NONE /\ op_taint tn (Lit w) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all scalar_clean_frame_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qpat_x_assum `MEM _ _` kall_tac >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by metis_tac[] >>
  `MEM EQ [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_clean_frame_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> conj_tac
  >- (irule (PURE_REWRITE_RULE [APPEND] (Q.INST
        [`xs` |-> `[mk_inst id SIGNEXTEND [Lit w;x] [a]]`]
        (Q.INST [`lo` |-> `0:num`] (SPEC_ALL inst_seq_ptr_uniform_append)))) >>
      simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`G1`,`tn1`] >> simp[GSYM mk_inst_def]) >>
  simp[] >> metis_tac[]
QED

Theorem scalar_signed_byte_certificate:
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = OK t \/
   run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b];
       mk_inst (id+2) ASSERT [Var b] []] s H th /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule scalar_signed_byte_prefix_runs >> strip_tac >>
  drule_all scalar_signed_byte_pure_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> reverse conj_tac >- simp[] >>
  irule (GEN_ALL (PURE_REWRITE_RULE [APPEND] (Q.INST
    [`xs` |-> `[mk_inst id SIGNEXTEND [Lit w;x] [a];
               mk_inst (id+1) EQ [x;Var a] [b]]`]
    (Q.INST [`id` |-> `id+2`, `w` |-> `value`]
      (SPEC_ALL checked_prefix_assert_certificate))))) >>
  simp[mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`v`,`value`] >> simp[GSYM mk_inst_def] >>
  qpat_x_assum `run_inst_seq [mk_inst id SIGNEXTEND _ _] s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst (id+1) EQ [x;Var a] [b]]` mp_tac) >> simp[]
QED

Theorem scalar_signed_byte_runtime_frame:
  run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. p <> a /\ p <> b ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_assum `step_inst_base (mk_inst id SIGNEXTEND _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `r` SUBST_ALL_TAC) >>
  qpat_assum `step_inst_base (mk_inst (id+1) EQ _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `z` SUBST_ALL_TAC) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem scalar_signed_byte_instruction_filter:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] /\
  FILTER (\i. i.inst_opcode = GAS)
    [mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] = []
Proof
  simp[mk_inst_def, is_terminator_def]
QED

Theorem scalar_signed_byte_uniform_certificate:
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = OK t \/
   run_inst_seq [mk_inst id SIGNEXTEND [Lit w;x] [a];
     mk_inst (id+1) EQ [x;Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = Abort err t) ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b];
       mk_inst (id+2) ASSERT [Var b] []] (s with vs_inst_idx := k) H th) /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule scalar_signed_byte_prefix_runs >> strip_tac >>
  drule_all scalar_signed_byte_pure_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> reverse conj_tac >- simp[] >>
  irule (PURE_REWRITE_RULE [APPEND] (Q.INST
    [`xs` |-> `[mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b]]`]
    (Q.INST [`lo` |-> `0:num`] (SPEC_ALL inst_seq_ptr_uniform_append)))) >>
  simp[mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`H`,`v`,`th`] >> simp[GSYM mk_inst_def] >> conj_tac
  >- (gen_tac >> irule clamp_assert_certificate >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `run_inst_seq [mk_inst id SIGNEXTEND _ _] s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst (id+1) EQ [x;Var a] [b]]` mp_tac) >> simp[]
QED

Theorem scalar_checked_pair_uniform_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = OK t \/
   run_inst_seq [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = Abort err t) ==>
  !k. ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) ASSERT [Var b] []] (s with vs_inst_idx := k) H th /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  irule scalar_checked_pair_certificate >> simp[] >>
  qexistsl_tac [`err`,`t with vs_inst_idx := k`] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []]` by
    gvs[MEM, mk_inst_def, is_terminator_def] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem scalar_empty_uniform_certificate:
  ?H th.
    (!k. inst_seq_ptr D lo ctx fn PG G tn [] (s with vs_inst_idx := k) H th) /\
    H = G /\ th = tn
Proof
  qexistsl_tac [`G`,`tn`] >> simp[inst_seq_ptr_def]
QED

Theorem convert_int_bytes_decompose:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) ==>
  ?mid.
    emit_op SHL [Lit (n2w ((32-m)*8));x] mid = (out,sb) /\
    emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb /\
    (!p. not_fresh_at sa p ==> not_fresh_at mid p) /\
    (if m*8 < bits then
       ?a b.
         emitted_insts sa mid =
           (if signed then
             [mk_inst sa.cs_next_id SIGNEXTEND [Lit (n2w (m-1));x] [a];
              mk_inst (sa.cs_next_id+1) EQ [x;Var a] [b];
              mk_inst (sa.cs_next_id+2) ASSERT [Var b] []]
            else
             [mk_inst sa.cs_next_id GT [x;Lit (n2w (2 ** (m*8)-1))] [a];
              mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
              mk_inst (sa.cs_next_id+2) ASSERT [Var b] []]) /\
         (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
     else mid = sa)
Proof
  Cases_on `m*8 < bits`
  >- (Cases_on `signed` >>
      simp[compile_type_convert_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      qpat_x_assum `(\(ext,cs). _) _ = _` mp_tac >>
      rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
      strip_tac >> gvs[] >>
      imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      gvs[same_blocks_def] >> strip_tac >> qexists_tac `cs'` >> simp[] >>
      qpat_assum `emit_op SHL _ _ = _`
        (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
      qpat_assum `emit_op SHL _ _ = _`
        (mp_then Any strip_assume_tac emit_op_extends) >>
      `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
        (qspecl_then [`sa`,`cs'`,`sb`] mp_tac emitted_insts_append >>
         simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
      simp[] >> (conj_tac
      >- (gvs[not_fresh_at_def] >> rpt strip_tac >>
          goal_assum (drule_at Any) >> simp[]) >>
      simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
      qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                    `STRING #"%" (toString (sa.cs_next_var+1))`] >>
      simp[not_fresh_at_def] >> rpt strip_tac >>
      first_x_assum irule >> simp[])) >>
  simp[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  strip_tac >> simp[emitted_insts_def]
QED

Theorem convert_int_bytes_instruction_filter:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule convert_int_bytes_decompose >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  qpat_assum `emit_op SHL _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  Cases_on `m*8 < bits` >> gvs[]
  >- (Cases_on `signed` >> gvs[FILTER_APPEND, mk_inst_def, is_terminator_def]) >>
  simp[emitted_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem scalar_byte_check_uniform_certificate:
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  xs = (if signed then
    [mk_inst id SIGNEXTEND [Lit w;x] [a]; mk_inst (id+1) EQ [x;Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []]
   else [mk_inst id GT [x;Lit hi] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []]) /\
  (run_inst_seq xs s = OK t \/ run_inst_seq xs s = Abort err t) ==>
  !k. ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn xs (s with vs_inst_idx := k) H th /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `signed` >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[]
  >- (drule_all scalar_signed_byte_uniform_certificate >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
      gen_tac >> qexistsl_tac [`H`,`th`] >> simp[]) >>
  `MEM GT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
   op_prov G (Lit hi) = NONE /\ op_taint tn (Lit hi) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all scalar_checked_pair_uniform_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >> simp[]
QED
