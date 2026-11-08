Theory bodyPtrTypeBuiltinsCheckedArithmetic
Ancestors
  bodyPtrTypeBuiltinsScalarCompose bodyPtrTypeBuiltinsScalarChecks
  bodyPtrTypeBuiltinsScalarArithmetic
  bodyPtrSignedConvertClamp bodyPtrSignedConvertScalarOps exprLowering exprLoweringProps
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

Theorem convert_int_bytes_prefix_certificate:
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (if m*8 < bits then
     ?a b. emitted_insts sa mid =
       (if signed then
         [mk_inst sa.cs_next_id SIGNEXTEND [Lit (n2w (m-1));x] [a];
          mk_inst (sa.cs_next_id+1) EQ [x;Var a] [b];
          mk_inst (sa.cs_next_id+2) ASSERT [Var b] []]
        else
         [mk_inst sa.cs_next_id GT [x;Lit (n2w (2 ** (m*8)-1))] [a];
          mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
          mk_inst (sa.cs_next_id+2) ASSERT [Var b] []]) /\
       (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
   else mid = sa) /\
  (run_inst_seq (emitted_insts sa mid) s = OK t \/
   run_inst_seq (emitted_insts sa mid) s = Abort err t) ==>
  !k. ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa mid)
      (s with vs_inst_idx := k) H th /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `m*8 < bits` >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `?a b. _` strip_assume_tac >>
      drule_all scalar_byte_check_uniform_certificate >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
      strip_tac >> gen_tac >> first_x_assum (qspec_then `k` strip_assume_tac) >>
      qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]) >>
  gvs[emitted_insts_def] >> gen_tac >> qexistsl_tac [`G`,`tn`] >>
  simp[inst_seq_ptr_def]
QED

Theorem scalar_emit_uniform_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  !k. ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  drule_all scalar_emit_instruction_filter >> strip_tac >>
  irule scalar_emit_fixed_certificate >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`opc`,`x`,`y`] >> gvs[MEM]) >>
  qexists_tac `t with vs_inst_idx := k` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    gvs[EVERY_MEM] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem convert_int_bytes_fixed_certificate:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule convert_int_bytes_decompose >> strip_tac >>
  drule convert_int_bytes_instruction_filter >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa mid)` by
    gvs[EVERY_APPEND, EVERY_MEM] >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >> strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
    convert_int_bytes_prefix_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` strip_assume_tac) >> gvs[] >>
  `op_prov H x = NONE /\ op_taint th x = {} /\
   op_prov H (Lit (n2w (8*(32-m)))) = NONE /\
   op_taint th (Lit (n2w (8*(32-m)))) = {} /\
   MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by
    (simp[op_prov_def, op_taint_def] >> metis_tac[]) >>
  drule_all scalar_emit_uniform_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] assume_tac) >>
  pop_assum (qspec_then `s.vs_inst_idx + LENGTH (emitted_insts sa mid)`
    strip_assume_tac) >>
  qexistsl_tac [`H'`,`th'`] >> reverse conj_tac
  >- (simp[] >> metis_tac[]) >>
  irule scalar_seq_ptr_append_at >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >>
  once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC
QED

Theorem convert_int_bytes_abort_fixed_certificate:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule convert_int_bytes_decompose >> strip_tac >>
  drule convert_int_bytes_instruction_filter >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa mid)` by
    gvs[EVERY_APPEND, EVERY_MEM] >>
  `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_emit_no_abort >> strip_tac >>
  `run_inst_seq (emitted_insts sa mid) s = Abort err t` by
    (qpat_x_assum `run_inst_seq _ s = Abort err t` mp_tac >>
     asm_rewrite_tac[] >> rewrite_tac[scalar_seq_append_abort_iff] >> metis_tac[]) >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
    convert_int_bytes_prefix_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` strip_assume_tac) >> fs[] >>
  qexistsl_tac [`H`,`th`] >> reverse conj_tac >- simp[] >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  irule inst_seq_ptr_abort_append >> goal_assum (drule_at Any) >> simp[]
QED

Theorem convert_int_bytes_counted_certificate:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all convert_int_bytes_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule convert_int_bytes_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_int_bytes_abort_counted_certificate:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th (Abort err (t with vs_inst_idx := j)) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all convert_int_bytes_abort_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_int_bytes_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED

Theorem convert_int_bytes_runtime_frame:
  compile_type_convert x (ConvIntToBytesM signed bits m) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule convert_int_bytes_decompose >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >> strip_tac >>
  `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_emit_runtime_frame >> strip_tac >>
  `(u with vs_vars := s.vs_vars) = s /\
   (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s)` by
    (Cases_on `m*8 < bits` >> gvs[]
     >- (Cases_on `signed` >> gvs[]
         >- (drule scalar_signed_byte_runtime_frame >> strip_tac >> simp[] >> metis_tac[]) >>
         `MEM GT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
         drule_all scalar_checked_pair_runtime_frame >> strip_tac >> simp[] >> metis_tac[]) >>
     gvs[emitted_insts_def, run_inst_seq_def]) >>
  irule scalar_seq_runtime_frame_trans >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem scalar_optional_check_decompose:
  (if enabled then
     comp_bind (emit_op opc [x;Lit w]) (\a.
       comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
   else comp_return ()) sa = (res,sb) ==>
  (if enabled then
     ?a b. emitted_insts sa sb =
       [mk_inst sa.cs_next_id opc [x;Lit w] [a];
        mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
        mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
       (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
   else sb = sa) /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  (!p. not_fresh_at sa p ==> not_fresh_at sb p)
Proof
  Cases_on `enabled` >> simp[comp_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      gvs[same_blocks_def] >>
      simp[emitted_insts_def, DROP_LENGTH_APPEND] >> conj_tac
      >- (qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                       `STRING #"%" (toString (sa.cs_next_var+1))`] >>
          simp[not_fresh_at_def] >> rpt strip_tac >>
          first_x_assum irule >> simp[]) >>
      gvs[not_fresh_at_def] >> rpt strip_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[emitted_insts_def, same_blocks_def]
QED

Theorem scalar_two_checks_decompose:
  comp_ignore_bind
    (if c1 then comp_bind (emit_op op1 [x;Lit w1]) (\a.
       comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
     else comp_return ())
    (comp_ignore_bind
      (if c2 then comp_bind (emit_op op2 [x;Lit w2]) (\a.
         comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
       else comp_return ())
      (emit_op opc [x;Lit scale])) sa = (out,sb) ==>
  ?s1 s2.
    emit_op opc [x;Lit scale] s2 = (out,sb) /\
    emitted_insts sa sb = emitted_insts sa s1 ++ emitted_insts s1 s2 ++ emitted_insts s2 sb /\
    (!p. not_fresh_at sa p ==> not_fresh_at s1 p) /\
    (!p. not_fresh_at s1 p ==> not_fresh_at s2 p) /\
    (if c1 then ?a b. emitted_insts sa s1 =
       [mk_inst sa.cs_next_id op1 [x;Lit w1] [a];
        mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
        mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
        (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
     else s1 = sa) /\
    (if c2 then ?a b. emitted_insts s1 s2 =
       [mk_inst s1.cs_next_id op2 [x;Lit w2] [a];
        mk_inst (s1.cs_next_id+1) ISZERO [Var a] [b];
        mk_inst (s1.cs_next_id+2) ASSERT [Var b] []] /\
        (!p. not_fresh_at s1 p ==> p <> a /\ p <> b)
     else s2 = s1)
Proof
  simp[comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_assum `(if c1 then _ else _) sa = _`
    (mp_then Any strip_assume_tac scalar_optional_check_decompose) >>
  qpat_assum `(if c2 then _ else _) cs' = _`
    (mp_then Any strip_assume_tac scalar_optional_check_decompose) >>
  drule emit_op_extends >> strip_tac >>
  qexistsl_tac [`cs'`,`cs''`] >> simp[] >>
  `emitted_insts sa cs'' = emitted_insts sa cs' ++ emitted_insts cs' cs''` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa cs'' ++ emitted_insts cs'' sb` by
    (irule emitted_insts_append >> simp[same_blocks_def] >> metis_tac[]) >>
  simp[APPEND_ASSOC]
QED

Theorem scalar_optional_check_uniform_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (if enabled then ?a b. emitted_insts sa sb =
       [mk_inst sa.cs_next_id opc [x;Lit w] [a];
        mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
        mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
       (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
   else sb = sa) /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  !k. ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `enabled` >> pure_rewrite_tac[COND_CLAUSES] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `?a b. _` strip_assume_tac >>
      qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
      `op_prov G (Lit w) = NONE /\ op_taint tn (Lit w) = {}` by
        simp[op_prov_def, op_taint_def] >>
      drule_all scalar_checked_pair_uniform_certificate >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
      strip_tac >> gen_tac >> first_x_assum (qspec_then `k` strip_assume_tac) >>
      qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]) >>
  gvs[emitted_insts_def] >> gen_tac >> qexistsl_tac [`G`,`tn`] >>
  simp[inst_seq_ptr_def]
QED

Theorem scalar_optional_check_instruction_filter:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  (if enabled then ?a b. emitted_insts sa sb =
       [mk_inst sa.cs_next_id opc [x;Lit w] [a];
        mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
        mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
       (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
   else sb = sa) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `enabled` >> pure_rewrite_tac[COND_CLAUSES] >> strip_tac
  >- gvs[MEM, mk_inst_def, is_terminator_def] >>
  gvs[emitted_insts_def]
QED

Theorem scalar_optional_check_runtime_frame:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  (if enabled then ?a b. emitted_insts sa sb =
       [mk_inst sa.cs_next_id opc [x;Lit w] [a];
        mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
        mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
       (!p. not_fresh_at sa p ==> p <> a /\ p <> b)
   else sb = sa) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  Cases_on `enabled` >> pure_rewrite_tac[COND_CLAUSES] >> strip_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
      drule_all scalar_checked_pair_runtime_frame >> strip_tac >> simp[] >> metis_tac[]) >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem scalar_two_checks_fixed_certificate:
  comp_ignore_bind
    (if c1 then comp_bind (emit_op op1 [x;Lit w1]) (\a.
       comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
     else comp_return ())
    (comp_ignore_bind
      (if c2 then comp_bind (emit_op op2 [x;Lit w2]) (\a.
         comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
       else comp_return ())
      (emit_op opc [x;Lit scale])) sa = (out,sb) /\
  MEM op1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM op2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule scalar_two_checks_decompose >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s1) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s1 s2)` by
    (drule_all scalar_optional_check_instruction_filter >> strip_tac >>
     rev_drule_all scalar_optional_check_instruction_filter >> strip_tac >>
     qpat_x_assum `EVERY _ (emitted_insts sa s1)` mp_tac >>
     qpat_x_assum `EVERY _ (emitted_insts s1 s2)` mp_tac >>
     simp_tac pure_ss [EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >> strip_tac >>
  rev_drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
    scalar_optional_check_uniform_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` strip_assume_tac) >>
  `op_prov H x = NONE /\ op_taint th x = {}` by metis_tac[] >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
    scalar_optional_check_uniform_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx + LENGTH (emitted_insts sa s1)` strip_assume_tac) >>
  `op_prov H' x = NONE /\ op_taint th' x = {} /\
   op_prov H' (Lit scale) = NONE /\ op_taint th' (Lit scale) = {}` by
    (simp[op_prov_def, op_taint_def] >> metis_tac[]) >>
  drule_all scalar_emit_uniform_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx + LENGTH (emitted_insts sa s1) +
    LENGTH (emitted_insts s1 s2)` strip_assume_tac) >>
  qexistsl_tac [`H''`,`th''`] >> reverse conj_tac
  >- (simp[] >> metis_tac[]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ G tn _ _ _ _`
    (assume_tac o SRULE []) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule scalar_seq_ptr_append_at >> simp[] >> qexistsl_tac [`H`,`th`] >>
  simp[] >> once_rewrite_tac[ADD_COMM] >>
  irule scalar_seq_ptr_append_at >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`H'`,`th'`,`u with vs_inst_idx :=
    s.vs_inst_idx + LENGTH (emitted_insts sa s1)`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ H' th' _ _ _ _` mp_tac >>
  simp_tac (pure_ss ++ boolSimps.BOOL_ss) [AC ADD_ASSOC ADD_COMM]
QED

Theorem scalar_two_checks_instruction_filter:
  comp_ignore_bind
    (if c1 then comp_bind (emit_op op1 [x;Lit w1]) (\a.
       comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
     else comp_return ())
    (comp_ignore_bind
      (if c2 then comp_bind (emit_op op2 [x;Lit w2]) (\a.
         comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
       else comp_return ())
      (emit_op opc [x;Lit scale])) sa = (out,sb) /\
  MEM op1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM op2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule scalar_two_checks_decompose >> strip_tac >>
  drule_all scalar_optional_check_instruction_filter >> strip_tac >>
  rev_drule_all scalar_optional_check_instruction_filter >> strip_tac >>
  drule_all scalar_emit_instruction_filter >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  simp[EVERY_APPEND, FILTER_APPEND]
QED

Theorem scalar_two_checks_abort_fixed_certificate:
  comp_ignore_bind
    (if c1 then comp_bind (emit_op op1 [x;Lit w1]) (\a.
       comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
     else comp_return ())
    (comp_ignore_bind
      (if c2 then comp_bind (emit_op op2 [x;Lit w2]) (\a.
         comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
       else comp_return ())
      (emit_op opc [x;Lit scale])) sa = (out,sb) /\
  MEM op1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM op2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_two_checks_instruction_filter >> strip_tac >>
  drule scalar_two_checks_decompose >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s1) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s1 s2)` by
    (qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     asm_rewrite_tac[EVERY_APPEND] >> simp_tac pure_ss [EVERY_MEM] >> metis_tac[]) >>
  drule_all scalar_emit_no_abort >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = Abort err t` mp_tac >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  rewrite_tac[scalar_seq_append_abort_iff] >> strip_tac
  >- (drule_all (cj 2 (PURE_REWRITE_RULE
        [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
        scalar_optional_check_uniform_certificate)) >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
      disch_then (qspec_then `s.vs_inst_idx` strip_assume_tac) >>
      qexistsl_tac [`H`,`th`] >> reverse conj_tac >- simp[] >>
      qpat_x_assum `inst_seq_ptr _ _ _ _ _ G tn _ _ _ _` (assume_tac o SRULE []) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      irule inst_seq_ptr_abort_append >> goal_assum (drule_at Any) >> simp[])
  >- (drule_all (cj 1 (PURE_REWRITE_RULE
        [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
        scalar_optional_check_uniform_certificate)) >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
      disch_then (qspec_then `s.vs_inst_idx` strip_assume_tac) >>
      `op_prov H x = NONE /\ op_taint th x = {}` by metis_tac[] >>
      drule_all (cj 2 (PURE_REWRITE_RULE
        [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
        scalar_optional_check_uniform_certificate)) >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
      disch_then (qspec_then `s.vs_inst_idx + LENGTH (emitted_insts sa s1)` strip_assume_tac) >>
      qexistsl_tac [`H'`,`th'`] >> reverse conj_tac >- (simp[] >> metis_tac[]) >>
      qpat_x_assum `inst_seq_ptr _ _ _ _ _ G tn _ _ _ _` (assume_tac o SRULE []) >>
      irule scalar_seq_ptr_append_at >> simp[] >> qexistsl_tac [`H`,`th`] >> simp[] >>
      irule inst_seq_ptr_abort_append >> reverse conj_tac
      >- (simp[] >> once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`err`,`t with vs_inst_idx :=
        s.vs_inst_idx + LENGTH (emitted_insts sa s1)`] >>
      simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  metis_tac[]
QED

Theorem scalar_two_checks_runtime_frame:
  comp_ignore_bind
    (if c1 then comp_bind (emit_op op1 [x;Lit w1]) (\a.
       comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
     else comp_return ())
    (comp_ignore_bind
      (if c2 then comp_bind (emit_op op2 [x;Lit w2]) (\a.
         comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
       else comp_return ())
      (emit_op opc [x;Lit scale])) sa = (out,sb) /\
  MEM op1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM op2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule scalar_two_checks_decompose >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >> strip_tac >>
  drule_all scalar_optional_check_runtime_frame >> strip_tac >>
  rev_drule_all scalar_optional_check_runtime_frame >> strip_tac >>
  drule_all scalar_emit_runtime_frame >> strip_tac >>
  `(u with vs_vars := s.vs_vars) = s /\
   (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s)` by
    (irule scalar_seq_runtime_frame_trans >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule scalar_seq_runtime_frame_trans >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Both decimal directions have the same pointer-relevant compiler shape.
   Threshold arithmetic only decides whether the two checks are present. *)
Theorem convert_decimal_pipeline:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) ==>
  ?c1 c2 op2 w1 w2 opc scale.
  compile_type_convert x tc =
    comp_ignore_bind
      (if c1 then comp_bind (emit_op SLT [x;Lit w1]) (\a.
         comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
       else comp_return ())
      (comp_ignore_bind
        (if c2 then comp_bind (emit_op op2 [x;Lit w2]) (\a.
           comp_bind (emit_op ISZERO [a]) (\b. emit_void ASSERT [b]))
         else comp_return ())
        (emit_op opc [x;Lit scale])) /\
  MEM op2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]
Proof
  strip_tac >> gvs[]
  >- (qexistsl_tac
        [`(if signed then - &(2 ** (bits-1)) else 0) < lo quot &divisor`,
         `(if signed then &(2 ** (bits-1)-1) else &(2 ** bits-1)) > hi quot &divisor`,
         `if signed then SGT else GT`, `i2w (lo quot &divisor)`,
         `i2w (hi quot &divisor)`, `MUL`, `n2w divisor`] >>
      Cases_on `signed` >> simp[compile_type_convert_def]) >>
  qexistsl_tac [`ilo < lo * &divisor`, `ihi > hi * &divisor`,
    `if signed then SGT else GT`, `i2w (lo * &divisor)`,
    `i2w (hi * &divisor)`, `SDIV`, `n2w divisor`] >>
  Cases_on `signed` >> simp[compile_type_convert_def]
QED

Theorem convert_decimal_fixed_certificate:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule convert_decimal_pipeline >> disch_then (qspec_then `x` strip_assume_tac) >>
  qpat_x_assum `compile_type_convert x tc = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `MEM SLT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_two_checks_fixed_certificate >> simp[]
QED

Theorem convert_decimal_abort_fixed_certificate:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule convert_decimal_pipeline >> disch_then (qspec_then `x` strip_assume_tac) >>
  qpat_x_assum `compile_type_convert x tc = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `MEM SLT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_two_checks_abort_fixed_certificate >> simp[]
QED

Theorem convert_decimal_instruction_filter:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) /\
  compile_type_convert x tc sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule convert_decimal_pipeline >> disch_then (qspec_then `x` strip_assume_tac) >>
  qpat_x_assum `compile_type_convert x tc = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `MEM SLT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_two_checks_instruction_filter >> simp[]
QED

Theorem convert_decimal_runtime_frame:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) /\
  compile_type_convert x tc sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule convert_decimal_pipeline >> disch_then (qspec_then `x` strip_assume_tac) >>
  qpat_x_assum `compile_type_convert x tc = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `MEM SLT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_two_checks_runtime_frame >> simp[]
QED

Theorem convert_decimal_counted_certificate:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all convert_decimal_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule_all convert_decimal_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_decimal_abort_counted_certificate:
  ((?signed bits divisor lo hi. tc = ConvIntToDecimal signed bits divisor lo hi) \/
   (?divisor ilo ihi lo hi signed. tc = ConvDecimalToInt divisor ilo ihi lo hi signed)) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th (Abort err (t with vs_inst_idx := j)) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all convert_decimal_abort_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule_all convert_decimal_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED
