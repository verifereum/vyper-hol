(* Uniform clean-operand signed continuation certificates. *)
Theory bodyFullConvertSignedClamp
Ancestors
  bodyPtrSignedConvertClamp exprSimConvertFromBytes instSeqComposePtr
  bodyFullConvertScalarCertificate fragExecMem memSafeRun
  fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragExec instIdxIndep
  exprLoweringProps emitHelperProps venomState venomInst venomExecSemantics
  ptrDiscipline finite_map words arithmetic list pred_set

Theorem double_check_uniform_prefix[local]:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc1 [x;Lit lower] [a];
    mk_inst (id+1) ISZERO [Var a] [b]] s = OK u /\
  run_inst_seq [mk_inst (id+2) opc2 [x;Lit upper] [c];
    mk_inst (id+3) ISZERO [Var c] [d]] u = OK v /\
  run_inst_seq [mk_inst (id+4) AND [Var b;Var d] [e]] v = OK w ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc1 [x;Lit lower] [a];
       mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) opc2 [x;Lit upper] [c];
       mk_inst (id+3) ISZERO [Var c] [d];
       mk_inst (id+4) AND [Var b;Var d] [e]]
      (s with vs_inst_idx := q) H th) /\
    op_prov H (Var e) = NONE /\ op_taint th (Var e) = {} /\
    op_prov H x = NONE /\ op_taint th x = {} /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all scalar_double_checked_prefix >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[] >> rpt gen_tac >>
  drule_all scalar_double_checked_prefix >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `H' = H /\ th' = th` by metis_tac[inst_seq_ptr_ghost_unique] >>
  qpat_x_assum `H' = H` SUBST_ALL_TAC >>
  qpat_x_assum `th' = th` SUBST_ALL_TAC >>
  first_assum (qspec_then `q` ACCEPT_TAC)
QED

Theorem double_check_uniform_certificate[local]:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq
    [mk_inst id opc1 [x;Lit lower] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x;Lit upper] [c]; mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b;Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s = OK t \/
   run_inst_seq
    [mk_inst id opc1 [x;Lit lower] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x;Lit upper] [c]; mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b;Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s = Abort err t) ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc1 [x;Lit lower] [a]; mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) opc2 [x;Lit upper] [c]; mk_inst (id+3) ISZERO [Var c] [d];
       mk_inst (id+4) AND [Var b;Var d] [e]; mk_inst (id+5) ASSERT [Var e] []]
      (s with vs_inst_idx := q) H th) /\
    op_prov H x = NONE /\ op_taint th x = {} /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_double_check_prefix_runs >> strip_tac >>
  drule_all double_check_uniform_prefix >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[] >> rpt gen_tac >>
  irule (PURE_REWRITE_RULE [APPEND] (Q.INST
    [`xs` |-> `[mk_inst id opc1 [x;Lit lower] [a];
      mk_inst (id+1) ISZERO [Var a] [b]; mk_inst (id+2) opc2 [x;Lit upper] [c];
      mk_inst (id+3) ISZERO [Var c] [d]; mk_inst (id+4) AND [Var b;Var d] [e]]`]
    (Q.INST [`id` |-> `id+5`] (SPEC_ALL checked_prefix_assert_certificate)))) >>
  imp_res_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_opcode_filter >>
  simp[mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def] >>
  qexistsl [`w with vs_inst_idx := q`,`value`] >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  conj_tac
  >- (qpat_abbrev_tac `code = [_;_;_;_;_]` >>
      `run_inst_seq code s = OK w` by
        (simp[Abbr `code`] >>
         qpat_assum `run_inst_seq [_;_] s = OK u` (mp_tac o MATCH_MP run_inst_seq_append) >>
         disch_then (qspec_then
           `[mk_inst (id+2) opc2 [x;Lit upper] [c];
             mk_inst (id+3) ISZERO [Var c] [d];
             mk_inst (id+4) AND [Var b;Var d] [e]]` mp_tac) >>
         simp[] >> disch_then SUBST1_TAC >>
         qpat_assum `run_inst_seq [_;_] u = OK v` (mp_tac o MATCH_MP run_inst_seq_append) >>
         disch_then (qspec_then `[mk_inst (id+4) AND [Var b;Var d] [e]]` mp_tac) >>
         simp[]) >>
      simp[run_inst_seq_inst_idx, Abbr `code`, mk_inst_def,
           is_terminator_def, exec_result_map_def]) >>
  fs[eval_operand_def, lookup_var_def]
QED

Theorem double_check_runtime_endpoint[local]:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  code = [mk_inst id opc1 [x;Lit lower] [a];
    mk_inst (id+1) ISZERO [Var a] [b];
    mk_inst (id+2) opc2 [x;Lit upper] [c];
    mk_inst (id+3) ISZERO [Var c] [d];
    mk_inst (id+4) AND [Var b;Var d] [e];
    mk_inst (id+5) ASSERT [Var e] []] /\
  (!z. x = Var z ==> ~MEM z [a;b;c;d;e]) ==>
  (!t. run_inst_seq code s = OK t ==>
    state_frame t = state_frame s /\
    (!z. ~MEM z [a;b;c;d;e] ==> lookup_var z t = lookup_var z s) /\
    eval_operand x t = eval_operand x s) /\
  (!err t. run_inst_seq code s = Abort err t ==>
    state_frame t = state_frame (revert_state (set_returndata [] s)) /\
    (!z. ~MEM z [a;b;c;d;e] ==> lookup_var z t = lookup_var z s) /\
    eval_operand x t = eval_operand x s)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `((t with vs_vars := s.vs_vars) = s) /\
       (!z. ~MEM z [a;b;c;d;e] ==> lookup_var z t = lookup_var z s)` by
        (irule scalar_double_check_runtime_frame >> metis_tac[]) >>
      conj_tac
      >- (qpat_x_assum `(t with vs_vars := _) = s` (mp_tac o AP_TERM ``state_frame``) >>
          simp[stateFrameTheory.state_frame_def]) >>
      conj_tac >- simp[] >>
      `t.vs_labels = s.vs_labels` by
        (qpat_x_assum `(t with vs_vars := _) = s`
          (mp_tac o AP_TERM ``\v:venom_state. v.vs_labels``) >> simp[]) >>
      Cases_on `x` >> simp[eval_operand_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `code = _` SUBST_ALL_TAC >>
  qpat_x_assum `run_inst_seq _ s = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs(),
    bodyPtrSignedConvertScalarOpsTheory.convert_scalar_no_abort,
    bodyPtrSignedConvertScalarOpsTheory.scalar_iszero_no_abort] >> strip_tac >>
  qpat_x_assum `step_inst_base (mk_inst id opc1 _ _) _ = _`
    (mp_then Any mp_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `w1` SUBST_ALL_TAC) >>
  qpat_x_assum `step_inst_base (mk_inst _ opc2 _ _) _ = _`
    (mp_then Any mp_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `w2` SUBST_ALL_TAC) >>
  qpat_x_assum `MEM opc1 _` kall_tac >>
  qpat_x_assum `MEM opc2 _` kall_tac >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac bodyPtrSignedConvertIszeroTheory.iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac bodyPtrSignedConvertIszeroTheory.iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ AND _ _) _ = _`
    (mp_then Any mp_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_run_shape) >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV
    [step_inst_base_def, mk_inst_def, instruction_accessors,
     instruction_accfupds, combinTheory.K_THM, opcode_case_def]))) >>
  simp[AllCaseEqs(), eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  simp[stateFrameTheory.state_frame_def, revert_state_def, set_returndata_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `x` >> gvs[eval_operand_def, lookup_var_def, revert_state_def,
                      set_returndata_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem convert_signed_decimal_suffix_origin_path:
  emitted_insts sa sb =
    [mk_inst id SLT [x;Lit lower] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) SGT [x;Lit upper] [c];
     mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b;Var d] [e];
     mk_inst (id+5) ASSERT [Var e] []] /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ALL_DISTINCT [a;b;c;d;e] /\
  (!p. not_fresh_at sa p ==> ~MEM p [a;b;c;d;e]) /\
  (!p. x = Var p ==> not_fresh_at sa p) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = r /\
  ((?u. r = OK u) \/ (?err u. r = Abort err u)) ==>
  ?t Gf tnf.
    (!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := q) Gf tnf) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (exec_result_map (\u. t) r,Gf,tnf)) /\
    (!u. r = OK u ==>
      t = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    (!err u. r = Abort err u ==> t = u with vs_inst_idx := t.vs_inst_idx) /\
    (!u. r = OK u ==>
      state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)) /\
    (!err u. r = Abort err u ==>
      state_frame t = state_frame
        ((revert_state (set_returndata [] s)) with vs_inst_idx := t.vs_inst_idx)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    eval_operand x t = eval_operand x s /\
    op_prov Gf x = NONE /\ op_taint tnf x = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?H th. (!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := q) H th) /\
    op_prov H x = NONE /\ op_taint th x = {} /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm` by
    (simp[] >> irule (SRULE [] double_check_uniform_certificate) >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := q) H th` by
    (rpt gen_tac >> irule scalar_seq_lower_bound >>
     simp[allocas_from_def] >>
     conj_tac >- (fs[EVERY_MEM, allocas_from_def] >> metis_tac[]) >>
     qexists `0` >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       inst_dload_in_section_def]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code _ _ _` mp_tac >>
     pure_rewrite_tac[fn_has_code_def] >> strip_tac >>
     qexists `bb` >> conj_tac >- metis_tac[] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  `(!u. run_inst_seq (emitted_insts sa sb) s = OK u ==>
      state_frame u = state_frame s /\
      (!p. ~MEM p [a;b;c;d;e] ==> lookup_var p u = lookup_var p s) /\
      eval_operand x u = eval_operand x s) /\
   (!err u. run_inst_seq (emitted_insts sa sb) s = Abort err u ==>
      state_frame u = state_frame (revert_state (set_returndata [] s)) /\
      (!p. ~MEM p [a;b;c;d;e] ==> lookup_var p u = lookup_var p s) /\
      eval_operand x u = eval_operand x s)` by
    (irule double_check_runtime_endpoint >> simp[] >> metis_tac[]) >>
  `!u D. r = OK u ==> gas_origin_ptr_path
      (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),H,th)` by
    (rpt gen_tac >> disch_tac >>
     `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
       (first_x_assum (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >>
        simp[venomStateTheory.venom_state_component_equality]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
         (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
     `run_inst_seq (emitted_insts sa sb) s = OK u` by metis_tac[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[mk_inst_def]) >>
  `!err u. r = Abort err u ==> ?j. !D.
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (Abort err (u with vs_inst_idx := j),H,th)` by
    (rpt gen_tac >> disch_tac >>
     `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
       (gen_tac >> first_x_assum (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >>
        simp[venomStateTheory.venom_state_component_equality]) >>
     `run_inst_seq (emitted_insts sa sb) s = Abort err u` by metis_tac[] >>
     drule_all run_inst_seq_abort_origin_ptr_uniform >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     qexists `j` >> metis_tac[]) >>
  Cases_on `r` >> gvs[exec_result_map_def]
  >- (qexistsl [`H`, `th`] >> simp[blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rename1 `run_inst_seq _ s = Abort err u` >>
  qexistsl [`u with vs_inst_idx := j`, `H`, `th`] >>
  simp[blockPrefixEquivTheory.lookup_var_set_inst_idx]
QED

Theorem convert_signed_clamp_origin_path:
  compile_int_clamp T bits x sa = (out,sb) /\
  (!p. x = Var p ==> not_fresh_at sa p) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = r /\
  ((?u. r = OK u) \/ (?err u. r = Abort err u)) ==>
  ?t Gf tnf.
    (!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := q) Gf tnf) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (exec_result_map (\u. t) r,Gf,tnf)) /\
    (!u. r = OK u ==>
      t = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    (!err u. r = Abort err u ==> t = u with vs_inst_idx := t.vs_inst_idx) /\
    (!u. r = OK u ==>
      state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)) /\
    (!err u. r = Abort err u ==>
      state_frame t = state_frame
        ((revert_state (set_returndata [] s)) with vs_inst_idx := t.vs_inst_idx)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    eval_operand x t = eval_operand x s /\
    op_prov Gf x = NONE /\ op_taint tnf x = {} /\
    op_prov Gf out = NONE /\ op_taint tnf out = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule int_clamp_signed_code >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[builtinConvertPrefixTheory.inst_extends_compile_int_clamp,
      inst_extends_def] >>
  drule_all convert_signed_decimal_suffix_origin_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED
