Theory bodyPtrTypeBuiltinsClamp
Ancestors
  bodyPtrTypeBuiltinsScalarOps bodyPtrTypeBuiltinsBool bodyPtrTypeBuiltinsIszero
  venomExecSemantics exprSendPtr fragGasSeqPtr bodyPtrTypeBuiltinsScalarTransfer list
  instSeqComposePtr exprLowering exprLoweringProps emitHelperProps
  compileEnv ASCIInumbers rich_list ptrDiscipline finite_map venomState venomInst

Theorem int_clamp_unsigned_code:
  compile_int_clamp F bits x sa = (out,sb) ==>
  ?a b.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id GT [x; Lit (n2w (2 ** bits - 1))] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
    a <> b /\
    (!p. not_fresh_at sa p ==> p <> a /\ p <> b) /\
    sb.cs_next_var = sa.cs_next_var+2 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+3
Proof
  simp[compile_int_clamp_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var+1))`] >> simp[toString_inj]
QED

Theorem int_clamp_signed_code:
  compile_int_clamp T bits x sa = (out,sb) ==>
  ?a b c d e.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SLT [x; Lit (i2w (- &(2 ** (bits-1))))] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) SGT [x; Lit (i2w (&(2 ** (bits-1)-1)))] [c];
       mk_inst (sa.cs_next_id+3) ISZERO [Var c] [d];
       mk_inst (sa.cs_next_id+4) AND [Var b; Var d] [e];
       mk_inst (sa.cs_next_id+5) ASSERT [Var e] []] /\
    ALL_DISTINCT [a;b;c;d;e] /\
    (!p. not_fresh_at sa p ==> ~MEM p [a;b;c;d;e]) /\
    sb.cs_next_var = sa.cs_next_var+5 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+6
Proof
  simp[compile_int_clamp_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var+1))`,
                `STRING #"%" (toString (sa.cs_next_var+2))`,
                `STRING #"%" (toString (sa.cs_next_var+3))`,
                `STRING #"%" (toString (sa.cs_next_var+4))`] >> simp[toString_inj]
QED

Theorem unsigned_clamp_runtime_frame:
  run_inst_seq
    [mk_inst id GT [x; Lit hi] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. p <> a /\ p <> b ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_assum `step_inst_base (mk_inst id GT _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  drule iszero_run_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem signed_clamp_runtime_frame:
  run_inst_seq
    [mk_inst id SLT [x; Lit lo] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) SGT [x; Lit hi] [c];
     mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b; Var d] [e];
     mk_inst (id+5) ASSERT [Var e] []] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. ~MEM p [a;b;c;d;e] ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base (mk_inst id SLT _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ SGT _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ AND _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem int_clamp_runtime_frame:
  compile_int_clamp signed bits x sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> Cases_on `signed`
  >- (drule int_clamp_signed_code >> strip_tac >> gvs[] >>
      drule signed_clamp_runtime_frame >> strip_tac >> simp[] >> metis_tac[]) >>
  drule int_clamp_unsigned_code >> strip_tac >> gvs[] >>
  drule unsigned_clamp_runtime_frame >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem scalar_iszero_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc [x;y] [a];
                mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b]] s
    (DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b}))
    (tn with t_var := tn.t_var |+ (a,{}) |+ (b,{}))
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  qpat_assum `step_inst_base (mk_inst id _ _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule iszero_run_shape >> strip_tac >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule convert_scalar_ptr_inst_ok >> simp[] >> goal_assum (drule_at Any)) >>
  `step_prov PG G (mk_inst id opc [x;y] [a]) (update_var a w s) =
     DRESTRICT G (COMPL {a})` by
    (simp[step_prov_def, set_prov_def, mk_inst_def] >>
     `out_prov PG G (mk_inst id opc [x;y] [a]) (update_var a w s) = NONE` by
       (irule out_prov_clearing_none >> gvs[MEM, mk_inst_def]) >>
     gvs[mk_inst_def]) >>
  `step_taint (mk_inst id opc [x;y] [a]) s (update_var a w s) tn =
    (tn with t_var := tn.t_var |+ (a,{}))` by
    (irule convert_scalar_ghost_update >> simp[] >> goal_assum (drule_at Any)) >>
  simp[] >>
  `step_inst_base (mk_inst (id+1) ISZERO [Var a] [b])
    (update_var a w s with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (update_var b (bool_to_word (w = 0w))
      (update_var a w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emitHelperPropsTheory.step_ISZERO >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule iszero_ptr_inst_ok >> simp[allocas_from_def, op_taint_def, FLOOKUP_UPDATE] >>
      goal_assum (drule_at Any)) >>
  simp[] >> drule iszero_ghost_update >> strip_tac >>
  gvs[DRESTRICT_DRESTRICT, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE] >>
  qpat_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_ghost_update) >> simp[]
QED
