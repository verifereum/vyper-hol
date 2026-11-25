(* Runtime-code dynamic selector, starting after the header load. *)
Theory bodyArrayFramedCodeDynamicMods
Ancestors
  bodyFullSubscriptArrayCodeBounds bodyFullSubscriptArrayCodeOps
  allocasBelowFmpUpdatesProps exprSimArrayIndex exprLoweringProps
  loweringShapeRules loweringShapeDefs compileEnv fragGasOriginPtrLoop
  fragExec ptrDiscipline venomState words finite_map pair

Theorem dynamic_bounds_next_var[local]:
  array_bounds_check iop lop signed sa = ((),sc) ==>
  sa.cs_next_var <= sc.cs_next_var
Proof
  strip_tac >>
  `ci_mono sa sc` suffices_by simp[ci_mono_def] >>
  pop_assum (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
  Cases_on `signed` >> simp[NoAsms, array_bounds_check_def, array_bounds_valid_def] >>
  rpt (irule ci_mono_bind >> conj_tac >> rpt gen_tac >>
       simp[NoAsms, ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return])
QED

Theorem dynamic_address_emit_cuts[local]:
  array_elem_ptr bop iop T 32 elemBytes sc = (dst,sb) ==>
  ?sm sn data offset out.
    emit_op ADD [bop;Lit 32w] sc = (Var data,sm) /\
    emit_op MUL [iop;Lit (n2w elemBytes)] sm = (Var offset,sn) /\
    emit_op ADD [Var data;Var offset] sn = (Var out,sb) /\ dst = Var out
Proof
  simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[] >>
  qpat_assum `emit_op ADD [Var _;Var _] _ = _`
    (mp_then Any strip_assume_tac emit_op_facts) >> gvs[]
QED

Theorem framed_code_dynamic_address_mods:
  array_bounds_check iop lop signed sa = ((),sc) /\
  array_elem_ptr bop iop T 32 elemBytes sc = (dst,sb) /\
  fn_has_code sa sc func /\ fn_has_code sc sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand bop s = SOME w /\ op_taint tn bop = {} /\ op_prov G bop = NONE /\
  eval_operand iop s = SOME iw /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  eval_operand lop s = SOME len /\ op_taint tn lop = {} /\ op_prov G lop = NONE /\
  (!q. bop = Var q ==> not_fresh_at sa q) /\ (!l. bop <> Label l) /\
  (!q. iop = Var q \/ lop = Var q ==> not_fresh_at sa q) /\
  (!l. iop <> Label l /\ lop <> Label l) /\
  idx_in_range signed iw len ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand dst sf = SOME (w + n2w (32 + w2n iw * elemBytes)) /\
    op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >> drule_then assume_tac dynamic_bounds_next_var >>
  drule_then strip_assume_tac dynamic_address_emit_cuts >>
  `!l. iop <> Label l` by (rpt strip_tac >> first_x_assum (qspec_then `l` mp_tac) >> simp[]) >>
  drule_all array_bounds_check_read_only_joint_ok_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac)) >>
  `eval_operand bop s1 = SOME w /\ op_taint tn1 bop = {} /\ op_prov G1 bop = NONE` by
    (Cases_on `bop` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `eval_operand iop s1 = SOME iw /\ op_taint tn1 iop = {} /\ op_prov G1 iop = NONE` by
    (Cases_on `iop` >> gvs[DISJ_IMP_THM, eval_operand_def, op_taint_def, op_prov_def]) >>
  `!q. iop = Var q ==> not_fresh_at sc q` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> fs[DISJ_IMP_THM]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (`allocas_below_fmp s1 <=> allocas_below_fmp s` by
       (irule allocas_below_fmp_fields >> simp[]) >> asm_rewrite_tac[]) >>
  drule_all (Q.INST [`i` |-> `w2n (iw:bytes32)`] code_dynamic_address_joint_frame |> SRULE []) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac)) >>
  qexistsl [`G2`,`tn2`,`s2`] >> simp[eval_operand_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `allocas_from lo s1` by (simp[allocas_from_def] >> fs[allocas_from_def] >> metis_tac[]) >>
      irule gas_origin_ptr_path_trans >> qexistsl [`G1`,`s1`,`tn1`] >>
      conj_tac >> first_assum irule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> `not_fresh_at sc q` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >> metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s1` by metis_tac[] >>
  metis_tac[]
QED
