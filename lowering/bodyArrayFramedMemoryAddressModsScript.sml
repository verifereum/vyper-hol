(* The fixed memory selector preserves the captured operand's provenance. *)
Theory bodyArrayFramedMemoryAddressMods
Ancestors
  bodyFullSubscriptArrayCodeBounds bodyFullSubscriptArrayCodeOps
  exprSimArrayIndex exprLoweringProps compileEnv loweringShapeDefs
  fragGasOriginPtrLoop fragGasOriginPtr fragExec bodyPtrDefs ptrDiscipline
  loweringPosts venomState words finite_map pair

Theorem fixed_bounds_compiler_extends[local]:
  array_bounds_check idx len sgn sa = ((),sc) ==> ci_mono sa sc
Proof
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_valid _ _ _ sa = (valid,sv)` >>
  `ci_mono sa sv` by
    (qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     Cases_on `sgn` >> simp[array_bounds_valid_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     metis_tac[ci_mono_emit_op, SND, ci_mono_trans]) >>
  metis_tac[ci_mono_emit_void, SND, ci_mono_trans]
QED

Theorem framed_memory_fixed_address_run:
  array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc) /\
  emit_op MUL [idx;Lit (n2w elem_size)] sc = (Var offset,sm) /\
  emit_op ADD [base_op;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q ==> not_fresh_at sa q) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  idx_in_range sgn (n2w i:bytes32) (n2w n) ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov G base_op /\
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
  strip_tac >> drule_then assume_tac fixed_bounds_compiler_extends >>
  `ci_mono sc sm /\ ci_mono sm sb` by metis_tac[ci_mono_emit_op, SND] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\ op_prov G (Lit (n2w n)) = NONE /\
   (!q. idx = Var q \/ Lit (n2w n) = Var q ==> not_fresh_at sa q) /\
   (!l. idx <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all array_bounds_check_read_only_joint_ok_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac)) >>
  `eval_operand base_op s1 = SOME a /\ op_taint tn1 base_op = {} /\
   op_prov G1 base_op = op_prov G base_op` by
    (Cases_on `base_op` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by
    (Cases_on `idx` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `!q. base_op = Var q ==> not_fresh_at sc q` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (`allocas_below_fmp s1 <=> allocas_below_fmp s` by simp[allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  drule_all scalar_mul_add_joint_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac)) >>
  qexistsl [`G2`,`tn2`,`s2`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      irule gas_origin_ptr_path_trans >> qexistsl [`G1`,`s1`,`tn1`] >>
      gvs[allocas_from_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sc q` by metis_tac[ci_mono_def, not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sc` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED
