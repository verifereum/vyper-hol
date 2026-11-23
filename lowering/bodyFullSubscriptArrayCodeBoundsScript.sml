(* Read-only array bounds suffixes, with one endpoint at every horizon. *)
Theory bodyFullSubscriptArrayCodeBounds
Ancestors
  bodyFullTargetArrayScalar bodyPtrSignedConvertSourceFrame fragGasCopyLoop fragGasCopySeqLiftProps
  augAssignPtrScalarRun augAssignPtrScalarCertificate fragGasOriginPtrDead
  fragGasSeqPtr fragGasOriginPtr fragExecMem fragExec memSafeRun
  exprSimArrayIndex emitHelper freshWrites compileEnv loweringStateRelDefs
  ptrDiscipline venomState venomInst venomExecSemantics finite_map pred_set list rich_list
  exprLoweringProps unitTransformDefs contextCodegenRel codegenRel

Theorem bounds_suffix_layout[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA /\
              ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
              i.inst_opcode <> DALLOCA)
    (emitted_insts sa sb) /\
  scalar_code {v | idx = Var v \/ len = Var v} (emitted_insts sa sb) /\
  writes_fresh sa (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  irule_at Any run_inst_seq_mem_ok_every >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def, scalar_code_def, scalar_shape_def,
       scalar_binary_def, scalar_unary_def, scalar_available_def,
       writes_fresh_def, fresh_write_op_def, not_fresh_at_def] >>
  Cases_on `idx` >> Cases_on `len` >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]
QED

(* Take the physical run from the receiver's nonalias result. Certify the
   same instruction list at bound zero, then lift its fixed ghost endpoint.
   On failure the cursor is selected by the executed prefix, not by lo. *)
Theorem bounds_suffix_uniform[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        ((if idx_in_range sgn a b then OK sf else Abort Revert_abort sf),Gf,tnf)) /\
    (idx_in_range sgn a b ==>
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (sf with vs_vars := s.vs_vars) = s with vs_inst_idx := sf.vs_inst_idx) /\
    (~idx_in_range sgn a b ==>
      (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
      revert_state (set_returndata [] s)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule_all bounds_suffix_layout >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  `(!x. idx = Var x ==> not_fresh_at sa x) /\
   (!x. len = Var x ==> not_fresh_at sa x)` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_CONJ] >>
  drule_all (array_bounds_check_nonalias_uniform |> Q.INST [`lo` |-> `0`]) >>
  disch_then (qspecl_then [`{}`, `PG`]
    (qx_choosel_then [`t`, `j0`, `unused_G`, `unused_tn`] strip_assume_tac)) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` kall_tac >>
  qabbrev_tac `code = emitted_insts sa sb` >>
  qabbrev_tac `A = {v | idx = Var v \/ len = Var v}` >>
  `!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by
    (simp[Abbr `A`] >> metis_tac[]) >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                      d_imm := K {}; d_ret := K {}|>` >>
  `?Gf tnf. inst_seq_ptr D0 0 ctx func PG G tn code s Gf tnf` by
    (irule scalar_code_inst_seq_ptr >> metis_tac[]) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  `!q. not_fresh_at sa q ==> ~MEM q (FLAT (MAP (\i. i.inst_outputs) code))` by
    (gvs[writes_fresh_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     metis_tac[DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `EVERY (\i. _ /\ _ /\ _ /\ _ /\ i.inst_opcode <> DALLOCA) code` mp_tac >>
     simp[EVERY_APPEND]) >>
  Cases_on `idx_in_range sgn a b` >> gvs[]
  >- (qexistsl [`Gf`,`tnf`,`t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
      conj_tac
      >- (rpt strip_tac >> irule gas_origin_ptr_path_from_no_dead >>
          `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH code` by
            (simp[] >> metis_tac[LENGTH_APPEND]) >>
          qpat_assum `LENGTH sb.cs_current_insts = _` (rewrite_tac o single) >>
          `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                     i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
            fs[EVERY_MEM] >>
          irule (cj 1 run_inst_seq_origin_ptr_lift) >>
          gvs[Abbr `D0`] >> metis_tac[]) >>
      fs[venom_state_component_equality, lookup_var_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) code` by fs[EVERY_CONJ] >>
  qspecl_then [`code`,`s`,`Revert_abort`,`t`,`ctx`,`func`,`bb`] mp_tac
    run_inst_seq_abort_origin_ptr_uniform >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `j` assume_tac) >>
  qexistsl [`Gf`,`tnf`,`t with vs_inst_idx := j`] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_from_no_dead >>
      gvs[Abbr `D0`] >> first_assum irule >>
      irule (inst_seq_ptr_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
      simp[]) >>
  fs[revert_state_def, set_returndata_def, venom_state_component_equality,
     lookup_var_def] >> metis_tac[]
QED

Theorem array_bounds_check_read_only_joint_ok_frame:
  array_bounds_check idx len sgn sa = ((),sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  idx_in_range sgn a b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\ sf.vs_accounts = s.vs_accounts /\
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
  strip_tac >> drule_all bounds_suffix_uniform >>
  disch_then (qspec_then `PG` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac) >>
  drule_all bounds_suffix_layout >> strip_tac >>
  qexistsl [`Gf`,`tnf`,`sf`] >>
  `sf = s with <|vs_vars := sf.vs_vars; vs_inst_idx := sf.vs_inst_idx|>` by
    fs[venom_state_component_equality] >>
  `!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
     local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf` by
    (rpt strip_tac >> irule stmt_state_rel_readonly_vars_pc >>
     qexistsl [`s`,`sa`] >> metis_tac[]) >>
  fs[venom_state_component_equality]
QED

Theorem array_bounds_check_joint_oob_frame:
  array_bounds_check idx len sgn sa = ((),sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  ~idx_in_range sgn a b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort sf,Gf,tnf)) /\
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
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule_all bounds_suffix_uniform >>
  disch_then (qspec_then `PG` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac) >>
  qexistsl [`Gf`,`tnf`,`sf`] >>
  fs[revert_state_def, set_returndata_def, venom_state_component_equality]
QED
