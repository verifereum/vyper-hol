(* Optional raw_call GAS: a single endpoint and ghost pair, before horizons. *)
Theory bodyFullRawCallGas
Ancestors
  generatedGasOrigin bodyPtrEnvBuiltinsGas bodyPtrEnvBuiltinsEdges
  bodyMemBiEnvMsgGas fragGasSeqPtr fragGasOriginPtr bodyPtrDefs
  ptrDiscipline ptrSafeRun gasShadowState gasShadowUnit gasExplicitSites
  allocaHistory exprLoweringProps exprSimProps loweringStateRelDefs
  exprLowering compileEnv emitHelper msgGasSim
  venomInst venomState venomExecSemantics memSafeRun
  vyperStorageTrace finite_map pred_set list codegenRel decoderGhostFramePtr
  vyperTypeSystem

Theorem raw_call_optional_gas_joint:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  (case shadow_go of SOME g => (g,shadow_sa) |
     NONE => emit_op GAS [] shadow_sa) = (shadow_gas,shadow_sb) /\
  (IS_NONE go <=> IS_NONE shadow_go) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H)) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!g. go = SOME g ==> ?w. eval_operand g s = SOME w /\
    op_taint tn g = {} /\ op_prov G g = NONE) ==>
  ?t G6 tn6 gw.
    (case go of SOME _ => t = s /\ G6 = G /\ tn6 = tn |
       NONE => gas_prefix 1 s.vs_gas_readings = [gw] /\
         t = update_var (FST (fresh_var sa)) gw
           (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                     vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
         G6 = step_prov PG G
           (mk_inst sa.cs_next_id GAS [] [FST (fresh_var sa)])
           (update_var (FST (fresh_var sa)) gw
             (s with vs_gas_readings := DROP 1 s.vs_gas_readings)) /\
         tn6 = step_taint (mk_inst sa.cs_next_id GAS [] [FST (fresh_var sa)]) s
           (update_var (FST (fresh_var sa)) gw
             (s with vs_gas_readings := DROP 1 s.vs_gas_readings)) tn) /\
    eval_operand gas t = SOME gw /\ op_taint tn6 gas = {} /\
    op_prov G6 gas = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_gas_readings = DROP (if IS_NONE go then 1 else 0) s.vs_gas_readings /\
    alloca_history func t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    tn6.t_mem = tn.t_mem /\ tn6.t_stor = tn.t_stor /\
    tn6.t_trans = tn.t_trans /\ tn6.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G6 x = FLOOKUP G x /\
      op_taint tn6 (Var x) = op_taint tn (Var x)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path
        (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) (case go of SOME _ => [] | NONE => [F]) (OK t,G6,tn6) /\
      ghost_inv_at (DF H) lo d cenv cx es G6 tn6 t /\
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_kept_at lo cenv es sa G tn s G6 tn6)
Proof
  Cases_on `go` >> strip_tac
  >- (Cases_on `shadow_go` >> gvs[] >>
      drule_all compile_generated_gas_origin_path >>
      disch_then (qspec_then `T` strip_assume_tac) >>
      `?out bb. gas = Var out /\
        sb.cs_current_bb = sa.cs_current_bb /\
        LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
        lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH sa.cs_current_insts) =
          SOME (mk_inst sa.cs_next_id GAS [] [out]) /\
        out = FST (fresh_var sa)` by
        (irule emit_gas_placement_id >> simp[]) >>
      gvs[] >>
      qabbrev_tac `out = FST (fresh_var sa)` >>
      qabbrev_tac `inst = mk_inst sa.cs_next_id GAS [] [out]` >>
      qabbrev_tac `u = update_var out w
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
      `~not_fresh_at sa out` by simp[Abbr `out`, fresh_var_def, not_fresh_at_def] >>
      `(step_taint inst s u tn).t_mem = tn.t_mem` by
        (irule step_taint_no_memory_effect >>
         simp[Abbr `inst`, Abbr `u`, source_memory_write_ranges_def,
           written_taint_def, mk_inst_def, update_var_def]) >>
      `(step_taint inst s u tn).t_stor = tn.t_stor /\
       (step_taint inst s u tn).t_trans = tn.t_trans /\
       (step_taint inst s u tn).t_imm = tn.t_imm` by
        (irule step_taint_nonmemory_frame >> simp[Abbr `inst`, mk_inst_def]) >>
      `compile_env_var MsgGas sa = (Var out,sb)` by
        simp[compile_env_var_def, Abbr `out`] >>
      drule_all compile_msg_gas_history >>
      disch_then (qspec_then `w` assume_tac) >>
      gvs[Abbr `out`, Abbr `inst`, Abbr `u`, update_var_def,
        eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
        scalar_builtin_output_clean, scalar_builtin_output_no_prov] >>
      conj_asm1_tac
      >- (rpt strip_tac >> `x <> FST (fresh_var sa)` by metis_tac[] >>
          simp[step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >>
      conj_tac >- suspend "gas_path" >>
      conj_tac
      >- (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
          goal_assum (drule_at Any) >> simp[] >>
          qexists_tac `sa` >> simp[lookup_var_def, FLOOKUP_UPDATE]) >>
      conj_tac >- suspend "state_frame" >>
      simp[ghost_kept_at_def] >> metis_tac[]) >>
  gvs[ghost_kept_at_def, gas_origin_ptr_path_rules]
QED

Resume raw_call_optional_gas_joint[gas_path]:
  qmatch_goalsub_abbrev_tac `step_prov PG G inst u` >>
  qmatch_goalsub_abbrev_tac `OK t` >>
  `t = u with vs_inst_idx := SUC s.vs_inst_idx` by
    simp[Abbr `t`, Abbr `u`] >>
  `step_inst_base inst s = OK u` by
    (mp_tac (Q.INST [`id` |-> `sa.cs_next_id`,
      `out` |-> `FST (fresh_var sa)`] gas_builtin_base_step) >>
     simp[Abbr `inst`, Abbr `u`, update_var_def] >> metis_tac[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >> irule ptr_inst_ok_scalar_builtin_at >>
     gvs[ghost_inv_at_def]) >>
  `gas_origin_ptr_edge
     (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s,G,tn)
     (if inst.inst_opcode = GAS then
        [(func.fn_name,inst.inst_id) IN gas_explicit_sites ctx shadow_ctx]
      else [])
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G inst u, step_taint inst s u tn)` by
    (irule straight_line_origin_ptr_edge >> fs[] >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `~t.vs_halted` by simp[Abbr `t`] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  simp[Abbr `inst`, mk_inst_def] >> strip_tac >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
  irule_at Any (cj 1 gas_origin_ptr_path_rules) >> gvs[]
QED

Resume raw_call_optional_gas_joint[state_frame]:
  cheat
QED

Finalise raw_call_optional_gas_joint
