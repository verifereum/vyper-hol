Theory gasFocusLowerDloadFrameHaltRow
Ancestors
  o1SafeUpto lowerDloadSafetyRelation lowerDloadTerminalObservation
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrCopiedSafety
  lowerDloadPtrMemoryRead concretizePtrDallocaHaltSteps
  concretizePtrDallocaObservationTransport concretizeLayoutCutSafe
  lowerDloadPtrRel lowerDloadRecursiveInterface lowerDloadSafetyKernel
  lowerDloadOracleCallAssembly lowerDloadSafetyAmbient lowerDloadOpaqueExecution
  lowerDloadPtrSupport lowerDloadPtrStatic lowerDloadPtrCall
  unitShapeDefs contextCodegenRel ptrDiscipline o1PassContract opcodeClass
  concretizeLayoutLocalReturn venomInst venomState venomExecSemantics
  pointerConfinedDefs memLocDefs pred_set list arithmetic finite_map words

Theorem ld_focus_frame_halt_row:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\ dead_wf D /\
  dload_boundary_core (dyn_floor C vs) lo rs
    (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
    PG PH G H0 tn un0 s t0 stk ds /\
  ld_prefix C' gn X p h t0 t /\ ti = EL h X /\
  dload_prefix_match pfuel C' PH X h t0 H0 un0 t H un /\
  dload_control_match (HD frames).lf_supply fn gn s t inst X h /\
  s.vs_gas_readings = t0.vs_gas_readings /\ gas_cut n vs t /\
  ti.inst_opcode <> INVOKE /\ step_inst fuel C' ti t = Halt th ==>
  (step_taint ti t th un).t_stor SUBSET
    D.d_stor th.vs_call_ctx.cc_address
      (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
  (step_taint ti t th un).t_trans SUBSET
    D.d_trans th.vs_call_ctx.cc_address (th.vs_transient th.vs_call_ctx.cc_address) /\
  (step_taint ti t th un).t_imm SUBSET D.d_imm th.vs_immutables /\
  ret_taint un ti t SUBSET D.d_ret th.vs_returndata
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule dload_control_match_expansion >> strip_tac >>
  `MEM ti X` by metis_tac[EL_MEM] >>
  drule_all ld_supply_halt_singleton >> strip_tac >>
  `h = 0` by gvs[] >>
  gvs[ld_prefix_zero, dload_prefix_match_def] >>
  drule ld_sync_source >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `FDOM G SUBSET fn_pv P fn` by
    (drule frame_reachable_prov_supported >>
     disch_then (qspec_then `P` mp_tac) >>
     fs[ld_sync_def, EVERY_MEM]) >>
  drule_all ld_sync_fn_shape >>
  disch_then (strip_assume_tac o MATCH_MP o1_fn_shape_components) >>
  `opaque_use_ok fn` by fs[fn_shape_ok_def] >>
  Q.SUBGOAL_THEN
    `inst.inst_opcode = STOP \/ inst.inst_opcode = SINK \/
     inst.inst_opcode = SELFDESTRUCT \/ inst.inst_opcode = RETURN`
    assume_tac
  >- metis_tac[step_inst_halt_opcodes] >>
  `!v. MEM (Var v) inst.inst_operands ==>
       v IN set (fn_ir_vars fn) DIFF {v | retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     conj_tac >- metis_tac[fn_ir_vars_operand] >>
     irule ld_retpc_observable_operand >> simp[] >>
     qexists `inst` >> fs[MEM]) >>
  `~in_revert_forward fn s` by
    (irule active_inst_not_revert_forward >>
     simp[fn_labels_def, MEM] >> qexists `inst` >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> fs[MEM]) >>
  qpat_x_assum `o1_safe_upto D lo n C vs`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE [o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  drule_all ptr_discipline_upto_at >> strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     qpat_x_assum `taint_ok fn tn inst s` mp_tac >>
     simp[taint_ok_def] >> metis_tac[]) >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [dload_boundary_core_def]) >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_labels = t.vs_labels /\
   s.vs_returndata = t.vs_returndata` by
    (qpat_x_assum `dload_equal_environment s t`
       (mp_tac o AP_TERM ``\u:venom_state. (u.vs_call_ctx,u.vs_labels,u.vs_returndata)`` o
        REWRITE_RULE [dload_equal_environment_def]) >> simp[]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  `!op. MEM op inst.inst_operands ==>
        (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule dload_matched_operand_defined >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands /\ op_prov G op = NONE ==>
        eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule scalar_operand_equal >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!op. ((inst.inst_opcode = SELFDESTRUCT /\ MEM op inst.inst_operands) \/
         (inst.inst_opcode = RETURN /\ ?addr. inst.inst_operands = [addr;op])) ==>
        op_prov G op = NONE` by
    (rpt strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
     rename1 `FLOOKUP G v = NONE` >> Cases_on `FLOOKUP G v` >> simp[] >>
     `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _`
       (qspec_then `v` mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_use_ok_def]) >>
     gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def,
         Excl "FILTER"] >>
     simp[FILTER] >> rpt IF_CASES_TAC >> gvs[]) >>
  `?sh. step_inst fuel C inst s = Halt sh /\
        final_taint vs C sh (step_taint inst s sh tn) (ret_taint tn inst s) /\
        ret_taint un inst t SUBSET ret_taint tn inst s /\
        LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
        (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
             EL i sh.vs_returndata = EL i th.vs_returndata)` by
    (irule ptr_dalloca_halt_step >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (goal_assum (drule_at Any) >> metis_tac[]) >>
     conj_tac >- suspend "return_payload" >>
     conj_tac
     >- (strip_tac >> irule eval_operands_agree >> metis_tac[]) >>
     metis_tac[]) >>
  suspend "final_transport"
QED

Resume ld_focus_frame_halt_row[return_payload]:
  strip_tac >>
  `step_inst_base inst t = Halt th` by metis_tac[step_inst_non_invoke] >>
  drule_all return_execution_envelope >>
  disch_then (qx_choose_then `ad` (qx_choose_then `szop`
    (qx_choose_then `offt` (qx_choose_then `sz` strip_assume_tac)))) >>
  `eval_operand szop s = SOME sz` by metis_tac[MEM] >>
  `?off. eval_operand ad s = SOME off` by
    (Cases_on `eval_operand ad s` >> simp[] >> gvs[MEM]) >>
  qexistsl [`ad`,`szop`,`ad`,`szop`,`off`,`offt`,`sz`] >> simp[] >>
  Cases_on `w2n sz = 0` >> simp[] >>
  `MEM (w2n offt,w2n sz) (source_memory_read_ranges inst t)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `inst.inst_opcode <> DRET` by simp[] >>
  drule_all dload_copied_read_range >> simp[] >>
  disch_then (qx_choose_then `a`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
  `a = w2n off` by
    (qpat_x_assum `MEM (a,_) (source_memory_read_ranges inst s)` mp_tac >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  `!k. k < w2n sz ==>
       (a+k IN tn.t_mem <=> w2n offt+k IN un.t_mem) /\
       (a+k NOTIN tn.t_mem ==>
        read_byte (a+k) s.vs_memory = read_byte (w2n offt+k) t.vs_memory)` by
    (match_mp_tac (GEN_ALL dload_memory_read_bytes) >>
     goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[ADD_COMM]
QED

Resume ld_focus_frame_halt_row[final_transport]:
  drule_all taint_within_upto_halt >> strip_tac >>
  `sh.vs_call_ctx = s.vs_call_ctx /\
   (!a. (sh.vs_accounts a).storage = (s.vs_accounts a).storage) /\
   sh.vs_transient = s.vs_transient /\ sh.vs_immutables = s.vs_immutables /\
   (step_taint inst s sh tn).t_stor = tn.t_stor /\
   (step_taint inst s sh tn).t_trans = tn.t_trans /\
   (step_taint inst s sh tn).t_imm = tn.t_imm` by
    (irule ld_noninvoke_halt_persistent >> metis_tac[]) >>
  `th.vs_call_ctx = t.vs_call_ctx /\
   (!a. (th.vs_accounts a).storage = (t.vs_accounts a).storage) /\
   th.vs_transient = t.vs_transient /\ th.vs_immutables = t.vs_immutables /\
   (step_taint inst t th un).t_stor = un.t_stor /\
   (step_taint inst t th un).t_trans = un.t_trans /\
   (step_taint inst t th un).t_imm = un.t_imm` by
    (irule ld_noninvoke_halt_persistent >> metis_tac[]) >>
  irule ptr_dalloca_final_taint_transport >>
  goal_assum (drule_at Any) >>
  qexistsl [`ret_taint tn inst s`, `sh`, `tn`] >>
  qpat_x_assum `dload_shared_store tn un s t`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [dload_shared_store_def]) >>
  qpat_x_assum `!a. _ /\ storage_agree_except _ _ _ /\ _`
    (qspec_then `t.vs_call_ctx.cc_address` mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  qpat_x_assum `!k x y. FLOOKUP _ k = SOME x /\ FLOOKUP _ k = SOME y ==> _`
    mp_tac >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Finalise ld_focus_frame_halt_row
