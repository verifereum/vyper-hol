Theory requestCutStaticSuffix
Ancestors
  requestCutFrameReady requestCutPrimitiveReady cfgNormSupplySim
  dftStaticAbortCompletion dftGasSimLocalBoundary dftGasOracleDefs dftWf stepWriteFootprintBase
  fnBlockBodyHelpers fnBlockBodySteps oracleExecProps passSharedFrame opcodeClass
  venomExecProofs venomInstProps staticAbortDefs contextRawReachable
  stackPlanGen unitShapeDefs o1PassContract contextCodegenRel venomExecSemantics venomState venomInst venomWf
  finite_map list rich_list arithmetic

Theorem static_suffix_inst_ready[local]:
  wf_ssa fn /\ codegen_ready_fn fn /\ fn_shape_ok fn /\
  MEM bb fn.fn_blocks /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
  LENGTH (get_params bb.bb_instructions) <= s.vs_inst_idx /\
  supply_prefix_defined fn s /\
  (!i l. MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s.vs_labels l)) ==>
  inst_wf inst /\ inst_shape_ok inst /\ codegen_ready_inst inst /\
  inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode /\
  EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_opcode <> PHI` by
    (qpat_assum `inst = _` SUBST1_TAC >> irule phi_prefix_not_phi >>
     fs[codegen_ready_fn_def, wf_function_def, bb_well_formed_def] >> metis_tac[]) >>
  `canonical_param_prefix fn` by fs[codegen_ready_fn_def] >>
  drule_all non_param_insts_drop >> strip_tac >>
  `MEM inst (non_param_insts bb)` by
    (asm_rewrite_tac[] >>
     imp_res_tac LESS_EQ_EXISTS >>
     simp[MEM_EL] >>
     qexists_tac `s.vs_inst_idx - LENGTH (get_params bb.bb_instructions)` >>
     simp[EL_DROP] >> metis_tac[SUB_ADD, ADD_COMM]) >>
  `active_inst fn inst s` by (simp[active_inst_def] >> metis_tac[lookup_block_label]) >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)` by
    metis_tac[request_cut_operand_ready] >>
  fs[non_param_insts_def, MEM_FILTER, codegen_ready_fn_def, fn_shape_ok_def,
     fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem static_suffix_step[local]:
  static_abort_pair bb s.vs_inst_idx j /\ get_instruction bb s.vs_inst_idx = SOME inst ==>
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (s.vs_inst_idx < j ==>
    inst.inst_opcode <> CALL /\ inst.inst_opcode <> STATICCALL /\
    inst.inst_opcode <> DELEGATECALL /\ inst.inst_opcode <> CREATE /\
    inst.inst_opcode <> CREATE2) /\
  (s.vs_inst_idx = j ==> MEM inst.inst_opcode [SSTORE; TSTORE; LOG])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `s.vs_inst_idx = j`
  >- (fs[static_abort_pair_def] >>
      `inst = EL j bb.bb_instructions` by fs[get_instruction_def] >>
      gvs[is_terminator_def]) >>
  `s.vs_inst_idx < j` by (fs[static_abort_pair_def] >> decide_tac) >>
  qpat_x_assum `static_abort_pair _ _ _`
    (mp_tac o REWRITE_RULE [static_abort_pair_def]) >>
  disch_then (mp_tac o Q.SPECL [`s.vs_inst_idx`,`inst`] o cj 4) >>
  simp[]
QED

(* The pending static interval can reach an earlier assertion fault or
   its final static write. Neither path crosses an external request. *)
Theorem request_cut_static_suffix_abort:
  !n s inst.
    j = s.vs_inst_idx + n /\
    static_abort_pair bb s.vs_inst_idx j /\
    s.vs_call_ctx.cc_static /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\ wf_ssa fn /\ codegen_ready_fn fn /\ fn_shape_ok fn /\
    phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
    LENGTH (get_params bb.bb_instructions) <= s.vs_inst_idx /\
    supply_prefix_defined fn s /\
    (!i l. MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
      MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s.vs_labels l)) /\
    raw_reachable vs0 C fn inst s ==>
    ?i t a post.
      raw_reachable vs0 C fn i t /\ i.inst_opcode <> INVOKE /\
      step_inst 0 C i t = Abort a post /\ t.vs_requests = s.vs_requests
Proof
  Induct_on `n` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_inst_idx <= j /\ j < LENGTH bb.bb_instructions` by fs[static_abort_pair_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `active_inst fn inst s` by metis_tac[raw_reachable_active] >>
  `inst = EL s.vs_inst_idx bb.bb_instructions` by
    (fs[active_inst_def, codegen_ready_fn_def, wf_function_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> fs[fn_labels_def]) >>
     gvs[]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by simp[get_instruction_def] >>
  drule_all static_suffix_inst_ready >> strip_tac >>
  drule_all static_suffix_step >> strip_tac
  >- suspend "last" >>
  suspend "before"
QED

Resume request_cut_static_suffix_abort[last]:
  `s.vs_inst_idx = j` by decide_tac >>
  `MEM inst.inst_opcode [SSTORE; TSTORE; LOG]` by
    (qpat_assum `s.vs_inst_idx = j ==> _` irule >> first_assum ACCEPT_TAC) >>
  `IS_SOME (eval_operands inst.inst_operands s)` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >>
     simp_tac bool_ss [MEM] >> strip_tac >>
     gvs[compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def, eval_operands_IS_SOME_EVERY,
         EVERY_REVERSE, inst_wf_def, eval_operand_def]) >>
  mp_tac (Q.INST [`x` |-> `inst`, `ctx` |-> `C`, `fuel` |-> `0`]
    inv_reached_static_write_fails) >>
  impl_tac >- simp[] >>
  `inst.inst_opcode <> GAS` by fs[] >>
  `ev_step orc p d 0 C inst s = step_inst 0 C inst s` by
    (irule ev_step_ordinary >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ev_step _ _ _ _ _ _ _ = step_inst _ _ _ _`
    (fn th => PURE_REWRITE_TAC [th]) >> strip_tac >>
  qexistsl_tac [`inst`, `s`, `ExHalt_abort`, `halt_state (set_returndata [] s)`] >>
  pure_rewrite_tac [] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)
QED

Resume request_cut_static_suffix_abort[before]:
  `s.vs_inst_idx < j` by decide_tac >>
  `inst.inst_opcode <> RET` by (strip_tac >> gvs[is_terminator_def]) >>
  `!err. step_inst 0 C inst s <> Error err` by
    (gen_tac >> irule request_cut_primitive_no_error >> simp[]) >>
  Cases_on `step_inst 0 C inst s`
  >- suspend "next"
  >- (qpat_assum `step_inst 0 C inst s = Halt _`
        (mp_tac o MATCH_MP step_inst_halt_opcodes) >>
      strip_tac >> gvs[is_terminator_def])
  >- metis_tac[]
  >- metis_tac[step_inst_non_invoke, step_inst_base_no_intret] >>
  metis_tac[]
QED

Resume request_cut_static_suffix_abort[next]:
  rename1 `step_inst 0 C inst s = OK v` >>
  `v.vs_requests = s.vs_requests` by metis_tac[step_inst_noninvoke_oracle] >>
  `v.vs_call_ctx = s.vs_call_ctx` by metis_tac[step_inst_ok_preserves_call_ctx] >>
  `v.vs_labels = s.vs_labels` by metis_tac[step_inst_preserves_labels_always] >>
  `v.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `wf_function fn /\ fn_inst_wf fn` by fs[codegen_ready_fn_def] >>
  `supply_prefix_defined fn (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[supply_prefix_defined_step] >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `active_inst fn (EL (SUC s.vs_inst_idx) bb.bb_instructions)
    (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac) >>
  `raw_reachable vs0 C fn (EL (SUC s.vs_inst_idx) bb.bb_instructions)
    (v with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[raw_reachable_next] >>
  `static_abort_pair bb (SUC s.vs_inst_idx) j` by
    (qpat_x_assum `static_abort_pair _ _ _` mp_tac >>
     pure_rewrite_tac[static_abort_pair_def] >>
     strip_tac >> asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     rpt strip_tac >>
     `s.vs_inst_idx <= k` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!s inst. _`
    (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,
      `EL (SUC s.vs_inst_idx) bb.bb_instructions`] mp_tac) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [] >>
      qpat_assum `j = s.vs_inst_idx + SUC n` (fn th => rewrite_tac [GSYM th]) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  simp[]
QED

Finalise request_cut_static_suffix_abort
