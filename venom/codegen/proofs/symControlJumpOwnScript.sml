(* JMP/JNZ kernels at supplied label offsets, shared by both modes. *)
Theory symControlJumpOwn
Ancestors
  codegenSymRel codegenSymOwnRel symFrameControlFacts symControlPrefixOwn
  fnFrameDeepJmp fnFrameDeepJnz asmSymBridge asmSymSem asmSplice
  frameRel contextCodegenRel unitShapeDefs stackPlanGen stackPlanTypes
  planExec asmSem venomExecSemantics venomState venomInst dfgDefs
  symPlannerSim symShuffleSim asmSymPc codegenEncodingWf symPostfixSim symInstPrefixOwn fnFrameDeepAbort

(* Syntax abbreviations, not logical definitions. *)
val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val _ = Parse.temp_overload_on ("control_frame", ``\lo code_ok p ctx cp fn ret srest labs0 ps cs ss.
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);

Theorem sym_jnz_condition_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
  ~is_label_operand cond_op /\ cond_op <> dead_stack_marker /\
  op_kind_ok fn ret cond_op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >> Cases_on `cond_op` >>
  gvs[op_kind_ok_def, is_label_operand_def] >>
  rename1 `Var x <> dead_stack_marker` >>
  `~retpc_var fn x` by
    (fs[fn_shape_ok_def, opaque_use_ok_def] >>
     first_x_assum (qspec_then `inst` mp_tac) >> simp[retpc_use_ok_def]) >>
  `~code_end_var fn x` by
    (Cases_on `allow_own` >> gvs[label_flow_ok_def, label_flow_own_ok_def] >>
     first_x_assum (qspecl_then [`fn`, `inst`] mp_tac) >> simp[]) >>
  gvs[]
QED

Theorem sym_code_label_dest_reloc_conditional:
  (!l off pc. MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
    sym_jump_dest p (Lab l 0) = SOME pc) /\
  MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
  sym_jump_dest p (Lab l 0) = SOME pc
Proof
  metis_tac[]
QED

Theorem sym_jump_steps_mode:
  asm_block_at p ss.sym_base.as_pc [AsmOp "JUMP"] /\
  ss.sym_stack = Lab l 0 :: stk /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps_mode allow_own p env own 1 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  strip_tac >> irule sym_steps_mode_ok >>
  rewrite_tac[arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[asm_block_at_def, sym_step_def, sym_step_op_def, sym_jump_def]
QED

Theorem sym_jmp_suffix_mode:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps_mode allow_own p env own 2 ss =
    SymOK (ss with sym_base := ss.sym_base with as_pc := pc)
Proof
  strip_tac >> irule sym_steps_mode_ok >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons, sym_step_def, sym_step_op_def,
      sym_set_stack_def, asm_next_def, sym_jump_def]
QED

Theorem sym_jnz_suffix_nonzero_mode:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l; AsmOp "JUMPI"] /\
  ss.sym_stack = Val w :: stk /\ w <> 0w /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps_mode allow_own p env own 2 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  strip_tac >> irule sym_steps_mode_ok >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons, sym_step_def, sym_step_op_def,
      sym_set_stack_def, asm_next_def, sym_jumpi_def]
QED

Theorem sym_jnz_suffix_zero_mode:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  ss.sym_stack = Val 0w :: stk /\
  sym_jump_dest p (Lab lz 0) = SOME pc ==>
  sym_steps_mode allow_own p env own 4 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  strip_tac >> irule sym_steps_mode_ok >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons, sym_step_def, sym_step_op_def,
      sym_set_stack_def, asm_next_def, sym_jumpi_def, sym_jump_def]
QED

Theorem sym_jnz_suffix_steps_mode:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  ss.sym_stack = Val w :: stk /\
  sym_jump_dest p (Lab ln 0) = SOME pn /\
  sym_jump_dest p (Lab lz 0) = SOME pz ==>
  sym_steps_mode allow_own p env own (if w = 0w then 4 else 2) ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc :=
      (if w = 0w then pz else pn); sym_stack := stk|>)
Proof
  strip_tac >>
  `asm_block_at p ss.sym_base.as_pc [AsmPushLabel ln; AsmOp "JUMPI"]` by
    fs[stackOpSimTheory.asm_block_at_cons] >>
  Cases_on `w = 0w` >- metis_tac[sym_jnz_suffix_zero_mode] >>
  simp[] >> drule_all sym_jnz_suffix_nonzero_mode >> simp[]
QED

Theorem sym_jmp_suffix_frame_sim_mode_conditional:
  !cp.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc [AsmPushLabel l; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p 2 cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs' ss' /\
    cs'.as_pc = pc
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `sym_steps_mode allow_own p env own 2 ss =
     SymOK (ss with sym_base := ss.sym_base with as_pc := pc)` by
    (irule sym_jmp_suffix_mode >> metis_tac[]) >>
  qpat_x_assum `!n cs ss ss'. _`
    (drule_all_then (qx_choose_then `cs'` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `cs'.as_pc = pc` by
    (qpat_x_assum `?m. (ss with sym_base := _).sym_base = _ /\ _` strip_assume_tac >>
     gvs[asm_state_component_equality]) >>
  qexistsl [`cs'`, `ss with sym_base := ss.sym_base with as_pc := pc`] >>
  fs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_jnz_suffix_frame_sim_mode_conditional:
  !cp.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  ps.ps_stack = tail ++ [cond] /\ ss.sym_stack = Val w :: stk /\
  asm_block_at p cs.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab ln 0) = SOME pn /\
  sym_jump_dest p (Lab lz 0) = SOME pz ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p (if w = 0w then 4 else 2) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (if w = 0w then 4 else 2) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0
      (ps with ps_stack := tail) cs' ss' /\
    cs'.as_pc = (if w = 0w then pz else pn)
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `sym_steps_mode allow_own p env own (if w = 0w then 4 else 2) ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc :=
      (if w = 0w then pz else pn); sym_stack := stk|>)` by
    (irule sym_jnz_suffix_steps_mode >> metis_tac[]) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  rename1 `sym_kinds_ok cplan fn ret srest ps ss` >>
  `sym_kinds_ok cplan fn ret srest (ps with ps_stack := tail)
    (ss with <|sym_base := ss.sym_base with as_pc :=
      (if w = 0w then pz else pn); sym_stack := stk|>)` by
    (gvs[sym_kinds_ok_def, listTheory.REVERSE_APPEND,
         listTheory.LIST_REL_CONS1]) >>
  qexistsl [`cs'`, `ss with <|sym_base := ss.sym_base with as_pc :=
    (if w = 0w then pz else pn); sym_stack := stk|>`] >>
  gvs[asm_state_component_equality] >> metis_tac[]
QED

Theorem sym_jmp_plan_decompose:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  inst.inst_outputs = [] /\
  lookup_block target fn.fn_blocks = SOME target_bb /\
  targets = MAP Var (input_vars_from lbl target_bb.bb_instructions
                       (live_vars_at lv target 0)) /\
  generate_inst_plan lv dfg cfg fn inst nl ih nit lbl ps = SOME (ops, qs) ==>
  ?rops prepared sops arranged.
    restore_spilled_plan targets ps = (rops, prepared) /\
    reorder_plan dfg targets prepared = (sops, arranged) /\
    ops = rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"] /\
    qs = release_dead_spills nl arranged
Proof
  strip_tac >>
  gvs[genFrameSimTheory.generate_inst_plan_jmp,
      generate_regular_inst_plan_def, compute_operands_def,
      asmIRTheory.get_non_label_operands_def, venomEffectsTheory.is_commutative_def,
      asmIRTheory.venom_to_evm_name_def, generate_emit_ops_def, stackModelTheory.stack_pop_def,
      join_target_ops_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem sym_jmp_plan_frame_sim_mode_conditional:
  !cplan base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!base pending ps restore_ops prepared reorder_ops arranged cs ss.
    generated_plan_state_wf_marked base ps /\ pending_inventory_wf pending ps /\
    restore_spilled_plan pending ps = (restore_ops,prepared) /\
    reorder_plan dfg pending prepared = (reorder_ops,arranged) /\
    (!off. MEM (SORestore off) restore_ops ==> off < dimword(:256)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) reorder_ops /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reorder_ops)) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own
        (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) ss = SymOK ss' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 arranged cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) /\
  (!l off pc. MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
    sym_jump_dest p (Lab l 0) = SOME pc) /\
  generated_plan_state_wf_marked base ps /\ pending_inventory_wf pending ps /\
  restore_spilled_plan pending ps = (rops,prepared) /\
  reorder_plan dfg pending prepared = (sops,arranged) /\
  ops = rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"] /\
  qs = release_dead_spills nl arranged /\
  (!off. MEM (SORestore off) rops ==> off < dimword(:256)) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ MEM (AsmLabel target) p /\
  FLOOKUP lo target = SOME off /\ FLOOKUP (build_offset_to_pc p) off = SOME pc /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?ac sy.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK ac /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK sy /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 qs ac sy /\ ac.as_pc = pc
Proof
  qx_gen_tac `cplan` >> qx_gen_tac `spillbase` >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `sym_jump_dest p (Lab target 0) = SOME pc` by metis_tac[] >>
  `execute_plan initial_fmp [SOPushLabel target; SOEmit "JUMP"] =
   [AsmPushLabel target; AsmOp "JUMP"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  `r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    gvs[allocMonoTheory.release_dead_spills_spill_base,
        allocMonoTheory.release_dead_spills_next_offset] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) sops` by
    gvs[listTheory.EVERY_APPEND] >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp (rops ++ sops))` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  qpat_x_assum `!base pending ps restore_ops prepared reorder_ops arranged cs ss. _`
    (drule_all_then (qx_choose_then `cs'` (qx_choose_then `ss'` assume_tac))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `asm_block_at p cs'.as_pc [AsmPushLabel target; AsmOp "JUMP"]` by
    (gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  drule_all_then (qx_choose_then `cs''` (qx_choose_then `ss''` assume_tac))
    sym_jmp_suffix_frame_sim_mode_conditional >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_then (qspec_then `nl` assume_tac) sym_kinds_ok_release_dead_spills >>
  `LENGTH (execute_plan initial_fmp ops) =
    LENGTH (execute_plan initial_fmp (rops ++ sops)) + 2` by
    (qpat_x_assum `ops = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp[NoAsms, stackOpSimTheory.execute_plan_append,
          execute_plan_def, exec_stack_op_def]) >>
  qexistsl [`cs''`, `ss''`] >>
  conj_tac
  >- (qpat_x_assum `LENGTH (execute_plan initial_fmp ops) = _` SUBST1_TAC >>
      pure_rewrite_tac[stackOpSimTheory.asm_steps_add] >>
      asm_rewrite_tac[] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `LENGTH (execute_plan initial_fmp ops) = _` SUBST1_TAC >>
      pure_rewrite_tac[sym_steps_mode_add] >> asm_rewrite_tac[] >> simp[]) >>
  metis_tac[]

QED

Theorem sym_jnz_arranged_word_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = JNZ /\ inst.inst_operands = [cond; Label ln; Label lz] /\
  ~is_label_operand cond /\ cond <> dead_stack_marker /\
  venom_asm_rel lo ps v mid /\ ps.ps_stack = tail ++ [cond] /\
  operand_val v lo cond = SOME w /\
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  ?stk. ss.sym_stack = Val w :: stk
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `mid.as_stack = [w] ++ DROP 1 mid.as_stack` by
    (fs[codegenRelTheory.venom_asm_rel_def, codegenRelTheory.plan_stack_rel_def] >>
     qpat_x_assum `!i. i < LENGTH tail + 1 ==> _` (qspec_then `0` mp_tac) >>
     Cases_on `mid.as_stack` >> gvs[listTheory.REVERSE_APPEND]) >>
  `?sv st. ss.sym_stack = sv :: st /\ op_kind_ok fn ret cond sv` by
    (gvs[sym_kinds_ok_def, listTheory.REVERSE_APPEND,
         listTheory.LIST_REL_CONS1]) >>
  `?u. sv = Val u` by (drule_all sym_jnz_condition_kind_mode >> simp[]) >>
  gvs[sval_conc_def] >>
  qpat_x_assum `mid.as_stack = _` SUBST_ALL_TAC >> gvs[]
QED

Theorem sym_jnz_prepare_frame_sim_mode_conditional:
  !base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  generated_plan_state_wf_marked base ps /\
  emit_input_plan JNZ [cond] nl ps = (iops, prepared) /\
  reorder_plan dfg [cond] prepared = (rops, arranged) /\
  ops = iops ++ rops ++ suffix /\
  (is_var_operand cond ==> IS_SOME (stack_get_depth cond ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled cond)) /\
  1 <= LENGTH prepared.ps_stack /\ cond <> dead_stack_marker /\
  (!at. operand_equiv dfg cond at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg cond at ==>
    operand_val (frame_view fn ra vs) lo cond =
    operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label ln; Label lz] /\ ~is_label_operand cond /\
  operand_val (frame_view fn ra vs) lo cond = SOME w /\
  asm_static_wf p /\ control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss ==>
  arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
  ?mid sy stk.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) cs = AsmOK mid /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss = SymOK sy /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 arranged mid sy /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    sy.sym_stack = Val w :: stk
Proof
  qx_gen_tac `spillbase` >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)` by
    (Cases_on `cond` >> gvs[is_label_operand_def]) >>
  `!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val (frame_view fn ra vs) lo at` by (simp[] >> metis_tac[]) >>
  `PERM [cond] [cond] /\ LENGTH [cond] <= 16 /\
    LENGTH [cond] <= LENGTH prepared.ps_stack /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond]` by
    (simp[] >> metis_tac[]) >>
  `arranged.ps_alloc.sa_spill_base = arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= arranged.ps_alloc.sa_next_offset` by simp[] >>
  `JNZ <> INVOKE /\
    (!op. MEM op [cond] /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op))` by simp[] >>
  drule_all frame_entry_selected_prefix_sim_marked >>
  disch_then (qspec_then `build_offset_to_pc p` strip_assume_tac) >>
  `!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[deepInstSimTheory.marked_operand_owned] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps` by
    metis_tac[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
      deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base` by
    metis_tac[allocMonoTheory.reorder_plan_spill_base,
      allocMonoTheory.emit_input_plan_spill_base] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
    asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  drule_all sym_selected_prefix_frame_sim_marked_mode_conditional >> strip_tac >>
  `operand_val (frame_view fn ra vs with vs_memory := cs.as_memory) lo cond = SOME w` by
    simp[genFrameSimTheory.operand_val_memory_update] >>
  `cs' = mid with as_stack := mid.as_stack ++ rest` by
    (qpat_x_assum `asm_steps _ _ _ _ _ = AsmOK cs'` mp_tac >> simp[]) >>
  `arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond]` by fs[] >>
  `?stk. ss'.sym_stack = Val w :: stk` by
    (drule_at (Pat `venom_asm_rel _ _ _ _`) sym_jnz_arranged_word_mode >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `operand_val _ _ _ = _`)) >>
     simp[] >>
     disch_then irule >> simp[] >>
     conj_tac >- (qexists `code_ok` >> fs[]) >>
     conj_tac >- fs[] >>
     conj_tac >- (qexists `m` >> fs[]) >>
     conj_tac >- (qexists `stack_pop 1 arranged.ps_stack` >> simp[]) >>
     conj_tac >- (qexistsl [`inst`, `ln`, `lz`] >> simp[]) >>
     conj_tac >- (qexistsl [`allow_own`, `ctx`] >> simp[]) >>
     qexists `rest` >> fs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cs'`, `ss'`, `stk`] >> simp[] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

Theorem sym_jnz_plan_frame_sim_mode_conditional:
  !base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!l off pc. MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
    sym_jump_dest p (Lab l 0) = SOME pc) /\
  generated_plan_state_wf_marked base ps /\
  emit_input_plan JNZ [cond] nl ps = (iops, prepared) /\
  reorder_plan dfg [cond] prepared = (rops, arranged) /\
  ops = iops ++ rops ++ [SOPushLabel ln; SOEmit "JUMPI"; SOPushLabel lz; SOEmit "JUMP"] /\
  final = release_dead_spills nl (arranged with ps_stack := stack_pop 1 arranged.ps_stack) /\
  (is_var_operand cond ==> IS_SOME (stack_get_depth cond ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled cond)) /\
  1 <= LENGTH prepared.ps_stack /\ cond <> dead_stack_marker /\
  (!at. operand_equiv dfg cond at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg cond at ==>
    operand_val (frame_view fn ra vs) lo cond =
    operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = JNZ /\ inst.inst_operands = [cond; Label ln; Label lz] /\
  ~is_label_operand cond /\ operand_val (frame_view fn ra vs) lo cond = SOME w /\
  MEM (AsmLabel ln) p /\ MEM (AsmLabel lz) p /\
  FLOOKUP lo ln = SOME offn /\ FLOOKUP (build_offset_to_pc p) offn = SOME pn /\
  FLOOKUP lo lz = SOME offz /\ FLOOKUP (build_offset_to_pc p) offz = SOME pz /\
  asm_static_wf p /\ control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss ==>
  ?ac sy.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
        (if w = 0w then 4 else 2)) cs = AsmOK ac /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
        (if w = 0w then 4 else 2)) ss = SymOK sy /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 final ac sy /\
    ac.as_pc = (if w = 0w then pz else pn)
Proof
  qx_gen_tac `spillbase` >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    gvs[allocMonoTheory.release_dead_spills_spill_base,
        allocMonoTheory.release_dead_spills_next_offset] >>
  drule_all_then assume_tac sym_jnz_prepare_frame_sim_mode_conditional >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `?mid sy stk. _`
    (qx_choose_then `mid` (qx_choose_then `sy` (qx_choose_then `stk` assume_tac))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `sym_jump_dest p (Lab ln 0) = SOME pn /\
   sym_jump_dest p (Lab lz 0) = SOME pz` by metis_tac[] >>
  `asm_block_at p mid.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"]` by
    (qpat_x_assum `asm_block_at p cs.as_pc _` mp_tac >>
     simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
          execute_plan_def, exec_stack_op_def]) >>
  drule_all_then assume_tac sym_jnz_suffix_frame_sim_mode_conditional >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `?cs' ss'. _` strip_assume_tac >>
  drule_then (qspec_then `nl` assume_tac) sym_kinds_ok_release_dead_spills >>
  qexistsl [`cs'`, `ss'`] >>
  conj_tac >- (pure_rewrite_tac[stackOpSimTheory.asm_steps_add] >> asm_rewrite_tac[] >> simp[]) >>
  conj_tac >- (pure_rewrite_tac[sym_steps_mode_add] >> asm_rewrite_tac[] >> simp[]) >>
  metis_tac[]
QED

Theorem sym_jmp_frame_sim_deep_mode_conditional:
  !fuel cplan base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!base pending ps restore_ops prepared reorder_ops arranged cs ss.
    generated_plan_state_wf_marked base ps /\ pending_inventory_wf pending ps /\
    restore_spilled_plan pending ps = (restore_ops,prepared) /\
    reorder_plan dfg pending prepared = (reorder_ops,arranged) /\
    (!off. MEM (SORestore off) restore_ops ==> off < dimword(:256)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) reorder_ops /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp (restore_ops ++ reorder_ops)) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan cplan.cp_initial_fmp (restore_ops ++ reorder_ops))) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own
        (LENGTH (execute_plan cplan.cp_initial_fmp (restore_ops ++ reorder_ops))) ss = SymOK ss' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 arranged cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (restore_ops ++ reorder_ops))) /\
  (!l off pc. MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
    sym_jump_dest p (Lab l 0) = SOME pc) /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\ inst.inst_outputs = [] /\
  lookup_block target fn.fn_blocks = SOME target_bb /\
  target_stack = MAP Var (input_vars_from bb_label target_bb.bb_instructions
    (live_vars_at liveness target 0)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  (!off. MEM (SORestore off) (FST (restore_spilled_plan target_stack ps)) ==>
    off < dimword(:256)) /\
  LENGTH target_stack <= LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
  pending_inventory_wf target_stack ps /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) target_stack /\
  (!op at. MEM op target_stack /\ (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  FLOOKUP lo target = SOME off /\ off < dimword(:256) /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc_t /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
    next_is_term bb_label ps = SOME (ops, ps') /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf p /\ codegen_ready_fn fn /\ MEM (AsmLabel target) p /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss ==>
  !vs'. step_inst fuel ctx inst vs = OK vs' ==>
    ?n cs' ss'.
      asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      fn_frame_inv ctx cplan lo fn ra rest mem0 ps' vs' cs' /\
      cs'.as_pc = pc_t /\ vs' = jump_to target vs /\
      sym_steps_mode allow_own p env own n ss = SymOK ss' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss'
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qx_gen_tac `vs'` >> strip_tac >>
  `build_offset_to_pc p = build_offset_to_pc p` by simp[] >>
  drule_all_then strip_assume_tac gen_jmp_frame_sim_deep_exact_reloc >>
  drule_all_then strip_assume_tac sym_jmp_plan_decompose >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `!off. MEM (SORestore off) rops ==> off < dimword(:256)` by fs[] >>
  drule_all_then assume_tac sym_jmp_plan_frame_sim_mode_conditional >>
  qpat_x_assum `?ac sy. _` (qx_choose_then `ac` (qx_choose_then `sy` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ac = as'` by
    (qpat_x_assum `asm_steps _ _ _ _ _ = AsmOK ac` mp_tac >> simp[]) >>
  qpat_x_assum `ac = as'` SUBST_ALL_TAC >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp ops)`, `as'`, `sy`] >> simp[] >> metis_tac[]
QED

Theorem sym_jnz_frame_sim_deep_mode_conditional:
  !fuel cplan base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!l off pc. MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
    sym_jump_dest p (Lab l 0) = SOME pc) /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
  ~is_label_operand cond_op /\ inst.inst_outputs = [] /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
  (is_var_operand cond_op ==> IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
  eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\ operand_equiv dfg cond_op at ==>
    operand_val (frame_view fn ra vs) lo cond_op = operand_val (frame_view fn ra vs) lo at) /\
  cond_op <> dead_stack_marker /\
  (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword(:256) /\
  FLOOKUP (build_offset_to_pc p) off_nz = SOME pc_nz /\
  FLOOKUP lo if_z = SOME off_z /\ off_z < dimword(:256) /\
  FLOOKUP (build_offset_to_pc p) off_z = SOME pc_z /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
    next_is_term bb_label ps = SOME (ops, ps') /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf p /\ codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  MEM (AsmLabel if_nz) p /\ MEM (AsmLabel if_z) p /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss ==>
  !vs'. step_inst fuel ctx inst vs = OK vs' ==>
    ?n cs' ss'.
      asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      fn_frame_inv ctx cplan lo fn ra rest mem0 ps' vs' cs' /\
      ((vs' = jump_to if_nz vs /\ cs'.as_pc = pc_nz) \/
       (vs' = jump_to if_z vs /\ cs'.as_pc = pc_z)) /\
      sym_steps_mode allow_own p env own n ss = SymOK ss' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss'
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qx_gen_tac `vs'` >> strip_tac >>
  `build_offset_to_pc p = build_offset_to_pc p` by simp[] >>
  drule_all_then assume_tac gen_jnz_frame_sim_deep_exact_reloc >>
  qpat_x_assum `?iops ps1 rops ps2 w as'. _`
    (qx_choose_then `iops` (qx_choose_then `ps1` (qx_choose_then `rops`
      (qx_choose_then `ps2` (qx_choose_then `w` (qx_choose_then `ac` assume_tac)))))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `1 <= LENGTH ps1.ps_stack` by fs[] >>
  `operand_val (frame_view fn ra vs) lo cond_op = SOME w` by metis_tac[] >>
  drule_all_then assume_tac sym_jnz_plan_frame_sim_mode_conditional >>
  qpat_x_assum `?ac sy. _` (qx_choose_then `sc` (qx_choose_then `sy` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `sc = ac` by
    (qpat_x_assum `asm_steps _ _ _ _ _ = AsmOK sc` mp_tac >> simp[]) >>
  qpat_x_assum `sc = ac` SUBST_ALL_TAC >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
    (if w = 0w then 4 else 2)`, `ac`, `sy`] >> simp[] >> metis_tac[]
QED
