(* Control-prefix framing at supplied offsets, shared by both execution modes.
   Run correspondence is discharged by the control owner at final assembly. *)
Theory symControlPrefixOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] codegenSymRel symPlannerSim symShuffleSim
  stackPlanGen stackPlanTypes planExec asmSem asmSymSem frameRel
  contextCodegenRel unitShapeDefs dfgDefs asmSplice

(* Parser abbreviation only: the existing structural bridge relation. *)
val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

Theorem sym_selected_prefix_frame_sim_marked_mode_conditional:
  !allow_own lo code_ok own opc operands nl ps iops prepared dfg selected rops
    arranged spillbase fn r cp p env ret srest labs0 ctx cs ss initial_fmp.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  opc <> INVOKE /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cp fn ret srest arranged ss' /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `MEM r cplan.cp_regions` >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (iops ++ rops))` by simp[] >>
  drule_all sym_selected_prefix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  conj_tac
  >- (conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  conj_tac
  >- (metis_tac[sym_frame_region_labels_transfer]) >>
  gvs[asmSymBridgeTheory.asm_sym_rel_core_pc]
QED

Theorem sym_prefix_ops_frame_sim_mode_conditional:
  !allow_own lo code_ok own ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs r.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\ context_spill_byte cp b) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\
    sym_kinds_ok cp fn ret srest (apply_prefix_ops initial_fmp lo ops ps) ss' /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `MEM r cplan.cp_regions` >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops)` by simp[] >>
  drule_all (BETA_RULE (Q.INST
    [`R` |-> `\b. r.sr_spill_base <= b /\ b < r.sr_spill_end`]
    (SPEC_ALL sym_prefix_ops_sim))) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  conj_tac
  >- (conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  conj_tac
  >- (metis_tac[sym_frame_region_labels_transfer]) >>
  gvs[asmSymBridgeTheory.asm_sym_rel_core_pc]
QED

Theorem sym_spill_free_prefix_frame_sim_mode_conditional:
  !allow_own lo code_ok own ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops) /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\
    sym_kinds_ok cp fn ret srest (apply_prefix_ops initial_fmp lo ops ps) ss' /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `sym_kinds_ok cplan fn ret srest ps ss` >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops)` by simp[] >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    F /\ context_spill_byte cplan b` by simp[] >>
  drule_all (BETA_RULE (Q.INST [`R` |-> `\b:num. F`]
    (SPEC_ALL sym_prefix_ops_sim))) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED
