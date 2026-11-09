(*
 * The rest of a function's run from inside one of its blocks, on the
 * symbolic machine: fnBlockBody's block_body_frame_sim with the symbolic
 * premises and conclusions added, over the same n steps.  Shared by the
 * two steps of the symbolic fuel induction (symFnStep).
 *
 * TOP-LEVEL:
 *   sym_body_result           - fnBlockBody's conclusion about a run
 *                               result, with the symbolic run
 *   sym_block_body_frame_sim  - the rest of the run, simulated
 *)
Theory symBlockBody
Ancestors
  symFrameBoundary symFrameControl symFrameInvoke symFrameInst symFnSimSpec
  codegenSymRel fnBlockBody fnBlockBodySteps fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  venomExecSemantics venomState venomInst

(* block_body_frame_sim's conclusion (fnBlockBodySteps' body_result) with
   the symbolic run from ss over the same n steps: it ends where the
   concrete run halts, reverts or faults, and at an internal return it is
   OK, related, and holds the returned values as words above srest, with
   the memory labels outside the function's closure those of labs0. *)
Definition sym_body_result_def:
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
      as ss res <=>
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\
               sym_steps prog env n ss = SymOK ss' /\
               asm_sym_rel prog env as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
End

Theorem sym_body_result_error:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss e.
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Error e)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_ok:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss vs.
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (OK vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_halt:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss vs.
  (?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
     venom_asm_terminal_rel vs as' /\
     sym_terminal (sym_steps prog env n ss)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_abort:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss a vs.
  (?n as'.
     ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
      (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
     venom_asm_terminal_rel vs as' /\
     sym_terminal (sym_steps prog env n ss)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_intret:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss rv vs.
  (?n as' ss'.
     asm_steps lo o2pc prog n as = AsmOK as' /\
     as'.as_pc = pc_ret /\
     as'.as_stack = REVERSE rv.iret_values ++ rest /\
     context_memory_rel cp vs.vs_memory as'.as_memory /\
     (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          read_byte b as'.as_memory = read_byte b mem0) /\
     shared_state_rel vs as' /\
     sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
     ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
     (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
     (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_prefix:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as as1 ss ss1 n res.
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps prog env n ss = SymOK ss1 /\
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as1 ss1 res ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss res
Proof
  rpt gen_tac >> strip_tac >>
  `!m. asm_steps lo o2pc prog (n + m) as =
       asm_steps lo o2pc prog m as1` by
    metis_tac[stackOpSimTheory.asm_steps_add_ok] >>
  `!m. sym_steps prog env (n + m) ss = sym_steps prog env m ss1` by
    simp[sym_steps_add] >>
  gvs[sym_body_result_def] >> rpt conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`n' + n`, `as'`] >> simp[] >> metis_tac[]
QED

Theorem sym_body_result_exec:
  !fuel ctx bb vs lo o2pc prog env cp fn mem0 pc_ret rest srest labs0 as ss.
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt gen_tac >> strip_tac >> simp[block_rest_def] >>
  Cases_on `exec_block fuel ctx bb vs` >> gvs[]
QED

Theorem sym_frame_inv_plan_transport:
  !ps' ps prog env ctx cp fn ret srest labs0 cs ss.
  ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss ==>
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps' cs ss
Proof
  simp[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem codegen_sym_code_end_label:
  codegen_assembly rpolicy unit = SOME prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "code_end"
Proof
  simp[codegenTheory.codegen_assembly_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> simp[sym_data_label_def]
QED

Theorem data_segment_asm_header:
  !segs ds. MEM ds segs ==>
    MEM (AsmDataHeader ds.ds_label) (data_segment_asm segs)
Proof
  Induct >> simp[asmIRTheory.data_segment_asm_def,
                 asmIRTheory.data_section_asm_def] >>
  metis_tac[asmIRTheory.data_segment_asm_def]
QED

Theorem codegen_sym_runtime_begin_label:
  codegen_assembly rpolicy unit = SOME prog /\
  sym_unit_static_ok unit /\ MEM fn unit.cu_context.ctx_functions /\
  MEM inst (fn_insts fn) /\ MEM (Label "runtime_begin") inst.inst_operands /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "runtime_begin"
Proof
  rpt strip_tac >>
  `EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment` by
    metis_tac[sym_unit_static_ok_def] >>
  gvs[listTheory.EXISTS_MEM] >>
  `MEM (AsmDataHeader "runtime_begin") (data_segment_asm unit.cu_data_segment)` by
    metis_tac[data_segment_asm_header] >>
  gvs[codegenTheory.codegen_assembly_def, AllCaseEqs()] >>
  simp[sym_data_label_def]
QED

Theorem placed_nonentry_sym_code_label:
  !bb fn liveness dfg cfg ps ops ps' prog pc initial_fmp.
  bb <> HD fn.fn_blocks /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  asm_block_at prog pc (execute_plan initial_fmp ops) ==>
  MEM (AsmLabel bb.bb_label) prog
Proof
  rpt strip_tac >>
  drule_all fnBlockStepHelpersTheory.generate_block_plan_nonentry >>
  strip_tac >> gvs[] >>
  irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >>
  simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

Theorem placed_revert_sym_code_label:
  asm_block_at prog pc (execute_plan initial_fmp revert_postamble) ==>
  MEM (AsmLabel "revert") prog
Proof
  strip_tac >> irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >>
  simp[stackPlanGenTheory.revert_postamble_def,
       planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

(* Application-only view: preserve each quantified/conditional premise intact.
   This generic transformation does not depend on concrete block terms. *)
fun anchored_leaf_core expose names th = let
  val th = SPEC_ALL th
  val (ant, _) = dest_imp (concl th)
  val premises = strip_conj ant
  val body = MP th (LIST_CONJ (map ASSUME premises))
  val body = if expose then SPEC_ALL body else body
  val steps = if expose andalso is_imp (concl body)
              then strip_conj (fst (dest_imp (concl body))) else []
  val body = if null steps then body
             else MP body (LIST_CONJ (map ASSUME steps))
  val premises = premises @ steps
  fun named n t = let
    val t = if is_eq t then lhs t else t
  in fst (dest_const (fst (strip_comb t))) = n end
    handle HOL_ERR _ => false
  val anchors = map (fn n =>
    case List.find (named n) premises of SOME t => t
    | NONE => raise Fail ("missing anchor: " ^ n ^ " in " ^
        String.concatWith "," (map (fn t =>
          (fst (dest_const (fst (strip_comb (if is_eq t then lhs t else t))))
          handle HOL_ERR _ => "variable-head"))
          (filter (fn t => not (is_forall t)) premises)))) names
  val others = filter (fn t => not (exists (aconv t) anchors)) premises
in
  foldr (fn (p, th) => DISCH p th) body (anchors @ others)
end;

fun anchored_leaf names th = anchored_leaf_core true names th;

fun leaf_matches 0 ttac th = ttac th
  | leaf_matches n ttac th = first_assum (fn a =>
      leaf_matches (n - 1) ttac
        (MATCH_MP (PART_MATCH (fst o dest_imp) th (concl a)) a));

Theorem sym_body_ordinary_ok:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 inst vs1 env ret srest labs0 ss.
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  rpt gen_tac >> strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule body_inv_not_in_rf >> disch_then drule >> strip_tac >>
  drule_all body_inv_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `sym_data_label prog env "code_end"` by
    metis_tac[codegen_sym_code_end_label] >>
  `(MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label prog env "runtime_begin")` by
    metis_tac[codegen_sym_runtime_begin_label] >>
  `!op w. inst.inst_opcode = ADD /\
    inst.inst_operands = [op; Label "code_end"] /\ eval_operand op vs = SOME w ==>
    w2n w < dimword (:256) DIV 2` by
    metis_tac[code_end_offset_ok_def] >>
  `!dist prev val_op. inst.inst_opcode = PHI /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
    vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
    operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
    eval_operand val_op (frame_view fn ra vs)` by simp[] >>
  `inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")` by simp[] >>
  leaf_matches 6 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "IN", "step_inst"]
    sym_inst_frame_sim_deep) >>
  simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem sym_body_gas_ok:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule body_inv_not_in_rf >> disch_then drule >> strip_tac >>
  drule_all body_inv_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `context_spill_step_safe cpl vs vs1` by metis_tac[] >>
  leaf_matches 6 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "IN", "step_inst"]
    sym_gas_frame_sim_deep) >>
  simp[venomInstTheory.is_terminator_def] >> strip_tac >> metis_tac[]
QED

Theorem invoke_operands_wf_shape:
  !inst. invoke_operands_wf inst ==>
    ?nm args. inst.inst_operands = Label nm :: args
Proof
  gen_tac >> namedCases_on `inst.inst_operands` ["", "op ops"]
  >- simp[stackPlanGenTheory.invoke_operands_wf_def] >>
  Cases_on `op` >> simp[stackPlanGenTheory.invoke_operands_wf_def]
QED

Theorem sym_body_invoke_step:
  gen_fn_sim_at fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest'.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
      ?n as1 ss1.
        asm_steps lo o2pc prog n as = AsmOK as1 /\
        fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
        as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
        sym_steps prog env n ss = SymOK ss1 /\
        sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (Halt vs1)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (Abort a vs1))
Proof
  strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?nm arg_ops. inst.inst_operands = Label nm :: arg_ops` by
    (irule invoke_operands_wf_shape >>
     qpat_x_assum `codegen_ready_inst inst` mp_tac >>
     simp[stackPlanGenTheory.codegen_ready_inst_def]) >>
  leaf_matches 2 mp_tac (anchored_leaf_core false
    ["codegen_context_obligations", "codegen_assembly"]
    fnBlockBodyClassesTheory.body_callee_placed) >> simp[] >> strip_tac >>
  leaf_matches 3 mp_tac (anchored_leaf_core false
    ["codegen_context_obligations", "codegen_assembly", "gen_fn_sim_at"]
    fnBlockBodyClassesTheory.body_callee_sim) >> simp[] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  leaf_matches 9 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "recordtype.spill_region.seldef.sr_fn_name", "sym_fn_sim_at",
     "codegen_context_obligations", "codegen_assembly", "recordtype.instruction.seldef.inst_operands"]
    sym_invoke_frame_sim_deep) >>
  gvs[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> simp[sym_body_result_def]
QED

Theorem codegen_ready_intret_opcode:
  !fuel ctx inst vs rv vs1.
  codegen_ready_inst inst /\ step_inst fuel ctx inst vs = IntRet rv vs1 ==>
  inst.inst_opcode = RET
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[step_inst_invoke_not_intret] >>
  gvs[step_inst_non_invoke] >>
  drule opcodeClassTheory.step_inst_base_intret_opcodes >>
  gvs[stackPlanGenTheory.codegen_ready_inst_def,
      stackPlanGenTheory.is_pre_codegen_opcode_def,
      stackPlanGenTheory.is_unlowered_fmp_opcode_def,
      venomInstTheory.is_raw_fmp_opcode_def] >>
  strip_tac >> gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem sym_body_halt_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Halt vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs1)
Proof
  strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule body_inv_not_in_rf >> disch_then drule >> strip_tac >>
  drule_all body_inv_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  leaf_matches 6 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "recordtype.spill_region.seldef.sr_fn_name", "step_inst"]
    sym_halt_frame_sim_deep) >>
  simp[] >> strip_tac >> irule sym_body_result_halt >> metis_tac[]
QED

Theorem sym_body_abort_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Abort a vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule body_inv_not_in_rf >> disch_then drule >> strip_tac >>
  drule_all body_inv_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `(inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog)` by
    metis_tac[placed_revert_sym_code_label] >>
  `(inst.inst_opcode = ASSERT ==> ?off pc.
    FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc /\
    asm_block_at prog pc (execute_plan cpl.cp_initial_fmp revert_postamble))` by
    metis_tac[] >>
  leaf_matches 6 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "recordtype.spill_region.seldef.sr_fn_name", "step_inst"]
    sym_abort_frame_sim_deep) >>
  simp[] >> strip_tac >> irule sym_body_result_abort >> metis_tac[]
QED

Theorem sym_body_ret_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = IntRet rv vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs1)
Proof
  strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  `inst.inst_opcode = RET` by metis_tac[codegen_ready_intret_opcode] >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule fnBlockBodyHelpersTheory.reachable_fn_mem_inst >>
     simp[] >> metis_tac[]) >>
  `ps'.ps_stack = []` by metis_tac[] >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  leaf_matches 5 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "step_inst"]
    sym_ret_frame_sim_deep) >>
  simp[] >> strip_tac >> irule sym_body_result_intret >> metis_tac[]
QED

Theorem body_inv_rest_placed:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 ==>
  asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)
Proof
  pure_rewrite_tac [body_inv_def] >> strip_tac >>
  qpat_x_assum `as.as_pc = _` SUBST1_TAC >>
  irule fnBlockBodyHelpersTheory.block_ops_at >> qexists_tac `[]` >>
  pure_rewrite_tac [listTheory.APPEND_NIL] >>
  qpat_x_assum `block_ops = _` (fn th => rewrite_tac [GSYM th]) >>
  first_assum ACCEPT_TAC
QED

Theorem sym_body_revert_abort:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  revert_forward_pair bb k j /\ exec_block fuel ctx bb vs = Abort a vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >>
  `k < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     gvs[contextCodegenRelTheory.revert_forward_pair_def,
         venomInstTheory.get_instruction_def]) >>
  `EL k bb.bb_instructions = EL k bb.bb_instructions` by simp[] >>
  drule_all body_inv_static >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst` by
    (rpt strip_tac >> drule_all fnBlockBodyHelpersTheory.body_inst_ready >>
     gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all rf_pair_no_labels >> strip_tac >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
   DROP k bb.bb_instructions` by
    (simp[rich_listTheory.DROP_DROP_T]) >>
  `generate_block_insts_plan liveness dfg cfg fn bb.bb_label
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (k - LENGTH (get_params bb.bb_instructions))
    (DROP k bb.bb_instructions) ps = SOME (rest_ops, ps_after)` by metis_tac[] >>
  `asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)` by
    metis_tac[body_inv_rest_placed] >>
  `!name. MEM (AsmOp name) (execute_plan cpl.cp_initial_fmp rest_ops) ==>
    IS_SOME (evm_opcode_byte name)` by
    metis_tac[body_placed_target_safe] >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !k' inst' op. _` drule >>
  strip_tac >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !ops ps_end. _` drule >>
  disch_then drule >> strip_tac >>
  leaf_matches 5 mp_tac (anchored_leaf
    ["fn_frame_inv", "generate_block_insts_plan", "sym_frame_inv",
     "generated_plan_state_wf_marked", "exec_block"]
    sym_revert_forward_frame_sim_deep) >>
  simp[] >> strip_tac >> irule sym_body_result_abort >> metis_tac[]
QED

Theorem sym_body_revert_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs)
Proof
  strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  `revert_forward_pair bb vs.vs_inst_idx j` by metis_tac[] >>
  drule fnBlockBodyClassesTheory.rf_exec_block_cases >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >> strip_tac
  >- (simp[] >> drule_all sym_body_revert_abort >> simp[]) >>
  simp[sym_body_result_error]
QED

Theorem body_step_entry_inv:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  ~vs1.vs_halted ==>
  fn_entry_inv Inv ctx fn vs1
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  pure_rewrite_tac [fn_entry_inv_def] >> rpt strip_tac >>
  qhdtm_assum `reachability_closed`
    (mp_tac o cj 2 o REWRITE_RULE [reachability_closed_def]) >>
  disch_then (fn th => leaf_matches 3 mp_tac (anchored_leaf_core false
    ["step_inst", "enters_block", "active_inst"] th)) >> simp[]
QED

Theorem body_jump_entry_lineage:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  MEM t (cfg_succs_of cfg bb.bb_label) /\
  dfs_block_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs ==>
  lineage_entry liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label t
    (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>)
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `ps_dfs_after.ps_spilled = ps_tdfs.ps_spilled` by
    (irule fnBlockPlanStaticRegionTheory.dfs_edge_spilled >> simp[] >>
     metis_tac[]) >>
  pure_rewrite_tac [fnPlanLineageTheory.lineage_entry_def] >>
  qexistsl_tac [`ps_l`, `bb`, `ps_dfs`, `block_ops`, `ps_dfs_after`, `h`,
               `promised`, `ps_after`, `ps_tdfs`] >> simp[]
QED

Theorem body_jump_entry_frame:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
  ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 ==>
  fn_frame_inv ctx cpl lo fn ra rest mem0
    (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>) vs1 as1
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  irule fnBlockBodyHelpersTheory.fn_frame_inv_same_slots >>
  conj_tac >- (qexists_tac `r` >> simp[]) >>
  qexists_tac `ps_after` >> simp[]
QED

Theorem body_jump_entry:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
  ?tbb ps_tdfs tops tafter pe.
    pe = ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |> /\
    ~vs1.vs_halted /\ vs1.vs_labels = vs.vs_labels /\
    vs1.vs_call_ctx = vs.vs_call_ctx /\ vs1.vs_current_bb = t /\
    vs1.vs_prev_bb = SOME bb.bb_label /\ tbb.bb_label = t /\
    lookup_block vs1.vs_current_bb fn.fn_blocks = SOME tbb /\
    tbb <> HD fn.fn_blocks /\ fn_reachable fn tbb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label tbb.bb_label pe /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs1.vs_current_bb ps_tdfs /\
    generate_block_plan liveness dfg cfg fn tbb ps_tdfs = SOME (tops,tafter) /\
    asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 pe vs1 as1 /\
    fn_entry_inv Inv ctx fn vs1 /\
    (!at. MEM at pe.ps_stack \/ at IN FDOM pe.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at))
Proof
  strip_tac >> drule_all fnBlockBodyClassesTheory.body_succ_placed >> strip_tac >>
  `toff = off /\ tpc = as1.as_pc` by metis_tac[optionTheory.SOME_11] >>
  `~vs1.vs_halted` by gvs[frameRelTheory.fn_frame_inv_def] >>
  drule_all body_step_entry_inv >> strip_tac >>
  drule_all body_jump_entry_lineage >> strip_tac >>
  drule_all body_jump_entry_frame >> strip_tac >>
  drule body_inv_facts >> strip_tac >>
  qexistsl_tac [`tbb`, `ps_tdfs`, `tops`, `tafter`,
    `ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>`] >>
  simp[] >> gvs[jump_to_def] >> gvs[]
QED

Theorem sym_body_jump_continue:
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_steps prog env n ss = SymOK ss1 /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 ==>
  ~vs1.vs_halted /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule_all body_jump_entry >> strip_tac >>
  conj_tac >- simp[] >>
  irule sym_body_result_prefix >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  `sym_frame_inv prog env ctx cpl fn ret srest labs0 pe as1 ss1` by
    (irule sym_frame_inv_plan_transport >> goal_assum (drule_at Any) >> simp[]) >>
  qhdtm_assum `sym_fn_frame_sim_at`
    (mp_tac o REWRITE_RULE [sym_fn_frame_sim_at_def]) >>
  pure_rewrite_tac [sym_body_result_def] >>
  disch_then (fn th => leaf_matches 4 irule (anchored_leaf_core false
    ["sym_frame_inv", "fn_frame_inv", "generate_block_plan", "lineage_entry"] th)) >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  metis_tac[]
QED

Theorem jmp_wf_operands:
  inst_wf inst /\ inst.inst_opcode = JMP ==>
  ?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = [] /\
    is_terminator inst.inst_opcode /\ MEM target (get_successors inst)
Proof
  simp[venomWfTheory.inst_wf_def, is_terminator_def] >>
  rpt strip_tac >> gvs[get_successors_def, get_label_def, is_terminator_def]
QED

Theorem sym_body_jmp_prefix:
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all jmp_wf_operands >> strip_tac >>
  drule_all fnBlockBodyClassesTheory.body_terminator_last >> strip_tac >>
  drule_all fnBlockBodyClassesTheory.body_succ_placed >> strip_tac >>
  `MEM (AsmLabel target) prog` by
    (drule_all placed_nonentry_sym_code_label >> simp[]) >>
  qmatch_asmsub_abbrev_tac `generate_block_plan liveness dfg cfg fn tbb ps_tdfs` >>
  `pending_inventory_wf
    (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))) ps` by metis_tac[] >>
  `!op at. MEM op (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\ operand_equiv dfg op at ==>
      operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at` by
    (match_mp_tac mem_operand_equiv >> conj_tac
      >- metis_tac[pending_inventory_wf_owned] >> gvs[body_inv_def]) >>
  `!off. MEM (SORestore off) (FST (restore_spilled_plan
      (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
        (live_vars_at liveness target 0))) ps)) ==> off < dimword (:256)` by
    (rpt strip_tac >> drule_all jmp_plan_restore_ops >> simp[]) >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?n as1 ss1. asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = tpc /\ vs1 = jump_to target vs /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (leaf_matches 6 irule (anchored_leaf
      ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv", "step_inst",
       "pending_inventory_wf", "generated_plan_state_wf_marked"]
      sym_jmp_frame_sim_deep) >> metis_tac[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    (leaf_matches 2 (match_mp_tac o REWRITE_RULE [AND_IMP_INTRO]) (anchored_leaf_core false
      ["generate_inst_plan", "step_inst"] fnAliasStepTheory.alias_step_preserve) >>
     metis_tac[]) >>
  qexistsl_tac [`n`, `as1`, `ss1`, `target`, `toff`] >> simp[] >>
  metis_tac[]
QED

Theorem body_succ_sym_label:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
  ?off pc. FLOOKUP lo t = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc /\ MEM (AsmLabel t) prog
Proof
  strip_tac >> drule_all fnBlockBodyClassesTheory.body_succ_placed >> strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all placed_nonentry_sym_code_label >> metis_tac[]
QED

Theorem jnz_wf_operands:
  inst_wf inst /\ inst_shape_ok inst /\ inst.inst_opcode = JNZ ==>
  ?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
    inst.inst_outputs = [] /\ ~is_label_operand c /\
    is_terminator inst.inst_opcode /\ MEM c (compute_operands inst) /\
    MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)
Proof
  simp[venomWfTheory.inst_wf_def, inst_shape_ok_def,
       label_positions_ok_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `c` >>
  gvs[stackPlanGenTheory.compute_operands_def, asmIRTheory.get_non_label_operands_def,
      get_successors_def, get_label_def, stackPlanTypesTheory.is_label_operand_def,
      is_terminator_def]
QED

Theorem jnz_condition_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = JNZ /\ inst.inst_operands = [c; Label l1; Label l2] ==>
  eval_operand c vs = eval_operand c (frame_view fn ra vs)
Proof
  strip_tac >> irule eval_operand_frame_view_vs >> rpt strip_tac >>
  `MEM (Var x) inst.inst_operands` by gvs[] >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]
QED

Theorem sym_body_jnz_prefix:
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all jnz_wf_operands >> strip_tac >>
  drule_all jnz_condition_frame_view >> strip_tac >>
  `eval_operand c vs = operand_val (frame_view fn ra vs) lo c` by metis_tac[] >>
  drule_all fnBlockBodyClassesTheory.body_terminator_last >> strip_tac >>
  `?off1 pc1. FLOOKUP lo l1 = SOME off1 /\ off1 < dimword (:256) /\
    FLOOKUP o2pc off1 = SOME pc1 /\ MEM (AsmLabel l1) prog` by
    (irule body_succ_sym_label >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `?off2 pc2. FLOOKUP lo l2 = SOME off2 /\ off2 < dimword (:256) /\
    FLOOKUP o2pc off2 = SOME pc2 /\ MEM (AsmLabel l2) prog` by
    (irule body_succ_sym_label >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?n as1 ss1. asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    ((vs1 = jump_to l1 vs /\ as1.as_pc = pc1) \/
     (vs1 = jump_to l2 vs /\ as1.as_pc = pc2)) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (leaf_matches 5 irule (anchored_leaf
      ["fn_frame_inv", "generate_inst_plan", "sym_frame_inv", "step_inst",
       "generated_plan_state_wf_marked"] sym_jnz_frame_sim_deep) >> metis_tac[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    (leaf_matches 2 (match_mp_tac o REWRITE_RULE [AND_IMP_INTRO]) (anchored_leaf_core false
      ["generate_inst_plan", "step_inst"] fnAliasStepTheory.alias_step_preserve) >>
     metis_tac[]) >>
  qexistsl_tac [`n`, `as1`, `ss1`] >> simp[] >>
  metis_tac[]
QED

Theorem sym_body_jmp_step:
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ~vs1.vs_halted /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule_all sym_body_jmp_prefix >> strip_tac >>
  drule_all sym_body_jump_continue >> simp[]
QED

Theorem sym_body_jnz_step:
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ~vs1.vs_halted /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule_all sym_body_jnz_prefix >> strip_tac >>
  drule_all sym_body_jump_continue >> simp[]
QED

Theorem sym_body_nonterm_prefix:
  gen_fn_sim_at fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?prefix' rest' ps' vs' as1 ss1 n.
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix' rest' (SUC k) ps' pc0 vs' as1 Inv
      ra pc_ret rest mem0 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1 /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    block_rest fuel ctx fn bb vs = block_rest fuel ctx fn bb vs'
Proof
  strip_tac >>
  `?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (drule_all sym_body_invoke_step >> strip_tac >>
         first_x_assum drule >> strip_tac >> metis_tac[]) >>
     Cases_on `inst.inst_opcode = GAS`
     >- (drule_all sym_body_gas_ok >> metis_tac[]) >>
     drule_all sym_body_ordinary_ok >> metis_tac[]) >>
  drule_all fnBlockBodyClassesTheory.body_inv_advance >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  drule_all body_inv_inst >> strip_tac >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all block_rest_advance >> strip_tac >>
  qexistsl_tac [`prefix_ops ++ ops`, `rest'`, `ps'`,
    `vs1 with vs_inst_idx := SUC k`, `as1`, `ss1`, `n`] >> simp[]
QED

Theorem sym_body_out_of_range:
  LENGTH bb.bb_instructions <= vs.vs_inst_idx ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule fnBlockBodyHelpersTheory.exec_block_out_of_range >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  drule block_rest_error >> simp[sym_body_result_error]
QED

Theorem sym_body_terminator:
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all fnBlockBodyHelpersTheory.step_ok_terminator_jump >> strip_tac
  >- (drule_all sym_body_jmp_step >> strip_tac >> metis_tac[block_rest_jump])
  >- (drule_all sym_body_jnz_step >> strip_tac >> metis_tac[block_rest_jump]) >>
  gvs[inst_shape_ok_def]
QED

Theorem sym_body_nonok:
  gen_fn_sim_at fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = res /\ (!s. res <> OK s) /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all block_rest_other >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  Cases_on `res` >> fs[sym_body_result_error]
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (drule_all sym_body_invoke_step >> metis_tac[]) >>
      drule_all sym_body_halt_step >> simp[])
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (drule_all sym_body_invoke_step >> metis_tac[]) >>
      drule_all sym_body_abort_step >> simp[]) >>
  drule_all sym_body_ret_step >> simp[]
QED

Theorem sym_body_inst_bounds:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4)
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  conj_tac >- (drule_all body_operands_le_16 >> simp[]) >>
  strip_tac >> irule log_case_topics >>
  drule_all body_log_topics >> simp[]
QED

Theorem sym_body_revert_result:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule_all sym_body_revert_step >> strip_tac >>
  irule sym_body_result_exec >> simp[]
QED

Theorem sym_body_nonterm_result:
  (!m. m < d ==>
    !k prefix_ops rest_ops ps vs as ss.
      m = LENGTH bb.bb_instructions - k /\
      gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
      sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
      body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
        growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
        block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
        ra pc_ret rest mem0 /\
      label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
      sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (block_rest fuel ctx fn bb vs)) /\
  d = LENGTH bb.bb_instructions - k /\
  gen_fn_sim_at fuel /\ sym_fn_sim_at fuel /\
  gen_fn_frame_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule_all sym_body_nonterm_prefix >> strip_tac >>
  `LENGTH bb.bb_instructions - SUC k < d` by decide_tac >>
  qpat_x_assum `!m. m < d ==> _` drule >> strip_tac >>
  `sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
     as1 ss1 (block_rest fuel ctx fn bb vs')` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all sym_body_result_prefix >> simp[]
QED

Theorem sym_body_run:
  !d k prefix_ops rest_ops ps vs as ss.
    d = LENGTH bb.bb_instructions - k /\
    gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
    sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
    sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  completeInduct_on `d` >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `k < LENGTH bb.bb_instructions`)
  >- (irule sym_body_out_of_range >>
      `vs.vs_inst_idx = k` by gvs[body_inv_def] >> simp[]) >>
  `EL k bb.bb_instructions = EL k bb.bb_instructions` by simp[] >>
  drule_all sym_body_inst_bounds >> strip_tac >>
  Cases_on `?j. revert_forward_pair bb k j`
  >- (pop_assum strip_assume_tac >> drule_all sym_body_revert_result >> simp[]) >>
  pop_assum (assume_tac o REWRITE_RULE [NOT_EXISTS_THM]) >>
  Cases_on `?vs1. step_inst fuel ctx (EL k bb.bb_instructions) vs = OK vs1`
  >- (pop_assum strip_assume_tac >>
      Cases_on `is_terminator (EL k bb.bb_instructions).inst_opcode`
      >- (drule_all sym_body_terminator >> simp[]) >>
      drule_all sym_body_nonterm_result >> simp[]) >>
  `!s. step_inst fuel ctx (EL k bb.bb_instructions) vs <> OK s` by metis_tac[] >>
  metis_tac[sym_body_nonok]
QED

(* body_inv bundles block_body_frame_sim's premises. *)
Theorem sym_block_body_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 env ret srest labs0 ss.
    gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
    sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    (* ----- The symbolic side ----- *)
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt strip_tac >> metis_tac[sym_body_run]
QED
