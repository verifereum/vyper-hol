(*
 * Block-boundary pieces of the label-discipline proof on the symbolic
 * machine: a block's PHI prefix (after a cleanup when the block has one
 * predecessor) and a function's parameter prologue.  Each
 * is codegen's own lemma with the symbolic premises and conclusions added,
 * over the same n steps.  The prologue starts from the entry symbolic
 * state of sym_fn_sim_at and establishes the symbolic frame invariant,
 * with the memory labels at entry as the frame's labs0.
 *
 * TOP-LEVEL:
 *   sym_phi_prefix_frame_sim          - a join block's PHI prefix
 *   sym_single_pred_prefix_frame_sim  - a one-predecessor block's cleanup
 *                                       and PHI prefix
 *   sym_entry_prefix_frame_sim        - a function's parameter prologue
 *)
Theory symFrameBoundary
Ancestors
  codegenSymRel fnFrameSteps fnFrameSinglePred fnEntryParams fnFrameBoundary asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs

(* Symbolic kinds at the boundary depend on the defining instruction,
   not on the concrete word used to represent a label. *)
Theorem phi_input_not_code_end:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands ==>
  ~code_end_var fn x
Proof
  rw[label_flow_ok_def] >>
  first_x_assum drule_all >> simp[] >> metis_tac[]
QED

Theorem phi_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs ==>
  ~code_end_var fn x
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> simp[]
QED

Theorem phi_retpc_kind:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs /\
  MEM (Var y) inst.inst_operands ==>
  (retpc_var fn x <=> retpc_var fn y)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      drule (cj 3 (iffLR retpc_shape_ok_def)) >>
      disch_then drule_all >> simp[] >> metis_tac[]) >>
  simp[retpc_var_def] >> strip_tac >>
  irule (cj 3 copy_phi_var_rules) >> metis_tac[]
QED

Theorem phi_operand_kind_transport:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  ssa_form fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM x inst.inst_outputs /\ MEM (Var y) inst.inst_operands /\
  op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var x) sv
Proof
  strip_tac >>
  drule_all phi_input_not_code_end >> strip_tac >>
  drule_all phi_output_not_code_end >> strip_tac >>
  drule_all phi_retpc_kind >> strip_tac >>
  gvs[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem param_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  ~code_end_var fn x
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> gvs[]
QED

Theorem param_output_retpc_kind:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  (retpc_var fn x <=> inst.inst_opcode = RETPC_PARAM)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule (cj 3 (iffLR retpc_shape_ok_def)) >>
      disch_then drule_all >> gvs[]) >>
  strip_tac >> simp[retpc_var_def] >>
  irule (cj 1 copy_phi_var_rules) >> metis_tac[]
QED

Theorem param_output_kind:
  ssa_form fn /\ retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  (op_kind_ok fn ret (Var x) sv <=>
   if inst.inst_opcode = RETPC_PARAM then sv = Lab ret 0
   else ?w. sv = Val w)
Proof
  strip_tac >> drule_all param_output_not_code_end >> strip_tac >>
  drule_all param_output_retpc_kind >> strip_tac >>
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem sym_frame_inv_same_count:
  !lo o2pc prog env ctx cp fn ret srest labs0 ps cs ss n cs' ss' ps'.
  lo = SND (compute_label_offsets prog) /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss /\
  asm_steps lo o2pc prog n cs = AsmOK cs' /\
  sym_steps prog env n ss = SymOK ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
     FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rw[sym_frame_inv_def] >>
  drule_all asm_sym_steps_lockstep >> strip_tac >> gvs[]
QED

Theorem sym_kinds_stack_poke:
  !cp fn ret srest ps ss d op.
  sym_kinds_ok cp fn ret srest ps ss /\ d < LENGTH ps.ps_stack /\
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
        op_kind_ok fn ret op sv) ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  rw[sym_kinds_ok_def] >> qexists `top` >>
  gvs[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_poke_def] >>
  rpt strip_tac >>
  simp[listTheory.EL_REVERSE, listTheory.EL_LUPDATE] >>
  IF_CASES_TAC >> gvs[stackModelTheory.stack_peek_def,
    listTheory.EL_REVERSE] >> metis_tac[]
QED

(* Scratch memory is indexed by byte offset, not by operand identity. *)
Theorem mem_sval_at_store_label:
  !labs off l d.
  mem_sval_at (labs |++ GENLIST (\i. (off+i,(l,d,i))) 32) off (Lab l d)
Proof
  simp[mem_sval_at_def, mem_label_at_def, mstore_labels_lookup,
       listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem sym_mload_mem_sval_label:
  !ss off l d stk.
  ss.sym_stack = Val off :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Lab l d) ==>
  sym_mload ss = SymOK
    (ss with <| sym_base := asm_next (ss.sym_base with
                  as_memory := asm_expand_memory (w2n off + 32)
                    ss.sym_base.as_memory);
                sym_stack := Lab l d :: stk |>)
Proof
  simp[mem_sval_at_def, sym_mload_def]
QED

Theorem mem_sval_at_cong:
  !labs labs' off sv.
  (!i. in_mem_range off 32 i ==> FLOOKUP labs' i = FLOOKUP labs i) ==>
  (mem_sval_at labs' off sv <=> mem_sval_at labs off sv)
Proof
  rpt gen_tac >> simp[in_mem_range_def] >> strip_tac >> Cases_on `sv`
  >- (simp[mem_sval_at_def, in_mem_range_def] >>
      metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  simp[mem_sval_at_def, mem_label_at_def,
       listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem mem_sval_at_clear_value:
  !labs off w.
  mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) off (Val w)
Proof
  simp[mem_sval_at_def, mem_labels_clear_def,
       finite_mapTheory.FDOM_DRESTRICT, pred_setTheory.IN_INTER]
QED

Theorem sym_mstore_label_scratch:
  !ss off l d stk.
  ss.sym_stack = Val off :: Lab l d :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Lab l d) /\
    (!i. ~in_mem_range (w2n off) 32 i ==>
      FLOOKUP ss'.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i)
Proof
  rpt strip_tac >>
  simp[sym_mstore_def, sym_lift_def, asmSemTheory.asm_mstore_def,
       asmSemTheory.asm_next_def, mem_sval_at_store_label,
       mstore_labels_lookup, in_mem_range_def, Excl "GENLIST_NUMERALS"] >>
  pure_once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
  rewrite_tac[mem_sval_at_store_label, mstore_labels_lookup] >>
  simp[]
QED

Theorem sym_phi_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  cheat
QED

Theorem sym_single_pred_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised ps base vs as s_phi clean_ops ps2 phis body ops ps3
   r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps2 =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  cheat
QED

Theorem sym_entry_prefix_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest Inv
   env ret srest ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    fn_entry_inv Inv ctx fn vs /\ reachability_closed Inv ctx /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    (* ----- The symbolic side: the entry symbolic state of sym_fn_sim_at *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    asm_sym_rel prog env as ss /\
    ss.sym_stack =
      (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b)
    ==>
    ?n as' vs_p ss'.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as' /\
      vs_p.vs_current_bb = vs.vs_current_bb /\
      vs_p.vs_labels = vs.vs_labels /\
      vs_p.vs_call_ctx = vs.vs_call_ctx /\
      (!inst. active_inst fn inst vs_p ==> Inv ctx fn inst vs_p) /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra vs_p) lo at =
         operand_val (frame_view fn ra vs_p) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest ss.sym_mem_labels ps1 as' ss'
Proof
  cheat
QED
