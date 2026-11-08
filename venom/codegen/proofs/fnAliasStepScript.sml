(*
 * One instruction's step preserves the slot alias invariant of the block
 * induction (fnAliasInv): every operand on the planner's stack or in its
 * spill map has the value of its ASSIGN-chain root (normalize_operand),
 * read through the frame view.  The block body (fnBlockBody) carries it
 * from instruction to instruction; lineage_alias_successor carries it
 * across a whole block from the block's entry.
 *
 * TOP-LEVEL:
 *   alias_step_preserve - an instruction whose step is OK keeps the
 *                         invariant from its planner state to the next
 *)

Theory fnAliasStep
Ancestors
  fnAliasInv reorderSim frameRel codegenRel unitShapeDefs stackPlanGen
  stackPlanOps stackPlanTypes venomExecSemantics venomState livenessDefs
  dfgDefs cfgDefs deepResidualBudget fnFrameStepsRevertForward frameViewFacts
  venomExecProps venomInstProps planWf stackModel foldlSim
  list rich_list finite_map pred_set fnPlanLineageInventory fnPlanLineageReorder
(* ===== Slot provenance: the planner manufactures no operand ===== *)

Theorem restore_spilled_plan_inventory_subset = fnPlanLineageInventoryTheory.restore_spilled_plan_inventory_subset

(* A restore moves its operand from the spill map to the stack. *)
Theorem do_restore_inventory_count[local] = fnPlanLineageInventoryTheory.do_restore_inventory_count

Theorem restore_spilled_plan_inventory_count[local] = fnPlanLineageInventoryTheory.restore_spilled_plan_inventory_count

(* The join reorder's target stack fits on the stack once its spilled
   operands are restored. *)
Theorem restore_spilled_plan_length_floor = fnPlanLineageInventoryTheory.restore_spilled_plan_length_floor

Theorem reorder_restore_length_mono[local] = fnPlanLineageInventoryTheory.reorder_restore_length_mono

(* reorder_one keeps the target window on the stack, with no bound on the
   number of targets. *)
Theorem reorder_one_length_floor = fnPlanLineageInventoryTheory.reorder_one_length_floor

Theorem plan_steps_reorder_inventory_subset_nb[local] = fnPlanLineageInventoryTheory.plan_steps_reorder_inventory_subset_nb

(* reorder_plan manufactures no operand, with no bound on the number of
   targets. *)
Theorem reorder_plan_inventory_subset_nb = fnPlanLineageInventoryTheory.reorder_plan_inventory_subset_nb

Theorem foldl_plan_inventory_subset[local] = fnPlanLineageInventoryTheory.foldl_plan_inventory_subset

Theorem popmany_individual_inventory_subset = fnPlanLineageInventoryTheory.popmany_individual_inventory_subset

Theorem popmany_plan_inventory_subset = fnPlanLineageInventoryTheory.popmany_plan_inventory_subset

Theorem optimistic_swap_plan_inventory_subset = fnPlanLineageInventoryTheory.optimistic_swap_plan_inventory_subset

Theorem release_dead_spills_inventory_subset = fnPlanLineageInventoryTheory.release_dead_spills_inventory_subset

Theorem generate_emit_ops_slots = fnPlanLineageReorderTheory.generate_emit_ops_slots

Theorem foldl_push_outputs_inventory[local]:
  !outs ps at.
    MEM at (FOLDL (\ps' out. ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
              ps outs).ps_stack \/
    at IN FDOM (FOLDL (\ps' out. ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
              ps outs).ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
    ?out. MEM out outs /\ at = Var out
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then
    [`ps with ps_stack := stack_push (Var h) ps.ps_stack`, `at`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  simp[stack_push_def, MEM_SNOC] >> metis_tac[]
QED

(* Every slot a regular instruction's plan leaves is a slot of its input
   state, one of its stack operands, or one of its outputs. *)
Theorem generate_regular_inst_plan_inventory:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_regular_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      (ops,ps') /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
          MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!target_ops. inst.inst_opcode = JMP /\
       join_target_ops liveness fn bbl inst = SOME target_ops ==>
       pending_inventory_wf target_ops ps) ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
      MEM at (compute_operands inst) \/
      ?out. MEM out inst.inst_outputs /\ at = Var out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst ltc` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  (* input emission *)
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
        MEM at (compute_operands inst)` by
    metis_tac[emit_input_plan_inventory_subset] >>
  (* join reorder *)
  `(!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
         MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled) /\
   LENGTH (compute_operands inst) <= LENGTH ps2.ps_stack` by
    (qpat_x_assum `(if _ then _ else _) = (join_ops,ps2)` mp_tac >>
     IF_CASES_TAC
     >- (BasicProvers.TOP_CASE_TAC
         >- (simp[] >> strip_tac >> gvs[] >>
             metis_tac[available_input_plan_length]) >>
         rename1 `join_target_ops _ _ _ _ = SOME target_ops` >>
         rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
         `pending_inventory_wf target_ops ps` by metis_tac[] >>
         `compute_operands inst = []` by
           (qpat_x_assum `join_target_ops _ _ _ _ = _` mp_tac >>
            simp[join_target_ops_def, AllCaseEqs()] >> strip_tac >>
            gvs[compute_operands_def, asmIRTheory.get_non_label_operands_def]) >>
         gvs[] >>
         rename1 `restore_spilled_plan target_ops ps = (restore_ops,ps1')` >>
         `LENGTH target_ops <= LENGTH ps1'.ps_stack` by
           metis_tac[restore_spilled_plan_length_floor] >>
         metis_tac[reorder_plan_inventory_subset_nb,
                   restore_spilled_plan_inventory_subset]) >>
     simp[] >> strip_tac >> gvs[] >>
     metis_tac[available_input_plan_length]) >>
  (* operand reorder, possibly commuted *)
  `!l rops rps. LENGTH l = LENGTH (compute_operands inst) /\
     reorder_plan dfg l ps2 = (rops,rps) ==>
     !at. MEM at rps.ps_stack \/ at IN FDOM rps.ps_spilled ==>
          MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled` by
    (rpt gen_tac >> strip_tac >>
     `LENGTH l <= LENGTH ps2.ps_stack` by decide_tac >>
     metis_tac[reorder_plan_inventory_subset_nb]) >>
  `!at. MEM at ps4.ps_stack \/ at IN FDOM ps4.ps_spilled ==>
        MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled` by
    (qpat_x_assum `(if _ then _ else _) = (reorder_ops,ps4)` mp_tac >>
     IF_CASES_TAC
     >- (IF_CASES_TAC >> strip_tac >> gvs[]
         >- metis_tac[] >>
         `LENGTH (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
            [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
             EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]) =
          LENGTH (compute_operands inst)` by
           (fs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> rw[] >> fs[]) >>
         metis_tac[]) >>
     strip_tac >> metis_tac[]) >>
  (* pop operands, push outputs, emit *)
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst ltc ps6 = (emit_ops,ps7)` >>
  `!at. MEM at ps7.ps_stack \/ at IN FDOM ps7.ps_spilled ==>
        MEM at ps4.ps_stack \/ at IN FDOM ps4.ps_spilled \/
        ?out. MEM out inst.inst_outputs /\ at = Var out` by
    (drule generate_emit_ops_slots >> strip_tac >> simp[] >>
     rpt strip_tac >>
     qspecl_then [`inst.inst_outputs`,
       `ps4 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack`,
       `at`] mp_tac foldl_push_outputs_inventory >>
     (impl_tac >- gvs[Abbr `ps6`]) >>
     simp[stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  (* post-processing *)
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> rpt strip_tac >>
      metis_tac[release_dead_spills_inventory_subset]) >>
  `!at. MEM at ps8.ps_stack \/ at IN FDOM ps8.ps_spilled ==>
        MEM at ps7.ps_stack \/ at IN FDOM ps7.ps_spilled` by
    (qpat_x_assum `(if _ then _ else _) = (pop_ops,ps8)` mp_tac >>
     IF_CASES_TAC >> strip_tac >> gvs[] >>
     metis_tac[popmany_plan_inventory_subset]) >>
  `!at. MEM at ps9.ps_stack \/ at IN FDOM ps9.ps_spilled ==>
        MEM at ps8.ps_stack \/ at IN FDOM ps8.ps_spilled` by
    (qpat_x_assum `(if _ then _ else _) = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >> strip_tac >> gvs[] >>
     metis_tac[optimistic_swap_plan_inventory_subset]) >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  metis_tac[release_dead_spills_inventory_subset]
QED

Theorem generate_inst_plan_inventory:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      SOME (ops,ps') /\
    inst.inst_opcode <> PHI /\
    (inst.inst_opcode = OFFSET ==> ?out. inst.inst_outputs = [out]) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
          MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!target_ops. inst.inst_opcode = JMP /\
       join_target_ops liveness fn bbl inst = SOME target_ops ==>
       pending_inventory_wf target_ops ps) ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
      ~is_var_operand at \/
      ?out. MEM out inst.inst_outputs /\ at = Var out
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (`?out. inst.inst_outputs = [out]` by metis_tac[] >>
      gvs[generate_inst_plan_def, generate_offset_plan_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[stack_push_def, MEM_SNOC]) >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- (gvs[generate_inst_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (gvs[generate_inst_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  `generate_regular_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
     (ops,ps')` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, LET_THM, AllCaseEqs()]) >>
  qspecl_then [`liveness`,`dfg`,`cfg`,`fn`,`inst`,`nl`,`ih`,`nit`,`bbl`,
               `ps`,`ops`,`ps'`] mp_tac generate_regular_inst_plan_inventory >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!at. _ ==> _ \/ _ \/ MEM at (compute_operands inst) \/ _`
    (qspec_then `at` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >> simp[] >>
  Cases_on `is_var_operand at` >> simp[] >> metis_tac[]
QED

(* ===== Values: an OK step changes only its outputs ===== *)

Theorem step_inst_ok_non_output_lookup:
  !fuel ctx inst vs vs1 v.
    step_inst fuel ctx inst vs = OK vs1 /\ ~MEM v inst.inst_outputs ==>
    FLOOKUP vs1.vs_vars v = FLOOKUP vs.vs_vars v
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
      simp[lookup_var_def]) >>
  drule_all venomInstPropsTheory.step_preserves_non_output_vars >>
  simp[lookup_var_def]
QED

Theorem frame_view_non_output_val:
  !fuel ctx inst vs vs1 fn ra lo op.
    step_inst fuel ctx inst vs = OK vs1 /\
    (!v. op = Var v ==> ~MEM v inst.inst_outputs) ==>
    operand_val (frame_view fn ra vs1) lo op =
    operand_val (frame_view fn ra vs) lo op
Proof
  rpt strip_tac >> Cases_on `op` >> simp[operand_val_def, frame_view_vars_lookup] >>
  rename1 `FLOOKUP vs1.vs_vars x` >>
  `FLOOKUP vs1.vs_vars x = FLOOKUP vs.vs_vars x` by
    (irule step_inst_ok_non_output_lookup >> metis_tac[]) >>
  simp[]
QED

(* Used at each instruction of the block body whose step is OK: every
   non-terminator (INVOKE included), and a JMP or JNZ, after which ps' is
   the state the successor's lineage entry inherits its stack and spill
   map from.  Its static premises are fnBlockPlanStatic's
   block_plan_state_static conclusions.  The label premise is needed at
   vs only: operand_val reads labels from lo, but an ASSIGN of a label
   gives its output the value vs_labels has.

   Why it should hold: a step that is OK changes no variable but inst's
   outputs (step_inst_base; INVOKE binds its outputs into the caller's
   state, merge_callee_state).  By the freshness premise, no slot of ps
   is an output or has one as its root, so each slot of ps keeps both
   values.  Each slot of ps' is a slot of ps (moved, duplicated, restored
   or spilled), a literal or label (its own root, as is
   dead_stack_marker), or an output of inst.  The emitted operands are
   owned (ownership premise), and a JMP's join reorder may relabel an
   equivalent slot as a target variable, which pending_inventory_wf keeps
   to variables the state holds.  An output's root is itself unless inst
   is an ASSIGN (dfg_build_function and SSA make inst its dfg_defs
   entry); an ASSIGN's output takes its operand's value: an owned
   variable's, which is its root's by the invariant at vs; a literal; or
   a label's, which is lo's by the label premise.  Return-PC variables are
   copied only into return-PC variables (retpc_shape_ok), so the frame
   view reads ra on both sides of such an ASSIGN. *)
Theorem alias_step_preserve:
  !fuel ctx lo fn ra liveness dfg cfg inst next_live is_halting next_is_term
   bb_label ps ops ps' vs vs1.
    dfg = dfg_build_function fn /\ codegen_ready_fn fn /\ retpc_shape_ok fn /\
    MEM inst (fn_insts fn) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       pending_inventory_wf target_stack ps) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    generate_inst_plan liveness dfg cfg fn inst next_live is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    step_inst fuel ctx inst vs = OK vs1
    ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     gvs[step_inst_non_invoke, Once step_inst_base_def]) >>
  `inst.inst_opcode = OFFSET ==> ?out. inst.inst_outputs = [out]` by
    (strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     gvs[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def,
         AllCaseEqs()] >> strip_tac >> simp[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op (compute_operands inst) /\ _ ==> IS_SOME _ \/ _`
       (qspec_then `op` mp_tac) >>
     impl_tac >- metis_tac[] >>
     Cases_on `stack_get_depth op ps.ps_stack` >> simp[FLOOKUP_DEF]
     >- (IF_CASES_TAC >> simp[]) >>
     drule stack_get_depth_props >> metis_tac[stack_peek_mem]) >>
  `!target_ops. inst.inst_opcode = JMP /\
     join_target_ops liveness fn bb_label inst = SOME target_ops ==>
     pending_inventory_wf target_ops ps` by
    (rpt strip_tac >> gvs[join_target_ops_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
     MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
     ~is_var_operand at \/
     ?out. MEM out inst.inst_outputs /\ at = Var out` by
    (qspecl_then [`liveness`,`dfg_build_function fn`,`cfg`,`fn`,`inst`,
                  `next_live`,`is_halting`,`next_is_term`,`bb_label`,`ps`,
                  `ops`,`ps'`] mp_tac generate_inst_plan_inventory >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!at. MEM at ps'.ps_stack \/ _ ==> _ \/ _ \/ ~is_var_operand at \/ _`
    (qspec_then `at` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
  >~ [`~is_var_operand at`]
  >- (Cases_on `at` >> gvs[is_var_operand_def, normalize_operand_def])
  >~ [`MEM out inst.inst_outputs`]
  >- (qpat_x_assum `MEM _ ps'.ps_stack \/ _` kall_tac >>
      `dfg_get_def (dfg_build_function fn) out = SOME inst` by
        metis_tac[dfg_build_function_ssa_def] >>
      Cases_on `inst.inst_opcode = ASSIGN`
      >- (`?op1 out1 v. inst.inst_operands = [op1] /\
            inst.inst_outputs = [out1] /\ eval_operand op1 vs = SOME v /\
            vs1 = update_var out1 v vs` by
            (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
             qpat_x_assum `inst.inst_opcode = ASSIGN`
               (fn th => simp[th, step_inst_non_invoke,
                              Once step_inst_base_def]) >>
             simp[AllCaseEqs()] >> metis_tac[]) >>
          gvs[] >>
          `normalize_operand (dfg_build_function fn) [] (Var out) = normalize_operand (dfg_build_function fn) [] op1` by
            metis_tac[normalize_operand_codegen_assign] >>
          simp[] >>
          Cases_on `op1`
          >- (`~retpc_var fn out` by
                (irule assign_nonvar_output_not_retpc >> simp[] >>
                 qexists_tac `inst` >> simp[]) >>
              gvs[eval_operand_def, normalize_operand_def, operand_val_def,
                  frame_view_vars_lookup, update_var_def, FLOOKUP_UPDATE])
          >- (rename1 `inst.inst_operands = [Var y]` >>
              `MEM (Var y) (compute_operands inst)` by
                gvs[compute_operands_def] >>
              `MEM (Var y) ps.ps_stack \/ Var y IN FDOM ps.ps_spilled` by
                (qpat_x_assum
                   `!op. MEM op (compute_operands inst) /\ _ ==> MEM op _ \/ _`
                   irule >> simp[is_var_operand_def]) >>
              `retpc_var fn out <=> retpc_var fn y` by
                (irule assign_output_retpc >> simp[] >>
                 qexists_tac `inst` >> simp[]) >>
              `operand_val (frame_view fn ra (update_var out v vs)) lo (Var out) =
               SOME (if retpc_var fn y then ra else v)` by
                (simp[operand_val_def, frame_view_vars_lookup, update_var_def,
                      FLOOKUP_UPDATE] >> metis_tac[]) >>
              `operand_val (frame_view fn ra vs) lo (Var y) =
               SOME (if retpc_var fn y then ra else v)` by
                (qpat_x_assum `eval_operand (Var y) vs = _` mp_tac >>
                 simp_tac bool_ss [eval_operand_def, lookup_var_def,
                   operand_val_def, frame_view_vars_lookup] >>
                 strip_tac >>
                 asm_simp_tac bool_ss [optionTheory.OPTION_MAP_DEF]) >>
              `operand_val (frame_view fn ra vs) lo (Var y) =
               operand_val (frame_view fn ra vs) lo
                 (normalize_operand (dfg_build_function fn) [] (Var y))` by metis_tac[] >>
              `operand_val (frame_view fn ra (update_var out v vs)) lo
                 (normalize_operand (dfg_build_function fn) [] (Var y)) =
               operand_val (frame_view fn ra vs) lo
                 (normalize_operand (dfg_build_function fn) [] (Var y))` by
                (irule frame_view_non_output_val >>
                 qexistsl_tac [`ctx`,`fuel`,`inst`] >>
                 conj_tac >- (rpt strip_tac >>
                   qpat_x_assum `!op. _ \/ _` (qspec_then `Var y` mp_tac) >>
                   gvs[]) >>
                 first_assum ACCEPT_TAC) >>
              metis_tac[])
          >> `~retpc_var fn out` by
               (irule assign_nonvar_output_not_retpc >> simp[] >>
                qexists_tac `inst` >> simp[]) >>
             gvs[eval_operand_def, normalize_operand_def, operand_val_def,
                 frame_view_vars_lookup, update_var_def, FLOOKUP_UPDATE]) >>
      `normalize_operand (dfg_build_function fn) [] (Var out) = Var out` by
        (simp[Once normalize_operand_def] >> gvs[dfg_get_def_def]) >>
      simp[]) >>
  `operand_val (frame_view fn ra vs) lo at =
   operand_val (frame_view fn ra vs) lo (normalize_operand (dfg_build_function fn) [] at)` by
    metis_tac[] >>
  `operand_val (frame_view fn ra vs1) lo at =
   operand_val (frame_view fn ra vs) lo at` by
    (irule frame_view_non_output_val >>
     qexistsl_tac [`ctx`,`fuel`,`inst`] >>
     conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  `operand_val (frame_view fn ra vs1) lo (normalize_operand (dfg_build_function fn) [] at) =
   operand_val (frame_view fn ra vs) lo (normalize_operand (dfg_build_function fn) [] at)` by
    (irule frame_view_non_output_val >>
     qexistsl_tac [`ctx`,`fuel`,`inst`] >>
     conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
