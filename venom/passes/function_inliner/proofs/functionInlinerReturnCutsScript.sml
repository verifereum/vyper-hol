(* Bounded actual-edit test of routed return cuts.  Definitions here are
   proof examples, not alternate executable semantics or input contracts. *)
Theory functionInlinerReturnCuts
Ancestors
  functionInlinerCuts functionInlinerReturnTransport functionInlinerDefs
  callLayoutDefs venomExecSemantics venomExecProofs venomState venomInst list finite_map
  analysisSimDefs

Definition return_cut_inner_def:
  return_cut_inner fmp = mk_raw_function "inner"
    [<|bb_label := "inner"; bb_instructions :=
      [mk_inst 10 PARAM [Lit 0w] ["arg"]] ++
      (if fmp then [mk_inst 11 FMP_PARAM [Lit 1w] ["fp"]] else []) ++
      [mk_inst 12 RETPC_PARAM [Lit (if fmp then 2w else 1w)] ["pc"];
       mk_inst 13 (if fmp then RETFMP else RET)
         [Var "arg"; Var "pc"] []] |>]
End

Definition return_cut_middle_def:
  return_cut_middle fmp = mk_raw_function "middle"
    [<|bb_label := "middle"; bb_instructions :=
      [mk_inst 20 RETPC_PARAM [Lit 0w] ["mpc"]] ++
      (if fmp then [mk_inst 21 GETFMP [] ["mf"]] else []) ++
      [mk_inst 22 INVOKE
         (if fmp then [Label "inner"; Lit 41w; Var "mf"]
          else [Label "inner"; Lit 41w]) ["answer"];
       mk_inst 23 RET [Var "answer"; Var "mpc"] []] |>]
End

Definition return_cut_outer_def:
  return_cut_outer = mk_raw_function "outer"
    [<|bb_label := "outer"; bb_instructions :=
      [mk_inst 30 INVOKE [Label "middle"] ["result"];
       mk_inst 31 STOP [] []] |>]
End

Definition return_cut_produced_def:
  return_cut_produced fmp =
    let p0 = inline_prefix 0;
        r0 = return_block_label p0 0;
        p1 = inline_prefix 1;
        r1 = return_block_label p1 1;
        mid = renumber_fn_inst_ids (inline_call_site p0 r0
          (return_cut_middle fmp) (return_cut_inner fmp) "middle"
          (if fmp then 2 else 1))
    in renumber_fn_inst_ids
         (inline_call_site p1 r1 return_cut_outer mid "outer" 0)
End

Theorem return_cut_layout:
  !fmp. ?bb.
    lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
    get_instruction bb (if fmp then 3 else 2) = SOME
      (mk_inst (if fmp then 10 else 8) ASSIGN
         [Var "inl1_inl0_arg"] ["inl1_answer"]) /\
    get_instruction bb (if fmp then 4 else 3) = SOME
      (mk_inst (if fmp then 11 else 9) JMP
        [Label "inl1_inl0_inline_return0"] []) /\
    LENGTH bb.bb_instructions = (if fmp then 5 else 4)
Proof
  Cases >> EVAL_TAC >> simp[mk_inst_def]
QED

Theorem return_cut_execute:
  !fmp t w fuel ctx.
    lookup_var "inl1_inl0_arg" t = SOME w /\ ~t.vs_halted ==>
    ?bb.
      lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
      exec_block fuel ctx bb
        (t with vs_inst_idx := if fmp then 3 else 2) =
        OK (jump_to "inl1_inl0_inline_return0"
          (update_var "inl1_answer" w t))
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `fmp` strip_assume_tac return_cut_layout >>
  qexists_tac `bb` >> simp[] >>
  irule inline_return_sequence_exec_block >>
  conj_tac >- simp[update_var_def] >>
  qexistsl_tac [`[mk_inst (if fmp then 10 else 8) ASSIGN
    [Var "inl1_inl0_arg"] ["inl1_answer"]]`,
    `if fmp then 11 else 9`] >>
  Cases_on `fmp` >>
  gvs[get_instruction_def, mk_inst_def, run_insts_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def]
QED

(* Source return evidence is independent of the physical owner's parameters
   and of its unrelated local bindings. *)
Theorem return_cut_source_return:
  !fmp s w pc fuel ctx.
    lookup_var "arg" s = SOME w /\ lookup_var "pc" s = SOME pc ==>
    step_inst fuel ctx
      (LAST (HD (return_cut_inner fmp).fn_blocks).bb_instructions) s =
      IntRet <|iret_values := [w];
        iret_adopt_fmp := if fmp then SOME s.vs_fmp else NONE|> s
Proof
  rpt gen_tac >> strip_tac >> Cases_on `fmp` >>
  simp[return_cut_inner_def, mk_raw_function_def, mk_inst_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs,
    eval_operands_def, eval_operand_def]
QED

Theorem return_cut_resumed_output:
  !t caller w.
    lookup_var "inl1_answer" (update_var "inl1_answer" w t) =
      lookup_var "answer" (THE (bind_outputs ["answer"] [w] caller)) /\
    inline_shared_frame (update_var "inl1_answer" w t) = inline_shared_frame t /\
    update_var "inl1_answer" w t =
      FOLDL (\u (x,v). update_var x v u) t
        (ZIP (MAP (STRCAT (inline_prefix 1)) ["answer"], [w]))
Proof
  `inline_prefix 1 = "inl1_"` by EVAL_TAC >>
  simp[bind_outputs_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    functionInlinerFrameTheory.inline_shared_frame_def]
QED

(* RET preserves the SAVED caller FMP; RETFMP adopts the LIVE child's FMP.
   No equality of those two values is needed or asserted. *)
Theorem return_cut_adopt_fmp:
  !fmp child caller w.
    (adopt_return_fmp
      <|iret_values := [w];
        iret_adopt_fmp := if fmp then SOME child.vs_fmp else NONE|>
      caller).vs_fmp = if fmp then child.vs_fmp else caller.vs_fmp
Proof
  Cases >> simp[]
QED

Theorem return_cut_source_to_adapter:
  !fmp s t caller w pc fuel ctx.
    lookup_var "arg" s = SOME w /\ lookup_var "pc" s = SOME pc /\
    lookup_var "inl1_inl0_arg" t = lookup_var "arg" s /\ ~t.vs_halted ==>
    ?bb ir u.
      step_inst fuel ctx
        (LAST (HD (return_cut_inner fmp).fn_blocks).bb_instructions) s =
        IntRet ir s /\
      lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
      exec_block fuel ctx bb
        (t with vs_inst_idx := if fmp then 3 else 2) =
        OK (jump_to "inl1_inl0_inline_return0" u) /\
      u = FOLDL (\u (x,v). update_var x v u) t
        (ZIP (MAP (STRCAT (inline_prefix 1)) ["answer"], ir.iret_values)) /\
      lookup_var "inl1_answer" u =
        lookup_var "answer" (THE (bind_outputs ["answer"] ir.iret_values caller)) /\
      inline_shared_frame u = inline_shared_frame t /\
      (adopt_return_fmp ir caller).vs_fmp =
        if fmp then s.vs_fmp else caller.vs_fmp
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_var "inl1_inl0_arg" t = SOME w` by simp[] >>
  drule_all return_cut_execute >>
  disch_then (qspecl_then [`fmp`, `fuel`, `ctx`] strip_assume_tac) >>
  `inline_prefix 1 = "inl1_"` by EVAL_TAC >>
  qexistsl_tac [`bb`,
    `<|iret_values := [w];
       iret_adopt_fmp := if fmp then SOME s.vs_fmp else NONE|>`,
    `update_var "inl1_answer" w t`] >>
  conj_tac >- (irule return_cut_source_return >> simp[]) >>
  mp_tac (Q.SPECL [`t`, `caller`, `w`] return_cut_resumed_output) >>
  simp[return_cut_adopt_fmp]
QED

(* Generalization checkpoint: these equations execute actual produced code,
   but do not construct a reachable multi-edit stack.  The general mutual
   evaluator predicate must carry original activation and original child run,
   route, suspended logical snapshots, physical owner frames, source phase,
   and an administrative cut (residual list and offset).  In particular the
   active shared-frame relation and nonhaltedness belong to that cut, not to
   an inactive saved caller snapshot.  General layout/namespace containment,
   protected remote ancestors, entry/PHI transitions and fuel composition
   remain obligations of the existing recursive transport frontier. *)

Theorem return_cut_destination_layout:
  !fmp. ?bb.
    lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
    FLAT (MAP (\i. i.inst_outputs)
      (TAKE (if fmp then 3 else 2) bb.bb_instructions)) =
      (if fmp then ["inl1_inl0_arg"; "inl1_inl0_fp"; "inl1_inl0_pc"]
       else ["inl1_inl0_arg"; "inl1_inl0_pc"]) /\
    FLAT (MAP (\i. i.inst_outputs)
      (DROP (if fmp then 3 else 2) bb.bb_instructions)) = ["inl1_answer"]
Proof
  Cases >> EVAL_TAC >> simp[]
QED

Theorem return_cut_namespace_support:
  !fmp.
    set (cfgTransform$fn_all_vars (return_cut_middle fmp)) =
      (if fmp then {"mpc"; "mf"; "answer"} else {"mpc"; "answer"}) /\
    set (cfgTransform$fn_all_vars return_cut_outer) = {"result"}
Proof
  Cases >> EVAL_TAC >> simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem return_cut_entry_avoids:
  inline_tracked_snapshot (return_cut_middle fmp) ma mr ms frame /\
  inline_tracked_snapshot return_cut_outer oa opr os frame /\
  mr.ir_rename = STRCAT "inl1_" /\ opr.ir_rename = I /\
  ms.ils_protected = {} /\ os.ils_protected = {} /\
  MEM d (if fmp then ["inl1_inl0_arg"; "inl1_inl0_fp"; "inl1_inl0_pc"]
         else ["inl1_inl0_arg"; "inl1_inl0_pc"]) ==>
  inline_suspended_avoids [(ma,mr,ms);(oa,opr,os)] d
Proof
  strip_tac >>
  `ms.ils_defined SUBSET set (cfgTransform$fn_all_vars (return_cut_middle fmp)) /\
   os.ils_defined SUBSET set (cfgTransform$fn_all_vars return_cut_outer)` by
    fs[inline_tracked_snapshot_def] >>
  qpat_x_assum `inline_tracked_snapshot _ _ _ _ _` kall_tac >>
  qpat_x_assum `inline_tracked_snapshot _ _ _ _ _` kall_tac >>
  fs[return_cut_namespace_support] >>
  Cases_on `fmp` >>
  full_simp_tac bool_ss [COND_CLAUSES, MEM] >>
  asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [inline_suspended_avoids_def,
    EVERY_DEF, pred_setTheory.NOT_IN_EMPTY] >>
  conj_tac >> gen_tac >> disch_tac >>
  first_x_assum (drule_then mp_tac o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
  pure_asm_rewrite_tac [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
  strip_tac >> gvs[]
QED

Theorem return_cut_return_avoids_outer:
  inline_tracked_snapshot return_cut_outer oa opr os frame /\
  opr.ir_rename = I /\ os.ils_protected = {} ==>
  inline_suspended_avoids [(oa,opr,os)] "inl1_answer"
Proof
  strip_tac >>
  `os.ils_defined SUBSET set (cfgTransform$fn_all_vars return_cut_outer)` by
    fs[inline_tracked_snapshot_def] >>
  fs[return_cut_namespace_support, pred_setTheory.SUBSET_DEF] >>
  simp[inline_suspended_avoids_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem return_cut_entry_preserves_ancestors:
  inline_tracked_snapshot (return_cut_middle fmp) ma mr ms frame /\
  inline_tracked_snapshot return_cut_outer oa opr os frame /\
  ma.ia_function = return_cut_middle fmp /\ oa.ia_function = return_cut_outer /\
  mr.ir_rename = STRCAT "inl1_" /\ opr.ir_rename = I /\
  ms.ils_protected = {} /\ os.ils_protected = {} /\
  lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
  EVERY (\(d,w). MEM d (FLAT (MAP (\i. i.inst_outputs)
    (TAKE (if fmp then 3 else 2) bb.bb_instructions)))) writes ==>
  inline_suspended_observations [(ma,mr,ms);(oa,opr,os)]
    (frame with ipf_state :=
      FOLDL (\s (d,w). update_var d w s) frame.ipf_state writes)
Proof
  strip_tac >>
  qspec_then `fmp` strip_assume_tac return_cut_destination_layout >>
  gvs[] >> irule inline_suspended_writes >>
  simp[inline_suspended_observations_def] >>
  fs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
  gvs[] >>
  qpat_x_assum `!e. MEM e writes ==> _` (qspec_then `(e0,e1)` mp_tac) >>
  simp[] >> strip_tac >> irule return_cut_entry_avoids >> metis_tac[]
QED

Theorem return_cut_pop_preserves_outer:
  inline_tracked_snapshot return_cut_outer oa opr os frame /\
  oa.ia_function = return_cut_outer /\
  opr.ir_rename = I /\ os.ils_protected = {} ==>
  inline_suspended_observations [(oa,opr,os)]
    (frame with ipf_state := update_var "inl1_answer" w frame.ipf_state)
Proof
  strip_tac >> irule inline_suspended_write >>
  simp[inline_suspended_observations_def] >>
  irule return_cut_return_avoids_outer >> metis_tac[]
QED

(* Phase boundary: the middle observation is popped before the output write.
   The outer tail survives; the resumed middle output is related to the
   original bind_outputs result, without preserving its old answer binding.
   General interface still required:
     original_child ... /\ reachable_cut ... (parent::ancestors) /\
     original_return ... ==> ?cut'. reachable_cut ... ancestors /\
       resumed_parent ... /\ administrative_return_segment ... .
   Here reachable_cut must PRODUCE ancestor namespace containment from actual
   edits. It must not take all-observation avoidance as a return premise. *)
Theorem return_cut_source_to_popped_adapter:
  lookup_var "arg" s = SOME w /\ lookup_var "pc" s = SOME pc /\
  lookup_var "inl1_inl0_arg" frame.ipf_state = lookup_var "arg" s /\
  ~frame.ipf_state.vs_halted /\
  inline_tracked_snapshot return_cut_outer oa opr os frame /\
  oa.ia_function = return_cut_outer /\ opr.ir_rename = I /\
  os.ils_protected = {} ==>
  ?bb ir u.
    step_inst fuel ctx
      (LAST (HD (return_cut_inner fmp).fn_blocks).bb_instructions) s =
      IntRet ir s /\
    lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
    exec_block fuel ctx bb
      (frame.ipf_state with vs_inst_idx := if fmp then 3 else 2) =
      OK (jump_to "inl1_inl0_inline_return0" u) /\
    inline_suspended_observations [(oa,opr,os)] (frame with ipf_state := u) /\
    lookup_var "inl1_answer" u =
      lookup_var "answer" (THE (bind_outputs ["answer"] ir.iret_values caller)) /\
    inline_shared_frame u = inline_shared_frame frame.ipf_state /\
    (adopt_return_fmp ir caller).vs_fmp =
      if fmp then s.vs_fmp else caller.vs_fmp
Proof
  strip_tac >>
  drule_all return_cut_source_to_adapter >>
  disch_then (qspecl_then [`fmp`, `caller`, `fuel`, `ctx`] strip_assume_tac) >>
  `ir = <|iret_values := [w];
          iret_adopt_fmp := if fmp then SOME s.vs_fmp else NONE|>` by
    (drule_all return_cut_source_return >>
     disch_then (qspecl_then [`fmp`, `fuel`, `ctx`] mp_tac) >> simp[]) >>
  `inline_prefix 1 = "inl1_"` by EVAL_TAC >>
  gvs[] >> qexists `update_var "inl1_answer" w frame.ipf_state` >>
  simp[] >> irule return_cut_pop_preserves_outer >> metis_tac[]
QED
