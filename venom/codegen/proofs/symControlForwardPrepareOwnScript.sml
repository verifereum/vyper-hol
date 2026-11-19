(* Forwarded-revert preparation. Lower subject interfaces below are transparent
   parser abbreviations, not logical definitions; final control assembly supplies
   their already proved statements. *)
Theory symControlForwardPrepareOwn
Ancestors
  asmSplice codegenSymRel fnFrameStepsRevertForward asmSymBridge[qualified,ignore_grammar]
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs symPlannerSim symShuffleSim asmSymPc codegenEncodingWf
  spillPlanSim reorderStages inputMaterialised reduceDepthSim mixedPrefixSim
  symFrameControlFacts

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

val _ = Parse.temp_overload_on ("rf_place", ``\dfg pending op f ps.
  case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
    NONE => ([],ps)
  | SOME d => if d = f then ([],ps)
    else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
    then ([],ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
    else (case do_swap d ps of (ops1,ps1) =>
      case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2))``);

val _ = Parse.temp_overload_on ("rf_E", ``!inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins,ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ins /\ ~MEM (SORestore off) ins) ==>
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack``);
val _ = Parse.temp_overload_on ("rf_T", ``!xs vals ys fn ret.
  LIST_REL (op_kind_ok fn ret) xs vals /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs ys ==>
  LIST_REL (op_kind_ok fn ret) ys vals``);
val _ = Parse.temp_overload_on ("rf_D", ``!dfg pending idx op ps ops ps'.
  reorder_one dfg pending idx op ps = (ops,ps') ==>
  ?restore_ops ps1.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ((stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps1.ps_stack = NONE /\ ops = restore_ops /\ ps' = ps1) \/
     ?dist reduce_ops ps2 suffix.
       stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
         (LENGTH pending) ps1.ps_stack = SOME dist /\
       (if dist > 16 then reduce_depth_plan (LENGTH ps1.ps_stack) pending op
         (LENGTH pending - (idx + 1)) (LENGTH pending) ps1
        else ([],ps1)) = (reduce_ops,ps2) /\
       ops = (restore_ops ++ reduce_ops) ++ suffix /\
       ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
       rf_place dfg pending op (LENGTH pending - (idx + 1)) ps2 = (suffix,ps'))``);
val _ = Parse.temp_overload_on ("rf_P", ``!dfg (pending : operand list) op f ps ops ps' fn ret qs fmp lo.
  rf_place dfg pending op f ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack``);
val _ = Parse.temp_overload_on ("rf_Irestore", ``!op f n ps ops ps1.
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SORestore off) ops) ==> ops = [] /\ ps1 = ps``);
val _ = Parse.temp_overload_on ("rf_Ireduce", ``!dist ps pending op f n ops ps1.
  (if (dist:num) > 16 then reduce_depth_plan (LENGTH ps.ps_stack) pending op f n ps
   else ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SOSpill off) ops) ==> ops = [] /\ ps1 = ps``);
val _ = Parse.temp_overload_on ("rf_S", ``!d ps ops ps'.
  do_swap d ps = (ops,ps') /\ (!off. ~MEM (SORestore off) ops) ==> d <= 16``);
val _ = Parse.temp_overload_on ("rf_W", ``!d ps ops ps' initial_fmp lo.
  do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\ EVERY is_prefix_op ops /\
  EVERY (\op. !l n. op <> SOPushOfst l n) ops /\ (!off. ~MEM (SOSpill off) ops)``);
val _ = Parse.temp_overload_on ("rf_B", ``rf_E /\ rf_T /\ rf_D /\ rf_P /\
  rf_Irestore /\ rf_Ireduce /\ rf_S /\ rf_W``);

Theorem reorder_one_spill_free_placement_conditional:
  rf_B ==>
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  rf_place dfg pending op (LENGTH pending - (idx + 1)) ps = (ops,ps')
Proof
  disch_tac >> strip_tac >>
  qpat_assum `rf_B` (drule_then strip_assume_tac o cj 3)
  >- (`restore_ops = [] /\ ps1 = ps` by
        (qpat_assum `rf_B` (drule_then irule o cj 5) >> metis_tac[]) >>
      qpat_x_assum `rf_B` kall_tac >> gvs[]) >>
  `restore_ops = [] /\ ps1 = ps` by
    (qpat_assum `rf_B` (drule_then irule o cj 5) >>
     fs[IgnAsm `rf_B`, listTheory.MEM_APPEND] >> metis_tac[]) >>
  qpat_x_assum `rf_B` (fn th => gvs[] >> assume_tac th) >>
  `reduce_ops = [] /\ ps2 = ps` by
    (qpat_assum `rf_B` (drule_then irule o cj 6) >>
     fs[IgnAsm `rf_B`, listTheory.MEM_APPEND] >> metis_tac[]) >>
  gvs[IgnAsm `rf_B`]
QED

Theorem reorder_one_spill_free_kind_replay_conditional:
  rf_B ==>
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  disch_then (fn bundle => let
    val placement = MP (SPEC_ALL reorder_one_spill_free_placement_conditional) bundle
    val kind_replay = BETA_RULE (cj 4 bundle)
  in
    strip_tac >> drule placement >>
    (impl_tac >- metis_tac[]) >> strip_tac >>
    RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
    drule kind_replay >> disch_then irule >> metis_tac[]
  end)
QED

Theorem reorder_steps_spill_free_kind_replay_conditional:
  rf_B ==>
  !items ps qs ops ps' dfg pending fn ret fmp lo.
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  disch_then (fn bundle => let
    val step_rule = MP (SPEC_ALL reorder_one_spill_free_kind_replay_conditional) bundle
  in
    Induct
    >- simp[foldlSimTheory.plan_steps_def, mixedPrefixSimTheory.apply_prefix_ops_def] >>
    Cases_on `h` >> rpt gen_tac >>
    simp[foldlSimTheory.plan_steps_def] >>
    Cases_on `reorder_one dfg pending q r ps` >>
    rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
    Cases_on `plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items mid` >>
    simp[] >> strip_tac >>
    gvs[listTheory.MEM_APPEND, planAlignTheory.apply_prefix_ops_append] >>
    first_x_assum irule >> simp[] >> metis_tac[step_rule]
  end)
QED

Theorem reorder_plan_spill_free_kind_replay_conditional:
  rf_B ==>
  reorder_plan dfg pending ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  disch_then (fn bundle => let
    val steps_rule = MP (SPEC_ALL reorder_steps_spill_free_kind_replay_conditional) bundle
  in
    rewrite_tac[reorderStagesTheory.reorder_plan_eq_plan_steps] >>
    metis_tac[steps_rule]
  end)
QED

Theorem sym_spill_free_stack_only_prefix_sim:
  !ops lo ps ss top srest fn ret cp p fmp env.
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest
      (apply_prefix_ops fmp lo ops (ps with ps_spilled := FEMPTY)) ss' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> rename1 `!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b` >>
  `sym_kinds_ok cplan fn ret srest (ps with ps_spilled := FEMPTY) ss` by
    (simp[sym_kinds_ok_def] >> metis_tac[]) >>
  `prefix_spill_wf fmp lo ops (ps with ps_spilled := FEMPTY)` by
    metis_tac[singleInputSimTheory.simple_prefix_spill_wf] >>
  `!op. is_simple_stack_op op ==> is_prefix_op op /\
     (!l d. op <> SOPushOfst l d) /\ (!off. op <> SOSpill off)` by
    (Cases >> simp[strongPrefixSimTheory.is_simple_stack_op_def,
                  prefixSimTheory.is_prefix_op_def] >>
     Cases_on `o'` >> simp[strongPrefixSimTheory.is_simple_stack_op_def]) >>
  `EVERY is_prefix_op ops /\ EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
   (!off. ~MEM (SOSpill off) ops)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `prefix_wf lo (LENGTH (ps with ps_spilled := FEMPTY).ps_stack) ops` by simp[] >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
     (\b:num. F) b /\ context_spill_byte cplan b` by simp[] >>
  drule_all (Q.INST [`R` |-> `\b:num. F`] (SPEC_ALL sym_prefix_ops_sim)) >>
  simp[] >> metis_tac[]
QED

Theorem sym_rf_preparation_stack_sim_conditional:
  rf_B ==>
  !opc inputs nl ps ins ps1 fn ros ps2 (lo:string |-> num) ss top srest ret cp p fmp env.
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (ins ++ ros)) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  disch_then (fn bundle => let
    val emit_rule = cj 1 bundle
    val reorder_rule = MP (SPEC_ALL reorder_plan_spill_free_kind_replay_conditional) bundle
  in
  rpt gen_tac >> strip_tac >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\ ~MEM (SORestore off) (ins ++ ros)` by
    (fs[listTheory.EVERY_MEM] >>
     metis_tac[strongPrefixSimTheory.is_simple_stack_op_def]) >>
  `(apply_prefix_ops fmp lo ins (ps with ps_spilled := FEMPTY)).ps_stack = ps1.ps_stack` by
    (drule emit_rule >> disch_then irule >>
     simp[] >> fs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  `LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
     (apply_prefix_ops fmp lo (ins ++ ros) (ps with ps_spilled := FEMPTY)).ps_stack
     ps2.ps_stack` by
    (rewrite_tac[planAlignTheory.apply_prefix_ops_append] >>
     irule reorder_rule >>
     simp[] >> fs[listTheory.MEM_APPEND] >>
     qexistsl [`inputs`, `ps1`] >> simp[] >>
     irule listTheory.EVERY2_refl >> simp[]) >>
  drule_all sym_spill_free_stack_only_prefix_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  fs[sym_kinds_ok_def] >>
  irule list_rel_op_kind_transport >> metis_tac[listTheory.LIST_REL_REVERSE]
  end)
QED

val rf_bundle_tm = fst (dest_imp (snd (strip_forall
  (concl reorder_one_spill_free_kind_replay_conditional))));
val _ = Parse.temp_overload_on ("rf_B", rf_bundle_tm);

Theorem assign_output_op_kind:
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs ==>
  (op_kind_ok fn ret rhs sv <=> op_kind_ok fn ret (Var out) sv)
Proof
  strip_tac >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `dfg_get_def (dfg_build_function fn) out = SOME inst` by
    metis_tac[fnFrameStepsRevertForwardTheory.dfg_build_function_ssa_def,
              listTheory.MEM] >>
  drule_all fnFrameStepsRevertForwardTheory.normalize_operand_codegen_assign >>
  metis_tac[op_kind_ok_normalize_operand]
QED

Theorem assign_prepared_stack_op_kind:
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [rhs])) top ==>
  LIST_REL (op_kind_ok fn ret) (REVERSE (stack_push (Var out) tail)) top
Proof
  Cases_on `top` >> simp[stackModelTheory.stack_push_def] >>
  metis_tac[assign_output_op_kind]
QED

Theorem simple_do_swap_replay_wf_conditional:
  rf_B ==>
  do_swap d ps = (ops,ps') /\ d < LENGTH ps.ps_stack /\
  EVERY is_simple_stack_op ops ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  apply_prefix_ops fmp lo ops ps = ps'
Proof
  disch_then (fn bundle => let
    val shallow = cj 7 bundle
    val prefix_facts = cj 8 bundle
  in
    strip_tac >>
    `!off. ~MEM (SORestore off) ops` by
      (fs[listTheory.EVERY_MEM] >>
       metis_tac[strongPrefixSimTheory.is_simple_stack_op_def]) >>
    `d <= 16` by metis_tac[shallow] >>
    metis_tac[prefix_facts, planAlignTheory.do_swap_align]
  end)
QED

Theorem optimistic_simple_replay_wf_conditional:
  rf_B ==>
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  EVERY is_simple_stack_op ops ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  apply_prefix_ops fmp lo ops ps = ps'
Proof
  disch_then (fn bundle => let
    val swap_rule = MP (SPEC_ALL simple_do_swap_replay_wf_conditional) bundle
  in
    simp[optimistic_swap_plan_def] >>
    rpt (IF_CASES_TAC >> simp[]) >>
    Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >>
    simp[] >> rpt strip_tac >> gvs[] >>
    simp[mixedPrefixSimTheory.apply_prefix_ops_def, prefixExecTheory.prefix_wf_def] >>
    metis_tac[swap_rule, planAlignTheory.stack_get_depth_bound]
  end)
QED

Theorem simple_prefix_equal_stack_replay:
  !ops ps qs fmp lo.
  EVERY is_simple_stack_op ops /\ qs.ps_stack = ps.ps_stack ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack =
    (apply_prefix_ops fmp lo ops ps).ps_stack
Proof
  Induct >> simp[mixedPrefixSimTheory.apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  Cases_on `h` >>
  gvs[strongPrefixSimTheory.is_simple_stack_op_def,
      mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def] >>
  Cases_on `o'` >>
  gvs[strongPrefixSimTheory.is_simple_stack_op_def,
      mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def]
QED

Theorem sym_simple_prefix_stack_sim:
  !ops lo ps ps' ss top srest fn ret cp p fmp env.
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  (apply_prefix_ops fmp lo ops ps).ps_stack = ps'.ps_stack /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `(apply_prefix_ops fmp lo ops (ps with ps_spilled := FEMPTY)).ps_stack = ps'.ps_stack` by
    metis_tac[simple_prefix_equal_stack_replay, plan_state_accfupds] >>
  drule_all sym_spill_free_stack_only_prefix_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  fs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem assign_postfix_simple_replay_wf_conditional:
  rf_B ==>
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) ==>
  prefix_wf lo (LENGTH ps.ps_stack) (pops ++ opts) /\
  (apply_prefix_ops fmp lo (pops ++ opts) ps).ps_stack =
    (release_dead_spills nl ps9).ps_stack
Proof
  disch_then (fn bundle => let
    val optimistic_rule = MP (SPEC_ALL optimistic_simple_replay_wf_conditional) bundle
  in
    strip_tac >> Cases_on `MEM out nl`
    >- (`pops = [] /\ ps8 = ps` by
          (Cases_on `halting` >> gvs[stackPlanOpsTheory.popmany_plan_def]) >>
        gvs[] >> drule_all optimistic_rule >>
        disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
        gvs[stackModelTheory.stack_push_def, arithmeticTheory.ADD1]) >>
    gvs[] >> Cases_on `halting`
    >- gvs[mixedPrefixSimTheory.apply_prefix_ops_def, prefixExecTheory.prefix_wf_def] >>
    `stack_get_depth (Var out) ps.ps_stack = SOME 0` by
      simp[stackModelTheory.stack_push_def, listTheory.REVERSE_SNOC,
           stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def] >>
    `popmany_plan [Var out] ps =
       ([SOPop 1],ps with ps_stack := stack_pop 1 ps.ps_stack)` by
      metis_tac[regularPostfixSimTheory.popmany_plan_top_singleton] >>
    gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
        mixedPrefixSimTheory.apply_prefix_op_def,
        strongPrefixSimTheory.apply_simple_op_def,
        prefixExecTheory.prefix_wf_def, prefixExecTheory.stack_op_wf_def,
        stackModelTheory.stack_push_def, stackModelTheory.stack_pop_def]
  end)
QED

Theorem sym_assign_postfix_stack_sim_conditional:
  rf_B ==>
  !ps out tail halting nl pops ps8 dfg inst term opts ps9 (lo:string |-> num) ss top srest fn ret cp p fmp env.
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (pops ++ opts)) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp (pops ++ opts))) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (release_dead_spills nl ps9).ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  disch_then (fn bundle => let
    val postfix_rule = MP (SPEC_ALL assign_postfix_simple_replay_wf_conditional) bundle
  in
    rpt gen_tac >> strip_tac >> rename1 `context_spill_byte cp0` >>
    drule_all postfix_rule >>
    disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
    irule sym_simple_prefix_stack_sim >> simp[] >>
    conj_tac >- (qexists_tac `cp0` >> simp[]) >>
    qexistsl_tac [`lo`, `ps`] >> simp[]
  end)
QED

Theorem rf_assign_preparation_stack_facts:
  emit_input_plan ASSIGN [rhs] nl ps = (ins,ps1) /\
  reorder_plan dfg [rhs] ps1 = (ros,ps2) /\
  ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)) ==>
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf (lo:string |-> num) (LENGTH ps.ps_stack) (ins ++ ros) /\
  ps2.ps_stack = stack_pop 1 ps2.ps_stack ++ [rhs]
Proof
  strip_tac >> rpt conj_tac
  >- metis_tac[fnFrameStepsRevertForwardTheory.spill_free_preparation_simple]
  >- (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
      qexistsl_tac [`dfg`, `[rhs]`, `nl`, `ASSIGN`, `ps1`, `ps2`] >>
      simp[] >> metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `!op. MEM op [rhs] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by simp[] >>
  `LENGTH [rhs] <= 16` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_preparation_arranged >> simp[]
QED

Theorem sym_assign_prepared_stack_sim:
  !ps2 tail rhs fn inst out ret ss top srest.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  ps2.ps_stack = tail ++ [rhs] /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top ==>
  LIST_REL (op_kind_ok fn ret)
    (REVERSE (ps2 with ps_stack := stack_push (Var out) tail).ps_stack) top
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  irule assign_prepared_stack_op_kind >> metis_tac[]
QED

Theorem rf_assign_postfix_simple:
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  (!off. ~MEM (SOSpill off) (pops ++ opts) /\
         ~MEM (SORestore off) (pops ++ opts)) ==>
  EVERY is_simple_stack_op (pops ++ opts)
Proof
  strip_tac >>
  irule fnFrameStepsRevertForwardTheory.spill_free_postfix_simple >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`dfg`, `~halting`, `inst`,
    `if MEM out nl then [] else [Var out]`, `nl`, `~MEM out nl`,
    `term`, `ps`, `ps8`, `ps9`] >>
  Cases_on `halting` >> Cases_on `MEM out nl` >> gvs[]
QED

Theorem sym_plan_runs_compose:
  sym_steps p env (LENGTH (execute_plan fmp ops1)) ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan fmp ops2)) mid = SymOK final ==>
  sym_steps p env (LENGTH (execute_plan fmp (ops1 ++ ops2))) ss = SymOK final
Proof
  simp[stackOpSimTheory.execute_plan_append, sym_steps_add]
QED

val rf_bundle_tm = fst (dest_imp (snd (strip_forall
  (concl reorder_one_spill_free_kind_replay_conditional))));
val _ = Parse.temp_overload_on ("rf_B", rf_bundle_tm);
val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

Theorem sym_rf_suffix_preparation_execution_mode_conditional:
  rf_B ==>
  !allow_own code_ok own fn ps opc inputs nl ins ps1 ros ps2 ra lo entry s stk st rest prog fmp
   env ss top srest ret cp.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inputs /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. MEM op inputs ==> operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)) /\
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
  asm_static_wf prog /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra s) ps2.ps_stack stk' /\
    rf_inventory_inv fn ra lo entry ps2 s /\
    ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    bridge_core lo code_ok mid ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  disch_then (fn bundle => assume_tac
    (MP (SPEC_ALL sym_rf_preparation_stack_sim_conditional) bundle)) >>
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `context_spill_byte cplan` >>
  pop_last_assum (mk_asm "preparation") >>
  qpat_x_assum `!n cs ss ss'. bridge_core _ _ cs ss /\ sym_steps_mode _ _ _ _ n ss = SymOK ss' ==> _`
    (mk_asm "correspondence") >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `ss.sym_base.as_pc = st.as_pc` by
    (qpat_assum `?m. _` strip_assume_tac >> simp[]) >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan fmp (ins ++ ros))` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_preparation_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  asm_x "preparation" drule_all >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  asm_x "correspondence" drule_all >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem sym_rf_copy_preparation_execution_mode_conditional:
  rf_B ==>
  !allow_own code_ok own cp.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop 3 ps2.ps_stack ++ [zop;sop;dop] /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    bridge_core lo code_ok mid ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)
Proof
  disch_then (fn bundle => assume_tac
    (MP (SPEC_ALL sym_rf_suffix_preparation_execution_mode_conditional) bundle)) >>
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  pop_last_assum (mk_asm "suffix") >>
  qpat_x_assum `!n cs ss ss'. bridge_core _ _ cs ss /\ sym_steps_mode _ _ _ _ n ss = SymOK ss' ==> _`
    (mk_asm "correspondence") >>
  `compute_operands inst = [zop;sop;dop]` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  `ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
   ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)` by
    (drule_all fnFrameStepsRevertForwardTheory.rf_copy_plan_result >>
     disch_then (fn th => fs[th])) >>
  `asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)))
     [AsmOp "RETURNDATACOPY"]` by
    gvs[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
        stackOpSimTheory.asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)` by fs[listTheory.MEM_APPEND] >>
  `RETURNDATACOPY <> INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
   EVERY (\op. ~is_label_operand op) (compute_operands inst)` by gvs[] >>
  `EVERY is_simple_stack_op (ins ++ ros)` by
    metis_tac[fnFrameStepsRevertForwardTheory.spill_free_preparation_simple] >>
  `prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros)` by
    (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
     qexistsl [`dfg_build_function fn`, `compute_operands inst`, `nl`, `RETURNDATACOPY`,
               `ps1`, `ps2`] >>
     simp[] >> gvs[] >> rpt strip_tac >> gvs[is_label_operand_def]) >>
  asm_x "correspondence" assume_tac >>
  asm_x "suffix" drule_all >> strip_tac >>
  qpat_x_assum `!n cs ss ss'. bridge_core _ _ cs ss /\ sym_steps_mode _ _ _ _ n ss = SymOK ss' ==> _`
    kall_tac >>
  qexistsl [`mid`, `ss'`, `stk'`, `top'`] >> gvs[] >> metis_tac[]
QED

Theorem sym_rf_assign_plan_execution_mode_conditional:
  rf_B ==>
  !allow_own code_ok own fn inst ps rhs out ra lo entry s fuel ctx s' lv cfg nl halting term lbl ops ps'
   stk st rest prog fmp env ss top srest ret cp.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?st' ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra s') ps'.ps_stack stk' /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok st' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  disch_then (fn bundle =>
    mk_asm "suffix" (MP (SPEC_ALL sym_rf_suffix_preparation_execution_mode_conditional) bundle) >>
    mk_asm "postfix" (MP (SPEC_ALL sym_assign_postfix_stack_sim_conditional) bundle)) >>
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `context_spill_byte cplan` >>
  qpat_x_assum `!n cs ss ss'. bridge_core _ _ cs ss /\ sym_steps_mode _ _ _ _ n ss = SymOK ss' ==> _`
    (mk_asm "correspondence") >>
  Cases_on `emit_input_plan ASSIGN [rhs] nl ps` >> rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) [rhs] ps1` >>
  rename1 `_ = (ros,ps2)` >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_plan_result >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)))
     (execute_plan fmp (pops ++ opts))` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
        listTheory.APPEND_ASSOC] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
    ~MEM (SORestore off) (ins ++ ros)` by fs[listTheory.MEM_APPEND] >>
  `!off. ~MEM (SOSpill off) (pops ++ opts) /\
    ~MEM (SORestore off) (pops ++ opts)` by fs[listTheory.MEM_APPEND] >>
  drule_all rf_assign_preparation_stack_facts >>
  disch_then (qspec_then `lo` strip_assume_tac) >>
  `ASSIGN <> INVOKE /\ LENGTH [rhs] <= 16 /\
   EVERY (\op. ~is_label_operand op) [rhs] /\
   (!op. MEM op [rhs] /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
   (!op. MEM op [rhs] ==> operand_val (frame_view fn ra s) lo op =
     operand_val entry lo (normalize_operand (dfg_build_function fn) [] op))` by gvs[] >>
  asm_x "correspondence" assume_tac >>
  asm_x "suffix" drule_all >> strip_tac >>
  qpat_x_assum `!n cs ss ss'. bridge_core _ _ cs ss /\ sym_steps_mode _ _ _ _ n ss = SymOK ss' ==> _`
    (mk_asm "correspondence") >>
  rename1 `sym_steps_mode allow_own prog env own _ ss = SymOK ss1` >>
  rename1 `ss1.sym_stack = prepared_top ++ srest` >>
  qabbrev_tac `pushed = ps2 with ps_stack :=
    stack_push (Var out) (stack_pop 1 ps2.ps_stack)` >>
  `LIST_REL (op_kind_ok fn ret) (REVERSE pushed.ps_stack) prepared_top` by
    (asm_x "postfix" kall_tac >> asm_x "correspondence" kall_tac >>
     simp[Abbr `pushed`] >> irule assign_prepared_stack_op_kind >> metis_tac[]) >>
  `EVERY is_simple_stack_op (pops ++ opts)` by
    (asm_x "postfix" kall_tac >> asm_x "correspondence" kall_tac >>
     metis_tac[rf_assign_postfix_simple]) >>
  `!b. b IN FDOM ss1.sym_mem_labels ==> context_spill_byte cplan b` by
    (asm_x "postfix" kall_tac >> asm_x "correspondence" kall_tac >>
     metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]) >>
  `ss1.sym_base.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros))` by
    simp[] >>
  `asm_block_at prog ss1.sym_base.as_pc (execute_plan fmp (pops ++ opts))` by (simp[] >> (gvs[])) >>
  `pushed.ps_stack = stack_push (Var out) (stack_pop 1 ps2.ps_stack)` by simp[Abbr `pushed`] >>
  asm_x "postfix" drule_all >>
  disch_then (qspecl_then [`lo`, `env`] strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  `sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss = SymOK ss'` by
    (`LENGTH (execute_plan fmp ops) =
        LENGTH (execute_plan fmp (ins ++ ros)) + LENGTH (execute_plan fmp (pops ++ opts))` by
       simp[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
     pop_assum (fn th => pure_once_rewrite_tac[th]) >>
     pure_once_rewrite_tac[sym_steps_mode_add] >> simp[]) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_plan_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  asm_x "correspondence" drule_all >> strip_tac >>
  gvs[] >> metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED
