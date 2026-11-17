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
  EVERY is_simple_stack_op ops /\ prefix_wf lo (LENGTH ps.ps_stack) ops /\
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
