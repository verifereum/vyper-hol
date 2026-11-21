(* Read-only control preparation.  The structural kind-exchange interface is
   discharged by the control join; no dependency on the old control owner. *)
Theory symControlReplayOwn
Ancestors
  symControlPrefixOwn symFrameControlFacts asmSymBridge[qualified,ignore_grammar] codegenSymRel
  symPlannerSim symShuffleSim stackPlanGen stackPlanTypes planExec asmSem
  asmSymSem frameRel contextCodegenRel unitShapeDefs dfgDefs asmSplice
  spillPlanSim reorderStages inputMaterialised reduceDepthSim mixedPrefixSim
  fnFrameStepsRevertForward reorderPreparationProps

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

Theorem restore_swap_sequence_member:
  MEM i idxs ==>
  MEM (SORestore (EL i offsets))
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) idxs))
Proof
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[listTheory.MEM]
QED

Theorem deep_dup_restore_sequence_member:
  31 < d ==>
  MEM (SORestore (EL (d - 16) offsets))
    (FLAT (MAP (\i. [SORestore (EL i offsets); SOSwap 1])
      (GENLIST (\i. d - (i + 16)) (d - 15))))
Proof
  strip_tac >> irule restore_swap_sequence_member >>
  simp[listTheory.MEM_GENLIST] >> qexists_tac `0` >> simp[]
QED

Theorem do_dup_no_restore_shallow:
  do_dup d ps = (ops, ps') /\
  (!off. ~MEM (SORestore off) ops) ==> d <= 15
Proof
  Cases_on `d <= 15` >- simp[] >>
  simp[stackPlanOpsTheory.do_dup_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >> qexists_tac `EL (d - 16) offsets` >>
  `MEM (d - 16) (dup_restore_indices (d - 15))` by
    (Cases_on `d <= 31` >>
     fs[stackPlanOpsTheory.dup_restore_indices_explicit, listTheory.MEM_GENLIST] >>
     qexists_tac `0` >> simp[]) >>
  simp[listTheory.MEM_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
  metis_tac[listTheory.MEM]
QED

Theorem do_dup_read_only_shallow:
  do_dup d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops) ==> d <= 15
Proof
  Cases_on `d <= 15` >- simp[] >> strip_tac >>
  `d > 15` by decide_tac >>
  drule_all doSwapSimTheory.do_dup_big_decompose >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
  qmatch_asmsub_abbrev_tac `FST (spill_alloc_n [] ps.ps_alloc items)` >>
  `FST (spill_alloc_n [] ps.ps_alloc items) = []` by
    (Cases_on `FST (spill_alloc_n [] ps.ps_alloc items)` >> gvs[] >>
     metis_tac[listTheory.MEM]) >>
  pop_assum (mp_tac o AP_TERM ``LENGTH:num list -> num``) >>
  simp[doSwapSimTheory.spill_alloc_n_offsets_length, Abbr`items`,
       stackPlanOpsTheory.top_n_def, listTheory.LENGTH_TAKE_EQ] >> rw[] >> decide_tac
QED

Theorem do_restore_read_only_replay:
  do_restore op ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[stackPlanOpsTheory.do_restore_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, mixedPrefixSimTheory.prefix_spill_wf_def,
      mixedPrefixSimTheory.spill_op_wf_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `spill_lookup off ps.ps_spilled = op` by
    (simp[mixedPrefixSimTheory.spill_lookup_def] >>
     metis_tac[planAlignTheory.spill_hilbert_unique]) >> simp[] >> metis_tac[]
QED

Theorem do_dup_read_only_replay:
  do_dup d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> drule_all do_dup_read_only_shallow >> strip_tac >>
  gvs[stackPlanOpsTheory.do_dup_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def,
      stackModelTheory.stack_dup_def, stackModelTheory.stack_peek_def]
QED

Theorem emit_var_input_unspilled_read_only_replay:
  FLOOKUP ps.ps_spilled (Var v) = NONE /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
  strip_tac >> Cases_on `MEM v nl` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.prefix_spill_wf_def] >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.prefix_spill_wf_def] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  Cases_on `do_dup dist ps` >> gvs[] >>
  metis_tac[do_dup_read_only_replay, planAlignTheory.stack_get_depth_bound]
QED

Theorem emit_var_input_spilled_read_only_replay:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >>
  `spill_lookup off ps.ps_spilled = Var v` by
    (simp[mixedPrefixSimTheory.spill_lookup_def] >>
     metis_tac[planAlignTheory.spill_hilbert_unique]) >>
  Cases_on `MEM v nl` >>
  gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
      stackPlanOpsTheory.do_restore_def, stackPlanOpsTheory.do_dup_def,
      stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def,
      stackModelTheory.stack_push_def, stackModelTheory.stack_dup_def,
      stackModelTheory.stack_peek_def, listTheory.REVERSE_SNOC, listTheory.EL_SNOC,
      mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def] >>
  metis_tac[]
QED

Theorem emit_one_input_read_only_replay:
  emit_one_input opc nl op ps = (ops, ps') /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Cases_on `op`
  >- (rpt strip_tac >>
      gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
          mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
          strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def,
          mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def])
  >- (strip_tac >> rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (irule emit_var_input_unspilled_read_only_replay >> simp[] >> metis_tac[]) >>
      irule emit_var_input_spilled_read_only_replay >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
      mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def]
QED

Theorem emit_input_plan_read_only_replay:
  !inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins, ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ins) /\
  (!off. MEM (SORestore off) ins ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ins qs /\
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack /\
  (apply_prefix_ops fmp lo ins qs).ps_spilled = ps1.ps_spilled
Proof
  Induct >> simp[emit_input_plan_def, mixedPrefixSimTheory.apply_prefix_ops_def,
                mixedPrefixSimTheory.prefix_spill_wf_def] >> rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars inputs ++ nl) h ps` >>
  Cases_on `emit_input_plan opc inputs nl r` >> simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all emit_one_input_read_only_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  `!op1 off1 op2 off2.
    FLOOKUP r.ps_spilled op1 = SOME off1 /\
    FLOOKUP r.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (drule_at Any doSwapSimTheory.safe_prefix_spilled_separated >>
     simp[] >> disch_then assume_tac >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum drule >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem do_dup_spill_free_stack_replay:
  do_dup d ps = (ops, ps') /\ qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  strip_tac >> drule do_dup_no_restore_shallow >> simp[] >> strip_tac >>
  gvs[stackPlanOpsTheory.do_dup_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      stackModelTheory.stack_dup_def, stackModelTheory.stack_peek_def]
QED

Theorem emit_var_input_unspilled_stack_replay:
  FLOOKUP ps.ps_spilled (Var v) = NONE /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ (!off. ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
  strip_tac >> Cases_on `MEM v nl` >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def] >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  Cases_on `do_dup dist ps` >> gvs[] >> metis_tac[do_dup_spill_free_stack_replay]
QED

Theorem emit_var_input_spilled_has_restore:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\
  emit_one_input opc nl (Var v) ps = (ops, ps') ==>
  MEM (SORestore off) ops
Proof
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       stackPlanOpsTheory.do_restore_def] >>
  strip_tac >> Cases_on `MEM v nl` >> gvs[] >>
  Cases_on `stack_get_depth (Var v) (stack_push (Var v) ps.ps_stack)` >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem emit_one_input_spill_free_stack_replay:
  emit_one_input opc nl op ps = (ops, ps') /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  Cases_on `op`
  >- (rpt strip_tac >> gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
           mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
           strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def])
  >- (rpt strip_tac >> Cases_on `FLOOKUP ps.ps_spilled (Var s)` >>
      metis_tac[emit_var_input_unspilled_stack_replay, emit_var_input_spilled_has_restore]) >>
  rpt strip_tac >> gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
       strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def]
QED

Theorem emit_input_plan_spill_free_stack_replay:
  !inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins, ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ins /\ ~MEM (SORestore off) ins) ==>
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack
Proof
  Induct >> simp[emit_input_plan_def, mixedPrefixSimTheory.apply_prefix_ops_def] >>
  rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars inputs ++ nl) h ps` >>
  Cases_on `emit_input_plan opc inputs nl r` >> simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum irule >> simp[] >> metis_tac[emit_one_input_spill_free_stack_replay]
QED

Theorem do_restore_read_only_kind_replay:
  do_restore op ps = (ops, ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[stackPlanOpsTheory.do_restore_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, mixedPrefixSimTheory.prefix_spill_wf_def,
      mixedPrefixSimTheory.spill_op_wf_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `spill_lookup off ps.ps_spilled = op` by
    (simp[mixedPrefixSimTheory.spill_lookup_def] >>
     metis_tac[planAlignTheory.spill_hilbert_unique]) >>
  simp[stackModelTheory.stack_push_def, listTheory.LIST_REL_SNOC] >> metis_tac[]
QED

Theorem do_swap_read_only_shallow:
  do_swap d ps = (ops, ps') /\ ps.ps_stack <> [] /\
  (!off. ~MEM (SOSpill off) ops) ==> d <= 16
Proof
  Cases_on `d <= 16` >- simp[] >>
  simp[stackPlanOpsTheory.do_swap_def] >> strip_tac >>
  pairarg_tac >> gvs[listTheory.MEM_APPEND] >>
  spose_not_then strip_assume_tac >>
  qspecl_then [`top_n (d + 1) ps.ps_stack`, `[]`, `[]`, `ps.ps_alloc`]
    mp_tac doSwapSimTheory.spill_foldl_ops_eq_map >> simp[] >> strip_tac >>
  `FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) = []` by
    (Cases_on `FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))` >>
     gvs[] >> metis_tac[listTheory.MEM]) >>
  pop_assum (mp_tac o AP_TERM ``LENGTH:num list -> num``) >>
  simp[doSwapSimTheory.spill_alloc_n_offsets_length, stackPlanOpsTheory.top_n_def] >>
  Cases_on `ps.ps_stack` >> gvs[]
QED

Theorem do_swap_no_restore_shallow:
  do_swap d ps = (ops, ps') /\
  (!off. ~MEM (SORestore off) ops) ==> d <= 16
Proof
  Cases_on `d <= 16` >- simp[] >>
  simp[stackPlanOpsTheory.do_swap_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM, listTheory.MEM_REVERSE, listTheory.MEM_APPEND]
QED

Theorem list_rel_stack_swap:
  LIST_REL R xs ys ==> LIST_REL R (stack_swap d xs) (stack_swap d ys)
Proof
  strip_tac >> Cases_on `xs = []`
  >- gvs[stackModelTheory.stack_swap_def, listTheory.LUPDATE_def] >>
  fs[listTheory.LIST_REL_EL_EQN] >>
  rw[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_swap_def, listTheory.EL_LUPDATE] >>
  rpt IF_CASES_TAC >> simp[] >> first_x_assum irule >> decide_tac
QED

Theorem do_swap_spill_free_kind_replay:
  do_swap d ps = (ops, ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  strip_tac >> drule do_swap_no_restore_shallow >> simp[] >> strip_tac >>
  Cases_on `d = 0`
  >- gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def] >>
  gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def] >>
  irule list_rel_stack_swap >> simp[]
QED

Theorem do_swap_read_only_kind_replay:
  do_swap d ps = (ops, ps') /\ ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled /\
  ps'.ps_stack <> []
Proof
  strip_tac >> drule_all do_swap_read_only_shallow >> strip_tac >>
  Cases_on `d = 0`
  >- gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
         mixedPrefixSimTheory.prefix_spill_wf_def] >>
  gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def] >>
  conj_tac >- (irule list_rel_stack_swap >> simp[]) >>
  simp[stackModelTheory.stack_swap_def, listTheory.LUPDATE_NIL]
QED

Theorem do_swap_pair_read_only_kind_replay:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) (ops1 ++ ops2)) ==>
  prefix_spill_wf fmp lo (ops1 ++ ops2) qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_stack ps2.ps_stack /\
  (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_spilled = ps2.ps_spilled
Proof
  simp[listTheory.MEM_APPEND, FORALL_AND_THM] >> strip_tac >>
  drule_all do_swap_read_only_kind_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  drule_all do_swap_read_only_kind_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >> simp[]
QED

Theorem list_rel_op_kind_equiv_trans:
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs ys /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) ys zs ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs zs
Proof
  rw[listTheory.LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem reorder_restore_no_restore_identity:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SORestore off) ops) ==> ops = [] /\ ps1 = ps
Proof
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[stackPlanOpsTheory.do_restore_def] >> metis_tac[listTheory.MEM]
QED

Theorem do_swap_pair_spill_free_kind_replay:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) (ops1 ++ ops2)) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_stack ps2.ps_stack
Proof
  simp[listTheory.MEM_APPEND, planAlignTheory.apply_prefix_ops_append] >>
  metis_tac[do_swap_spill_free_kind_replay]
QED

Theorem stack_exchange_kind_replay:
  stack_get_unfixed_depth op f n ps.ps_stack = SOME d /\
  f < LENGTH ps.ps_stack /\ dfg = dfg_build_function fn /\
  ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack (stack_poke f op (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
Proof
  strip_tac >> drule stackModelTheory.stack_get_unfixed_depth_props >> strip_tac >>
  metis_tac[stack_exchange_op_kind_equiv, list_rel_op_kind_equiv_trans]
QED

Theorem reorder_swap_pair_case_kind_replay:
  (case do_swap d ps of (ops1,ps1) =>
     case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)) = (ops,ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  strip_tac >> gvs[AllCaseEqs()] >>
  irule do_swap_pair_spill_free_kind_replay >>
  simp[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem reorder_swap_pair_case_read_only_kind_replay:
  (case do_swap d ps of (ops1,ps1) =>
     case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)) = (ops,ps') /\
  ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> gvs[AllCaseEqs()] >>
  irule do_swap_pair_read_only_kind_replay >>
  simp[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem control_reorder_place_read_only_kind_replay_expr:
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     NONE => ([],ps)
   | SOME d => if d = f then ([],ps)
     else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
     then ([],ps with ps_stack := stack_poke f op
       (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
     else (case do_swap d ps of (ops1,ps1) =>
       case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2))) = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                           mixedPrefixSimTheory.prefix_spill_wf_def]) >>
  rename1 `_ = SOME d` >> Cases_on `d = f` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                           mixedPrefixSimTheory.prefix_spill_wf_def]) >>
  Cases_on `f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                       mixedPrefixSimTheory.prefix_spill_wf_def] >>
      metis_tac[stack_exchange_kind_replay]) >>
  strip_tac >> irule reorder_swap_pair_case_read_only_kind_replay >> simp[] >>
  qexistsl [`d`, `f`, `ps`] >> simp[] >>
  drule stackModelTheory.stack_get_unfixed_depth_props >> strip_tac >>
  Cases_on `ps.ps_stack` >> gvs[]
QED

Theorem control_reorder_place_spill_free_kind_replay_expr:
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     NONE => ([],ps)
   | SOME d => if d = f then ([],ps)
     else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
     then ([],ps with ps_stack := stack_poke f op
       (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
     else (case do_swap d ps of (ops1,ps1) =>
       case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2))) = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def]) >>
  rename1 `_ = SOME d` >> Cases_on `d = f` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def]) >>
  Cases_on `f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def] >>
      metis_tac[stack_exchange_kind_replay]) >>
  metis_tac[reorder_swap_pair_case_kind_replay]
QED

Theorem reorder_reduce_no_spill_identity:
  (if (dist:num) > 16 then reduce_depth_plan (LENGTH ps.ps_stack) pending op f n ps
   else ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SOSpill off) ops) ==> ops = [] /\ ps1 = ps
Proof
  Cases_on `dist > 16` >> simp[] >>
  metis_tac[reorderPreparationPropsTheory.reduce_depth_plan_spill_free]
QED

Theorem reorder_restore_read_only_kind_replay:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[]
  >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
      >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                              mixedPrefixSimTheory.prefix_spill_wf_def]) >>
      metis_tac[do_restore_read_only_kind_replay]) >>
  rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                       mixedPrefixSimTheory.prefix_spill_wf_def]
QED

Theorem reorder_one_read_only_decompose_expr:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) ==>
  ?restore_ops ps1 suffix.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ops = restore_ops ++ suffix /\
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps1.ps_stack of
       NONE => ([],ps1)
     | SOME d => if d = LENGTH pending - (idx + 1) then ([],ps1)
       else if LENGTH pending - (idx + 1) < LENGTH ps1.ps_stack /\
         operand_equiv dfg op (stack_peek (LENGTH pending - (idx + 1)) ps1.ps_stack)
       then ([],ps1 with ps_stack := stack_poke (LENGTH pending - (idx + 1)) op
         (stack_poke d (stack_peek (LENGTH pending - (idx + 1)) ps1.ps_stack) ps1.ps_stack))
       else (case do_swap d ps1 of (ops1,ps2) =>
         case do_swap (LENGTH pending - (idx + 1)) ps2 of (ops2,ps3) =>
           (ops1 ++ ops2,ps3))) = (suffix,ps')
Proof
  rewrite_tac[stackPlanOpsTheory.reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `LENGTH pending = num_ops` >>
  Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops ps1.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if _ > 16 then _ else _) = (reduce_ops,ps2)` >>
  gs[pairTheory.UNCURRY_pair_CASE, AllCaseEqs()] >>
  `reduce_ops = [] /\ ps2 = ps1` by
    (irule (Q.INST [`dist` |-> `x`] (SPEC_ALL reorder_reduce_no_spill_identity)) >>
     conj_tac
     >- (gvs[listTheory.MEM_APPEND] >> metis_tac[]) >>
     qexistsl [`num_ops - (idx + 1)`, `num_ops`, `op`, `pending`] >>
     qexists `x` >> simp[]) >>
  gvs[] >> metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem reorder_one_read_only_kind_replay:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> drule_all reorder_one_read_only_decompose_expr >> strip_tac >>
  gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all reorder_restore_read_only_kind_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  irule (SRULE [] (Q.INST
    [`f` |-> `LENGTH pending - (idx + 1)`, `dfg` |-> `dfg_build_function fn`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:operand``]
      control_reorder_place_read_only_kind_replay_expr)))) >>
  simp[] >> qexistsl [`idx`, `op`, `pending`, `ps1`] >>
  simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem reorder_steps_read_only_kind_replay:
  !items ps qs ops ps' dfg pending fn ret fmp lo.
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Induct
  >- simp[foldlSimTheory.plan_steps_def, mixedPrefixSimTheory.apply_prefix_ops_def,
          mixedPrefixSimTheory.prefix_spill_wf_def] >>
  Cases_on `h` >> rpt gen_tac >> simp[foldlSimTheory.plan_steps_def] >>
  Cases_on `reorder_one dfg pending q r ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
  Cases_on `plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items mid` >>
  simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all (SRULE [] (Q.INST [`dfg` |-> `dfg_build_function fn`]
    reorder_one_read_only_kind_replay)) >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  `!op1 off1 op2 off2.
    FLOOKUP mid.ps_spilled op1 = SOME off1 /\
    FLOOKUP mid.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (drule_at Any doSwapSimTheory.safe_prefix_spilled_separated >>
     simp[] >> disch_then assume_tac >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum drule >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem reorder_plan_read_only_kind_replay:
  reorder_plan dfg pending ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >>
  qspecl_then [`dfg`, `pending`, `ps`, `ops`, `ps'`,
    `\st trace out. !q.
      LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
        q.ps_stack st.ps_stack /\ q.ps_spilled = st.ps_spilled /\
      (!x a y b.
        FLOOKUP st.ps_spilled x = SOME a /\
        FLOOKUP st.ps_spilled y = SOME b /\ x <> y ==>
        a + 32 <= b \/ b + 32 <= a) /\
      (!off. ~MEM (SOSpill off) trace) /\
      (!off. MEM (SORestore off) trace ==> off < dimword(:256)) ==>
      prefix_spill_wf fmp lo trace q /\
      LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
        (apply_prefix_ops fmp lo trace q).ps_stack out.ps_stack /\
      (apply_prefix_ops fmp lo trace q).ps_spilled = out.ps_spilled`]
    (mp_tac o BETA_RULE) reorder_plan_trace_relation >>
  impl_tac
  >- (rpt conj_tac
      >- simp[mixedPrefixSimTheory.apply_prefix_ops_def,
              mixedPrefixSimTheory.prefix_spill_wf_def]
      >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
          gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
          qpat_x_assum `!q'. _ ==> prefix_spill_wf fmp lo first_ops q' /\ _`
            (qspec_then `q` mp_tac) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
          qabbrev_tac `qm = apply_prefix_ops fmp lo first_ops q` >>
          `!x a y b.
             FLOOKUP qm.ps_spilled x = SOME a /\
             FLOOKUP qm.ps_spilled y = SOME b /\ x <> y ==>
             a + 32 <= b \/ b + 32 <= a` by
            (qspecl_then [`first_ops`, `q`, `fmp`, `lo`] mp_tac
               doSwapSimTheory.safe_prefix_spilled_separated >>
             impl_tac >- (conj_tac >> fs[] >> first_assum ACCEPT_TAC) >>
             simp[Abbr `qm`]) >>
          qpat_x_assum `!q'. _ ==> prefix_spill_wf fmp lo rest_ops q' /\ _`
            (qspec_then `qm` mp_tac) >>
          impl_tac
          >- (conj_tac >- first_assum ACCEPT_TAC >>
              conj_tac >- first_assum ACCEPT_TAC >>
              qpat_assum `qm.ps_spilled = mid.ps_spilled` (fn eq =>
                qpat_assum `!x a y b. FLOOKUP qm.ps_spilled x = _ /\ _ ==> _`
                  (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
          simp[doSwapSimTheory.prefix_spill_wf_append,
               planAlignTheory.apply_prefix_ops_append, Abbr `qm`])
      >- metis_tac[do_restore_read_only_kind_replay]
      >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
          drule_all reduce_depth_plan_spill_free >>
          simp[mixedPrefixSimTheory.apply_prefix_ops_def,
               mixedPrefixSimTheory.prefix_spill_wf_def])
      >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> gvs[] >>
          drule_all (SRULE [] (Q.INST [`dfg` |-> `dfg_build_function fn`]
            reorder_one_read_only_kind_replay)) >>
          disch_then (qspecl_then [`lo`, `fmp`] ACCEPT_TAC))
      >- first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `qs` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem sym_kinds_ok_kind_transport:
  !cp fn ret srest ps ss qs.
  sym_kinds_ok cp fn ret srest ps ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    ps.ps_stack qs.ps_stack /\ ps.ps_spilled = qs.ps_spilled ==>
  sym_kinds_ok cp fn ret srest qs ss
Proof
  rpt gen_tac >> simp[sym_kinds_ok_def] >> strip_tac >>
  qexists `top` >> simp[] >> irule list_rel_op_kind_transport >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem sym_frame_inv_kind_transport:
  !p env ctx cp fn ret srest labs0 ps cs ss qs.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    ps.ps_stack qs.ps_stack /\ ps.ps_spilled = qs.ps_spilled ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 qs cs ss
Proof
  rpt gen_tac >> simp[sym_frame_inv_def] >> strip_tac >>
  irule sym_kinds_ok_kind_transport >> goal_assum (drule_at Any) >> simp[]
QED

Theorem selected_prefix_read_only_kind_replay:
  !opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp lo.
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo (iops ++ rops) ps /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (iops ++ rops) ps).ps_stack ps2.ps_stack /\
  (apply_prefix_ops fmp lo (iops ++ rops) ps).ps_spilled = ps2.ps_spilled
Proof
  rpt gen_tac >>
  simp[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  `prefix_spill_wf fmp lo iops ps /\
   (apply_prefix_ops fmp lo iops ps).ps_stack = ps1.ps_stack /\
   (apply_prefix_ops fmp lo iops ps).ps_spilled = ps1.ps_spilled` by
    (irule emit_input_plan_read_only_replay >> simp[] >> metis_tac[]) >>
  `!op1 off1 op2 off2.
    FLOOKUP ps1.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps1.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (drule_at Any doSwapSimTheory.safe_prefix_spilled_separated >>
     simp[] >> disch_then assume_tac >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  irule reorder_plan_read_only_kind_replay >> simp[] >>
  qexistsl [`inputs`, `ps1`] >> simp[listTheory.LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem sym_read_only_selected_prefix_frame_sim_mode_conditional:
  !allow_own lo code_ok own opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp p env ctx cp srest labs0 cs ss.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops) /\
  EVERY is_prefix_op (iops ++ rops) /\
  EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops) /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cp fn ret srest ps2 ss' /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all selected_prefix_read_only_kind_replay >>
  disch_then (qspecl_then [`ret`, `fmp`, `lo`] strip_assume_tac) >>
  drule_all sym_spill_free_prefix_frame_sim_mode_conditional >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  conj_tac
  >- (conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  irule sym_kinds_ok_kind_transport >> goal_assum (drule_at Any) >> simp[]
QED
