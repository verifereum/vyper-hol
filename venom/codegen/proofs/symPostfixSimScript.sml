(* Symbolic output metadata and postfix execution boundaries. *)
Theory symPostfixSim
Ancestors
  symInstKinds symShuffleSim regularPostfixSim fnPlanPrefix
  doSwapSim planWf codegenEncodingWf rich_list
  stackPlanOps stackPlanGen stackModel planExec prefixExec prefixSim
  codegenSymRel asmSymSem finite_map list

Theorem sym_kinds_ok_inventory_mono:
  sym_kinds_ok cplan fn ret srest ps ss /\
  qs.ps_stack = ps.ps_stack /\
  (!op off. FLOOKUP qs.ps_spilled op = SOME off ==>
            FLOOKUP ps.ps_spilled op = SOME off) ==>
  sym_kinds_ok cplan fn ret srest qs ss
Proof
  simp[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem release_spill_fold_cons_lookup[local]:
  (!ps op off.
    FLOOKUP (FOLDL (\p (at, slot).
      p with <| ps_spilled := p.ps_spilled \\ at;
                ps_alloc := free_spill_slot slot p.ps_alloc |>) ps xs).ps_spilled
      op = SOME off ==> FLOOKUP ps.ps_spilled op = SOME off) ==>
  FLOOKUP (FOLDL (\p (at, slot).
    p with <| ps_spilled := p.ps_spilled \\ at;
              ps_alloc := free_spill_slot slot p.ps_alloc |>)
    (ps with <| ps_spilled := ps.ps_spilled \\ at;
                ps_alloc := free_spill_slot slot ps.ps_alloc |>) xs).ps_spilled
    op = SOME off ==> FLOOKUP ps.ps_spilled op = SOME off
Proof
  rpt strip_tac >> first_x_assum drule >>
  simp[DOMSUB_FLOOKUP_THM, AllCaseEqs()] >> metis_tac[]
QED

Theorem release_spill_fold_lookup[local]:
  !xs ps op off.
  FLOOKUP (FOLDL (\p (at, slot).
    p with <| ps_spilled := p.ps_spilled \\ at;
              ps_alloc := free_spill_slot slot p.ps_alloc |>) ps xs).ps_spilled
    op = SOME off ==>
  FLOOKUP ps.ps_spilled op = SOME off
Proof
  Induct_on `xs` >- simp[] >>
  Cases >> simp[] >> metis_tac[release_spill_fold_cons_lookup]
QED

Theorem release_dead_spills_lookup:
  FLOOKUP (release_dead_spills nl ps).ps_spilled op = SOME off ==>
  FLOOKUP ps.ps_spilled op = SOME off
Proof
  simp[release_dead_spills_def] >>
  metis_tac[release_spill_fold_lookup]
QED

Theorem sym_kinds_ok_release_dead_spills:
  sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest (release_dead_spills nl ps) ss
Proof
  strip_tac >> irule sym_kinds_ok_inventory_mono >>
  qexists `ps` >> simp[release_dead_spills_stack] >>
  MATCH_ACCEPT_TAC release_dead_spills_lookup
QED

Theorem sym_kinds_ok_stack_replace:
  sym_kinds_ok cplan fn ret srest ps ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE stk) top ==>
  sym_kinds_ok cplan fn ret srest (ps with ps_stack := stk) ss
Proof
  simp[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_generated_postfix_sim:
  prefix_wf lo (LENGTH ps.ps_stack) tail /\
  prefix_spill_wf initial_fmp lo tail ps /\
  EVERY is_prefix_op tail /\
  EVERY (\op. !l d. op <> SOPushOfst l d) tail /\
  (!off b. MEM (SOSpill off) tail /\ in_mem_range off 32 b ==>
     R b /\ context_spill_byte cplan b) /\
  apply_prefix_ops initial_fmp lo tail ps = qs /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp tail) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp tail)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest (release_dead_spills nl qs) ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp tail) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all sym_prefix_ops_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >> gvs[] >>
  irule sym_kinds_ok_release_dead_spills >> simp[]
QED

Theorem sym_pop_top_sim:
  0 < LENGTH ps.ps_stack /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOPop 1]) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp [SOPop 1])) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest (ps with ps_stack := stack_pop 1 ps.ps_stack) ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOPop 1]) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `prefix_wf lo (LENGTH ps.ps_stack) [SOPop 1] /\
   prefix_spill_wf initial_fmp lo [SOPop 1] ps /\
   EVERY is_prefix_op [SOPop 1]` by
    simp[prefix_wf_def, stack_op_wf_def, mixedPrefixSimTheory.prefix_spill_wf_def,
         mixedPrefixSimTheory.spill_op_wf_def, is_prefix_op_def] >>
  `EVERY (\op. !l d. op <> SOPushOfst l d) [SOPop 1] /\
   (!off b. MEM (SOSpill off) [SOPop 1] /\ in_mem_range off 32 b ==>
      F /\ context_spill_byte cplan b)` by simp[] >>
  drule_all (BETA_RULE (Q.INST [`R` |-> `\b:num. F`] (SPEC_ALL sym_prefix_ops_sim))) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >>
  gvs[planAlignTheory.sopop_align, stack_pop_def, FLOOKUP_EXT, FUN_EQ_THM]
QED

Theorem sym_popmany_plan_top_singleton_sim:
  stack_get_depth v ps.ps_stack = SOME 0 /\
  popmany_plan [v] ps = (ops, qs) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `0 < LENGTH ps.ps_stack` by metis_tac[planAlignTheory.stack_get_depth_bound] >>
  gvs[popmany_plan_top_singleton] >> metis_tac[sym_pop_top_sim, arithmeticTheory.ADD_COMM]
QED

Theorem LIST_REL_relabel_left[local]:
  LIST_REL R xs ys /\
  (!sv. R (EL i xs) sv ==> R op sv) ==>
  LIST_REL R (LUPDATE op i xs) ys
Proof
  simp[LIST_REL_EL_EQN, EL_LUPDATE] >> rpt strip_tac >>
  IF_CASES_TAC >> metis_tac[]
QED

Theorem sym_kinds_ok_poke:
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
        op_kind_ok fn ret op sv) ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  qexists `top` >> simp[] >>
  once_rewrite_tac[GSYM rich_listTheory.LIST_REL_REVERSE_EQ] >>
  pure_rewrite_tac[REVERSE_REVERSE, stack_poke_def] >>
  irule LIST_REL_relabel_left >>
  simp[stack_peek_def, rich_listTheory.LIST_REL_REVERSE1]
QED


(* prefix_wf is polymorphic in the label map's range; replay uses num. *)
Theorem swap_prefix_wf_num[local]:
  do_swap dist ps = (ops, qs) /\ dist < LENGTH ps.ps_stack ==>
  prefixExec$prefix_wf (lo:(string,num) fmap) (LENGTH ps.ps_stack) ops
Proof
  strip_tac >>
  drule (INST_TYPE [alpha |-> ``:num``] planWfTheory.do_swap_wf_len) >>
  simp[] >> metis_tac[]
QED

Theorem sym_do_swap_sim:
  dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT (top_n (dist + 1) ps.ps_stack) /\
  DISJOINT (set (top_n (dist + 1) ps.ps_stack)) (FDOM ps.ps_spilled) /\
  do_swap dist ps = (ops, qs) /\
  prefix_spill_wf initial_fmp lo (FRONT ops) spill_view /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
      R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `prefix_wf (lo:(string,num) fmap) (LENGTH ps.ps_stack) ops` by
    metis_tac[swap_prefix_wf_num] >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (drule_all do_swap_prefix_spill_wf_from_front_cross_view >> simp[]) >>
  `EVERY is_prefix_op ops /\ EVERY (\op. !l d. op <> SOPushOfst l d) ops` by
    (drule do_swap_prefix_op >> drule do_swap_no_push_ofst >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `qs.ps_stack = (apply_prefix_ops initial_fmp lo ops ps).ps_stack /\
   qs.ps_spilled = (apply_prefix_ops initial_fmp lo ops ps).ps_spilled` by
    (drule do_swap_apply_relevant_align_layout >> simp[] >> metis_tac[]) >>
  drule_all sym_prefix_ops_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >> simp[] >>
  irule sym_kinds_ok_inventory_mono >>
  qexists `apply_prefix_ops initial_fmp lo ops ps` >> simp[]
QED

Theorem optimistic_swap_result_cases[local]:
  optimistic_swap_plan dfg inst nl next_term ps = (ops, qs) ==>
  (ops = [] /\ qs = ps) \/
  ?d. d < LENGTH ps.ps_stack /\ do_swap d ps = (ops, qs)
Proof
  simp[optimistic_swap_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[stack_get_depth_props]
QED

Theorem sym_optimistic_swap_plan_postfix_sim_structural:
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  optimistic_swap_plan dfg inst nl next_term ps = (ops, qs) /\
  prefix_spill_wf initial_fmp lo (FRONT ops) spill_view /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
      R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule optimistic_swap_result_cases >> strip_tac
  >- (gvs[] >> qexists `ss` >> simp[execute_plan_def, sym_steps_def]) >>
  `ALL_DISTINCT (top_n (d + 1) ps.ps_stack) /\
   DISJOINT (set (top_n (d + 1) ps.ps_stack)) (FDOM ps.ps_spilled)` by
    (simp[top_n_def, ALL_DISTINCT_TAKE, ALL_DISTINCT_REVERSE] >>
     gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  drule_all sym_do_swap_sim >> simp[]
QED

Theorem regular_postfix_cases[local]:
  LENGTH inst.inst_outputs <= 1 /\
  (if inst.inst_outputs = [] \/ is_halting then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl)
     inst.inst_outputs)) ps7) = (pop_ops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl next_term ps8) = (opt_ops,ps9) ==>
  (pop_ops = [] /\ opt_ops = [] /\ ps8 = ps7 /\ ps9 = ps7) \/
  (pop_ops = [] /\ ps8 = ps7 /\
   optimistic_swap_plan dfg inst nl next_term ps7 = (opt_ops,ps9)) \/
  (?out. inst.inst_outputs = [out] /\ opt_ops = [] /\ ps9 = ps8 /\
    popmany_plan [Var out] ps7 = (pop_ops,ps8))
Proof
  strip_tac >> Cases_on `inst.inst_outputs` >> gvs[] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> gvs[] >>
  Cases_on `MEM out nl` >> gvs[popmany_plan_def] >>
  Cases_on `is_halting` >> gvs[]
QED

Theorem sym_regular_generated_postfix_sim_structural:
  LENGTH inst.inst_outputs <= 1 /\
  (!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) ps7.ps_stack = SOME 0) /\
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  ALL_DISTINCT ps7.ps_stack /\
  DISJOINT (set ps7.ps_stack) (FDOM ps7.ps_spilled) /\
  (if inst.inst_outputs = [] \/ is_halting then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl)
     inst.inst_outputs)) ps7) = (pop_ops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl next_term ps8) = (opt_ops,ps9) /\
  qs = release_dead_spills nl ps9 /\
  prefix_spill_wf initial_fmp lo (FRONT opt_ops) spill_view /\
  (!off b. MEM (SOSpill off) opt_ops /\ in_mem_range off 32 b ==>
      R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps7 ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (pop_ops ++ opt_ops)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops)) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all regular_postfix_cases >> strip_tac
  >- (gvs[] >> qexists `ss` >>
      simp[execute_plan_def, sym_steps_def, sym_kinds_ok_release_dead_spills])
  >- (gvs[] >> drule_all sym_optimistic_swap_plan_postfix_sim_structural >>
      metis_tac[sym_kinds_ok_release_dead_spills, arithmeticTheory.ADD_COMM]) >>
  gvs[] >> drule_all sym_popmany_plan_top_singleton_sim >>
  metis_tac[sym_kinds_ok_release_dead_spills, arithmeticTheory.ADD_COMM]
QED
