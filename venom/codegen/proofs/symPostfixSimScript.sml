(* Symbolic output metadata and postfix execution boundaries. *)
Theory symPostfixSim
Ancestors
  symInstKinds symShuffleSim regularPostfixSim fnPlanPrefix
  doSwapSim deepDupCallerSim planWf codegenEncodingWf rich_list
  stackPlanOps stackPlanGen stackModel planExec prefixExec prefixSim
  codegenSymRel asmSymSem asmSem finite_map list

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

Theorem assign_output_kind:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  label_positions_ok inst ==>
  (op_kind_ok fn ret (Var x) sv <=> op_kind_ok fn ret op sv)
Proof
  strip_tac >> Cases_on `op`
  >- metis_tac[assign_lit_output_kind]
  >- metis_tac[assign_var_output_kind] >>
  gvs[unitShapeDefsTheory.label_positions_ok_def,
      stackPlanTypesTheory.is_label_operand_def]
QED

Theorem sym_assign_rename_top:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  label_positions_ok inst /\ stack_peek 0 ps.ps_stack = op /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke 0 (Var x) ps.ps_stack) ss
Proof
  strip_tac >> irule sym_kinds_ok_poke >>
  simp[] >> metis_tac[assign_output_kind]
QED

Theorem phi_depth_operand:
  stack_get_phi_depth (FILTER is_var_operand ops) stk = SOME d ==>
  ?y. stack_peek d stk = Var y /\ MEM (Var y) ops
Proof
  strip_tac >>
  `d < LENGTH stk` by
    metis_tac[stack_get_phi_depth_def, planWfTheory.stack_find_bound, LENGTH_REVERSE] >>
  `MEM (stack_peek d stk) (FILTER is_var_operand ops)` by
    (gvs[stack_get_phi_depth_def, stack_peek_def] >>
     drule genBlockSimTheory.stack_find_el >>
     simp[EL_REVERSE, arithmeticTheory.PRE_SUB1]) >>
  Cases_on `stack_peek d stk` >>
  gvs[MEM_FILTER, stackPlanTypesTheory.is_var_operand_def]
QED

Theorem sym_phi_rename:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = SOME d /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d (Var x) ps.ps_stack) ss
Proof
  strip_tac >> drule phi_depth_operand >> strip_tac >>
  irule sym_kinds_ok_poke >> simp[] >> metis_tac[phi_var_output_kind]
QED

Theorem mem_sval_at_range_cong:
  (!b. in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  (mem_sval_at labs' off sv <=> mem_sval_at labs off sv)
Proof
  strip_tac >> Cases_on `sv` >>
  simp[mem_sval_at_def, mem_label_at_def] >>
  `FLOOKUP labs' off = FLOOKUP labs off` by
    (first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[] >>
  `!i. MEM i (COUNT_LIST 32) ==>
       FLOOKUP labs' (off + i) = FLOOKUP labs (off + i)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[in_mem_range_def, MEM_COUNT_LIST]) >>
  simp[EVERY_MEM, GSYM (cj 1 flookup_thm)] >> gvs[]
QED

Theorem temporary_spill_ranges_avoid_inventory:
  spill_alloc_layout_wf al sp /\
  MEM tmp (FST (spill_alloc_n [] al items)) /\
  FLOOKUP sp op = SOME old /\ in_mem_range old 32 b ==>
  ~in_mem_range tmp 32 b
Proof
  strip_tac >>
  drule spill_alloc_n_temporary_layout >> simp[] >>
  disch_then (qspec_then `items` strip_assume_tac) >>
  `old + 32 <= tmp \/ tmp + 32 <= old` by
    (gvs[MEM_EL] >> metis_tac[]) >>
  gvs[in_mem_range_def] >> decide_tac
QED

Theorem sym_kinds_ok_retained_spills:
  sym_kinds_ok cplan fn ret srest ps ss /\
  ss'.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE qs.ps_stack) top /\
  (!op off. FLOOKUP qs.ps_spilled op = SOME off ==>
     FLOOKUP ps.ps_spilled op = SOME off) /\
  (!op off b. FLOOKUP qs.ps_spilled op = SOME off /\
      in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cplan b) ==>
  sym_kinds_ok cplan fn ret srest qs ss'
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  metis_tac[mem_sval_at_range_cong]
QED

Theorem do_dup_spill_inventory_untouched:
  do_dup d ps = (ops,qs) /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM (SOSpill tmp) ops /\ FLOOKUP ps.ps_spilled op = SOME old /\
  in_mem_range old 32 b ==>
  ~in_mem_range tmp 32 b
Proof
  strip_tac >> Cases_on `d <= 15`
  >- gvs[do_dup_def] >>
  mp_tac (Q.SPECL [`d`, `ps`] do_dup_big_decompose) >>
  simp[] >> strip_tac >>
  `MEM tmp (FST (spill_alloc_n [] ps.ps_alloc
      (REVERSE (top_n (d - 15) ps.ps_stack))))` by
    (gvs[MEM_MAP, MEM_FLAT] >> Cases_on `d - 15 <= 16` >>
     gvs[MEM_MAP, MEM_FLAT]) >>
  metis_tac[temporary_spill_ranges_avoid_inventory]
QED

Theorem do_swap_spill_inventory_untouched:
  do_swap d ps = (ops,qs) /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM (SOSpill tmp) ops /\ FLOOKUP ps.ps_spilled op = SOME old /\
  in_mem_range old 32 b ==>
  ~in_mem_range tmp 32 b
Proof
  strip_tac >> Cases_on `d <= 16`
  >- (Cases_on `d = 0` >> gvs[do_swap_def]) >>
  mp_tac (Q.SPECL [`d`, `ps`] do_swap_big_decompose) >>
  simp[] >> strip_tac >>
  `MEM tmp (FST (spill_alloc_n [] ps.ps_alloc
      (top_n (d + 1) ps.ps_stack)))` by gvs[MEM_MAP] >>
  metis_tac[temporary_spill_ranges_avoid_inventory]
QED

(* Contract audit: marked well-formedness permits the duplicate-key scratch
   trace already excluded by do_dup17_duplicate_top_not_wf.  This concerns
   operand-keyed replay, not the physical symbolic machine. *)
Theorem marked_scratch_dup_audit[local]:
  !ps f lo.
    ps = (init_plan_state 0 with
      ps_stack := REPLICATE 18 dead_stack_marker) ==>
    generated_plan_state_wf_marked 0 ps /\
    ~prefix_spill_wf f lo (FST (do_dup 17 ps)) ps
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (gvs[generated_plan_state_wf_marked_def,
          planSpillBoundsTheory.plan_slots_bounded_def,
          planSpillBoundsTheory.alloc_slots_bounded_def,
          spill_alloc_layout_wf_def, stackPlanTypesTheory.init_plan_state_def,
          stackPlanTypesTheory.init_spill_alloc_def] >> EVAL_TAC) >>
  `ps.ps_stack = REPLICATE 16 dead_stack_marker ++
       [dead_stack_marker; dead_stack_marker]` by
    (simp[] >> EVAL_TAC) >>
  `17 < LENGTH ps.ps_stack` by simp[] >>
  metis_tac[do_dup17_duplicate_top_not_wf, pairTheory.PAIR, APPEND_NIL]
QED

(* Physical scratch inventory: keys identify cells, not operand names. *)
Definition scratch_mem_ok_def:
  scratch_mem_ok fn ret slots labs <=>
    !off op. FLOOKUP slots off = SOME op ==>
      ?sv. op_kind_ok fn ret op sv /\ mem_sval_at labs off sv
End

Definition scratch_store_labels_def:
  scratch_store_labels labs off (Val w) =
    mem_labels_clear labs (in_mem_range off 32) /\
  scratch_store_labels labs off (Lab l d) =
    labs |++ GENLIST (\i. (off + i, (l,d,i))) 32
End

Theorem scratch_store_labels_outside:
  ~in_mem_range off 32 b ==>
  FLOOKUP (scratch_store_labels labs off sv) b = FLOOKUP labs b
Proof
  Cases_on `sv` >> pure_rewrite_tac[scratch_store_labels_def,
    asmSymBridgeTheory.mstore_labels_lookup] >>
  simp[mem_labels_clear_def, FLOOKUP_DRESTRICT, in_mem_range_def]
QED

Theorem scratch_store_labels_at:
  mem_sval_at (scratch_store_labels labs off sv) off sv
Proof
  Cases_on `sv` >> pure_rewrite_tac[scratch_store_labels_def,
    mem_sval_at_def, mem_label_at_def,
    asmSymBridgeTheory.mstore_labels_lookup] >>
  simp[mem_labels_clear_def, FDOM_DRESTRICT, in_mem_range_def,
       EVERY_MEM, MEM_COUNT_LIST]
QED

Theorem scratch_store_labels_retains:
  (off + 32 <= old \/ old + 32 <= off) /\ mem_sval_at labs old sv ==>
  mem_sval_at (scratch_store_labels labs off value) old sv
Proof
  strip_tac >> irule (iffRL mem_sval_at_range_cong) >>
  qexists `labs` >> simp[] >> rpt strip_tac >>
  irule scratch_store_labels_outside >> gvs[in_mem_range_def] >> decide_tac
QED

Theorem scratch_mem_ok_store:
  scratch_mem_ok fn ret slots labs /\ op_kind_ok fn ret op sv /\
  (!old at. FLOOKUP slots old = SOME at /\ old <> off ==>
     off + 32 <= old \/ old + 32 <= off) ==>
  scratch_mem_ok fn ret (slots |+ (off,op))
    (scratch_store_labels labs off sv)
Proof
  simp[scratch_mem_ok_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `off = off'` >> gvs[]
  >- metis_tac[scratch_store_labels_at] >>
  metis_tac[scratch_store_labels_retains]
QED

Theorem scratch_mem_ok_restore:
  scratch_mem_ok fn ret slots ss.sym_mem_labels /\
  FLOOKUP slots off = SOME op ==>
  ?sv. op_kind_ok fn ret op sv /\ mem_sval_at ss.sym_mem_labels off sv
Proof
  simp[scratch_mem_ok_def] >> metis_tac[]
QED

Theorem scratch_duplicate_cells_probe:
  a + 32 <= b /\ op_kind_ok fn ret op sva /\ op_kind_ok fn ret op svb ==>
  scratch_mem_ok fn ret (FEMPTY |+ (a,op) |+ (b,op))
    (scratch_store_labels (scratch_store_labels labs a sva) b svb)
Proof
  strip_tac >> irule scratch_mem_ok_store >> simp[FLOOKUP_UPDATE] >>
  irule scratch_mem_ok_store >> simp[scratch_mem_ok_def]
QED

Theorem sym_mstore_scratch_step:
  ss.sym_stack = Val off :: sv :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\
        ss'.sym_stack = tail /\
        ss'.sym_mem_labels = scratch_store_labels ss.sym_mem_labels (w2n off) sv /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  Cases_on `sv` >> strip_tac >>
  simp[sym_mstore_def, scratch_store_labels_def, sym_step_concrete_def,
       sym_lift_def, sval_val_def, asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, log_table_def,
       mem_labels_hit_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_mstore_def, asm_next_def]
QED

Theorem sym_mload_scratch_word:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val word) ==>
  ?ss' w. sym_mload ss = SymOK ss' /\
        ss'.sym_stack = Val w :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >>
  `FLOOKUP ss.sym_mem_labels (w2n off) = NONE` by
    (gvs[mem_sval_at_def, flookup_thm] >>
     first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[sym_mload_def, mem_label_at_def, sym_step_concrete_def,
       sym_lift_def, sval_val_def, asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, log_table_def,
       mem_labels_hit_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_mload_def, asm_next_def] >>
  `~(?i. i IN FDOM ss.sym_mem_labels /\ in_mem_range (w2n off) 32 i)` by
    metis_tac[mem_sval_at_def] >>
  simp[mem_labels_clear_def, DRESTRICT_UNIV, GSYM pred_setTheory.UNIV_DEF]
QED

Theorem op_kind_ok_word_irrelevant:
  op_kind_ok fn ret op (Val w) = op_kind_ok fn ret op (Val v)
Proof
  Cases_on `op` >> simp[op_kind_ok_def]
QED

Theorem sym_mload_scratch_kind:
  ss.sym_stack = Val off :: tail /\
  op_kind_ok fn ret op sv /\ mem_sval_at ss.sym_mem_labels (w2n off) sv ==>
  ?ss' value. sym_mload ss = SymOK ss' /\
        ss'.sym_stack = value :: tail /\ op_kind_ok fn ret op value /\
        ss'.sym_mem_labels = ss.sym_mem_labels /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  Cases_on `sv` >> strip_tac
  >- (drule_all sym_mload_scratch_word >>
      metis_tac[op_kind_ok_word_irrelevant]) >>
  gvs[mem_sval_at_def] >>
  simp[sym_mload_def, asm_next_def] >> metis_tac[]
QED

Theorem scratch_dead_marker_two_labels[local]:
  a + 32 <= b ==>
  scratch_mem_ok fn ret
    (FEMPTY |+ (a,dead_stack_marker) |+ (b,dead_stack_marker))
    (scratch_store_labels
      (scratch_store_labels labs a (Lab l d)) b (Lab other delta))
Proof
  strip_tac >> irule scratch_duplicate_cells_probe >> simp[op_kind_ok_def]
QED

Theorem scratch_store_step_inventory:
  ss.sym_stack = Val off :: sv :: tail /\
  scratch_mem_ok fn ret slots ss.sym_mem_labels /\ op_kind_ok fn ret op sv /\
  (!old at. FLOOKUP slots old = SOME at /\ old <> w2n off ==>
    w2n off + 32 <= old \/ old + 32 <= w2n off) ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    scratch_mem_ok fn ret (slots |+ (w2n off,op)) ss'.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule sym_mstore_scratch_step >>
  metis_tac[scratch_mem_ok_store, scratch_store_labels_outside]
QED

Theorem scratch_restore_step_inventory:
  ss.sym_stack = Val off :: tail /\
  scratch_mem_ok fn ret slots ss.sym_mem_labels /\
  FLOOKUP slots (w2n off) = SOME op ==>
  ?ss' value. sym_mload ss = SymOK ss' /\
    ss'.sym_stack = value :: tail /\ op_kind_ok fn ret op value /\
    scratch_mem_ok fn ret slots ss'.sym_mem_labels /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >> drule_all scratch_mem_ok_restore >>
  metis_tac[sym_mload_scratch_kind]
QED

Theorem scratch_store_retains_inventory:
  scratch_mem_ok fn ret inventory labs /\
  (!old op. FLOOKUP inventory old = SOME op ==>
    off + 32 <= old \/ old + 32 <= off) ==>
  scratch_mem_ok fn ret inventory (scratch_store_labels labs off sv)
Proof
  simp[scratch_mem_ok_def] >> metis_tac[scratch_store_labels_retains]
QED

Theorem scratch_two_label_cells_readable[local]:
  a + 32 <= b ==>
  mem_label_at
    (scratch_store_labels (scratch_store_labels labs a (Lab l d))
      b (Lab other delta)) a = SOME (l,d) /\
  mem_label_at
    (scratch_store_labels (scratch_store_labels labs a (Lab l d))
      b (Lab other delta)) b = SOME (other,delta)
Proof
  strip_tac >> rewrite_tac[GSYM mem_sval_at_def] >> conj_tac
  >- (irule scratch_store_labels_retains >> simp[scratch_store_labels_at]) >>
  simp[scratch_store_labels_at]
QED
