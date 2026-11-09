(* Symbolic output metadata and postfix execution boundaries. *)
Theory symPostfixSim
Ancestors
  symInstKinds symShuffleSim regularPostfixSim fnPlanPrefix
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

Theorem release_spill_fold_lookup[local]:
  !xs ps op off.
  FLOOKUP (FOLDL (\p (at, slot).
    p with <| ps_spilled := p.ps_spilled \\ at;
              ps_alloc := free_spill_slot slot p.ps_alloc |>) ps xs).ps_spilled
    op = SOME off ==>
  FLOOKUP ps.ps_spilled op = SOME off
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[] >> strip_tac >> first_x_assum drule >>
  simp[DOMSUB_FLOOKUP_THM, AllCaseEqs()] >> metis_tac[]
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
