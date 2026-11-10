Theory symPlannerReorder
Ancestors
  list stackModel symPlannerBase symPlannerMoves reorderSim deepResidualBudget
  unitShapeDefs venomWf dfgDefs

Theorem LIST_REL_stack_poke_exchange[local]:
  LIST_REL R (REVERSE stk) top /\ a < LENGTH stk /\ b < LENGTH stk /\
  (!sv. R (stack_peek a stk) sv <=> R (stack_peek b stk) sv) ==>
  LIST_REL R (REVERSE (stack_poke b (stack_peek a stk)
    (stack_poke a (stack_peek b stk) stk))) top
Proof
  rw[LIST_REL_EL_EQN, EL_REVERSE, stack_poke_def, EL_LUPDATE, stack_peek_def] >>
  gvs[stack_peek_def] >> metis_tac[]
QED

Theorem sym_kinds_ok_poke_exchange:
  sym_kinds_ok cplan fn ret srest ps ss /\
  a < LENGTH ps.ps_stack /\ b < LENGTH ps.ps_stack /\
  stack_peek a ps.ps_stack = op /\
  operand_equiv dfg op (stack_peek b ps.ps_stack) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke b op
      (stack_poke a (stack_peek b ps.ps_stack) ps.ps_stack)) ss
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def] >> qexists `top` >>
  simp[LIST_REL_stack_poke_exchange, op_kind_ok_operand_equiv]
QED

Theorem reorder_restore_alternatives[local]:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,out) ==>
  (ops = [] /\ out = ps) \/ do_restore op ps = (ops,out)
Proof
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack`
  >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]) >> simp[]
QED

Theorem spill_restore_bounds_restore_only[local]:
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops ==>
  EVERY (\s. case s of SORestore off => off < dimword(:256) | _ => T) ops
Proof
  match_mp_tac EVERY_MONOTONIC >> Cases >> simp[]
QED

Theorem sym_reorder_restore_run[local]:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,out) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_then strip_assume_tac reorder_restore_alternatives
  >- gvs[planExecTheory.execute_plan_def, codegenSymRelTheory.sym_steps_def] >>
  metis_tac[sym_do_restore, spill_restore_bounds_restore_only]
QED

Theorem reorder_restore_marked_structure[local]:
  residual_budget_wf_marked spillbase pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,out) ==>
  residual_budget_wf_marked spillbase pending out /\
  LENGTH pending <= LENGTH out.ps_stack
Proof
  strip_tac >>
  drule_all_then (qspecl_then [`op`, `f`] mp_tac)
    reorder_restore_residual_budget_wf_marked >> gvs[LET_THM]
QED

Theorem sym_reorder_restore:
  residual_budget_wf_marked spillbase pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,out) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  residual_budget_wf_marked spillbase pending out /\
  LENGTH pending <= LENGTH out.ps_stack /\
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all_then strip_assume_tac reorder_restore_marked_structure >>
  metis_tac[sym_reorder_restore_run]
QED

Theorem reorder_reduce_structure[local]:
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps.ps_stack) pending op f (LENGTH pending) ps
   else ([],ps)) = (ops,out) ==>
  spill_alloc_layout_wf out.ps_alloc out.ps_spilled /\
  LENGTH pending <= LENGTH out.ps_stack
Proof
  Cases_on `dist > 16` >> simp[] >>
  metis_tac[reduce_depth_plan_layout_wf, reduce_depth_plan_target_len_floor, pairTheory.SND]
QED

Theorem sym_reorder_reduce_run[local]:
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps.ps_stack) pending op f (LENGTH pending) ps
   else ([],ps)) = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Cases_on `dist > 16`
  >- (pure_asm_rewrite_tac[COND_CLAUSES] >> MATCH_ACCEPT_TAC sym_reduce_depth_plan) >>
  rw[planExecTheory.execute_plan_def, codegenSymRelTheory.sym_steps_def] >> simp[]
QED

Theorem reorder_restore_spill_base[local]:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,out) ==>
  out.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  strip_tac >> drule_then strip_assume_tac reorder_restore_alternatives >>
  metis_tac[allocMonoTheory.do_restore_spill_base]
QED

Theorem reorder_prepare_structure[local]:
  residual_budget_wf_marked spillbase pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (rops,ps1) /\
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1
   else ([],ps1)) = (dops,ps2) ==>
  spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled /\
  spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled /\
  LENGTH pending <= LENGTH ps2.ps_stack
Proof
  strip_tac >> drule_all_then strip_assume_tac reorder_restore_marked_structure >>
  metis_tac[reorder_reduce_structure, residual_budget_wf_marked_def]
QED

Theorem sym_plan_frame_compose[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp xs)) ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp ys)) mid = SymOK last /\
  sym_kinds_ok cplan fn ret srest out last /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp xs) /\
  last.sym_base.as_pc = mid.sym_base.as_pc + LENGTH (execute_plan initial_fmp ys) /\
  (!b. ~P b ==> FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. ~P b ==> FLOOKUP last.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b) ==>
  sym_steps p env (LENGTH (execute_plan initial_fmp (xs ++ ys))) ss = SymOK last /\
  sym_kinds_ok cplan fn ret srest out last /\
  last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (xs ++ ys)) /\
  (!b. ~P b ==> FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, LENGTH_APPEND] >>
  MATCH_ACCEPT_TAC sym_steps_frame_compose
QED

(* Deterministic witness packaging for two already-established phase runs. *)
val compose_plan_frame_tac =
  qexists_tac `last` >> ho_match_mp_tac sym_plan_frame_compose >>
  asm_rewrite_tac[];

Theorem sym_reorder_prepare_finish[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp rops)) ss = SymOK mid /\
  sym_kinds_ok cplan fn ret srest ps1 mid /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp rops) /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1
   else ([],ps1)) = (dops,ps2) /\
  spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) dops /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps1.ps_alloc.sa_spill_base /\
  ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp dops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp (rops ++ dops))) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest ps2 last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (rops ++ dops)) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule_all_then (qspec_then `env` (qx_choose_then `last` strip_assume_tac))
    sym_reorder_reduce_run >>
  compose_plan_frame_tac
QED
