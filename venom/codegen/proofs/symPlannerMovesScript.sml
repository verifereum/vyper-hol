(* Exact-output symbolic simulations for stack moves. *)
Theory symPlannerMoves
Ancestors
  symPlannerScratch symPlannerBase stackOpSim stackPlanOps list rich_list
  asmSymSem asmSem planExec codegenSymRel doSwapSim reorderSpillFresh planSpillBounds

Theorem sym_step_dup_name:
  d <= 15 ==>
  sym_step p env (AsmOp (dup_name (d+1))) ss = sym_dup d ss
Proof
  strip_tac >>
  `d < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  pure_rewrite_tac[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >> gvs[]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >- simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
  >> simp[sym_step_def, sym_step_op_def, dup_name_def, dup_table_def]
QED

Theorem sym_step_swap_name:
  0 < d /\ d <= 16 ==>
  sym_step p env (AsmOp (swap_name d)) ss = sym_swap d ss
Proof
  strip_tac >>
  `d < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  pure_rewrite_tac[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >> gvs[]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >- simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
  >> simp[sym_step_def, sym_step_op_def, swap_name_def, dup_table_def, swap_table_def]
QED

Theorem sym_steps_singleton:
  asm_block_at p ss.sym_base.as_pc [inst] ==>
  sym_steps p env 1 ss = sym_step p env inst ss
Proof
  simp[asm_block_at_def, codegenSymRelTheory.sym_steps_compute] >>
  Cases_on `sym_step p env inst ss` >>
  simp[codegenSymRelTheory.sym_steps_compute]
QED

Theorem sym_kinds_ok_base_change:
  sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest ps (ss with sym_base := newbase)
Proof
  simp[codegenSymRelTheory.sym_kinds_ok_def]
QED

Theorem sym_kinds_ok_frame_length:
  sym_kinds_ok cplan fn ret srest ps ss ==>
  LENGTH ps.ps_stack <= LENGTH ss.sym_stack
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def] >>
  imp_res_tac LIST_REL_LENGTH >> gvs[]
QED

Theorem sym_swap_kind_step:
  sym_kinds_ok cplan fn ret srest ps ss /\
  0 < d /\ d < LENGTH ps.ps_stack ==>
  ?last. sym_swap d ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_swap d ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> imp_res_tac sym_kinds_ok_frame_length >>
  simp[sym_swap_def, sym_set_stack_def, asm_next_def,
       sym_kinds_ok_base_change, sym_kinds_ok_swap]
QED

Theorem sym_dup_kind_step:
  sym_kinds_ok cplan fn ret srest ps ss /\
  d < LENGTH ps.ps_stack ==>
  ?last. sym_dup d ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_dup d ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> imp_res_tac sym_kinds_ok_frame_length >>
  simp[sym_dup_def, sym_set_stack_def, asm_next_def,
       sym_kinds_ok_base_change, sym_kinds_ok_dup]
QED

Theorem sym_exec_swap:
  sym_kinds_ok cplan fn ret srest ps ss /\
  0 < d /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSwap d]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [SOSwap d])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_swap d ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp [SOSwap d]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[execute_plan_def, exec_stack_op_def] >> strip_tac >>
  metis_tac[sym_steps_singleton, sym_step_swap_name, sym_swap_kind_step]
QED

Theorem sym_exec_dup:
  sym_kinds_ok cplan fn ret srest ps ss /\
  d <= 15 /\ d < LENGTH ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SODup (d+1)]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [SODup (d+1)])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_dup d ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp [SODup (d+1)]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[execute_plan_def, exec_stack_op_def] >> strip_tac >>
  metis_tac[sym_steps_singleton, sym_step_dup_name, sym_dup_kind_step]
QED

Theorem sym_do_swap_small:
  do_swap d ps = (ops,out) /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Cases_on `d = 0`
  >- (simp[do_swap_def, execute_plan_def, sym_steps_def] >> metis_tac[]) >>
  strip_tac >> gvs[do_swap_def] >>
  metis_tac[sym_exec_swap, arithmeticTheory.NOT_ZERO_LT_ZERO, arithmeticTheory.ADD_COMM]
QED

Theorem sym_do_dup_small:
  do_dup d ps = (ops,out) /\ d <= 15 /\ d < LENGTH ps.ps_stack /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> gvs[do_dup_def] >> metis_tac[sym_exec_dup, arithmeticTheory.ADD_COMM]
QED

Theorem scratch_frame_durable_kinds:
  scratch_frame offsets labs labs' /\
  (!op at. FLOOKUP spilled op = SOME at ==>
    ?v. op_kind_ok fn ret op v /\ mem_sval_at labs at v) /\
  (!op at. FLOOKUP spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) ==>
  !op at. FLOOKUP spilled op = SOME at ==>
    ?v. op_kind_ok fn ret op v /\ mem_sval_at labs' at v
Proof
  metis_tac[scratch_frame_cell]
QED

Theorem sym_kinds_ok_scratch_change:
  sym_kinds_ok cplan fn ret srest ps ss /\
  scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  MEM r cplan.cp_regions /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  out.ps_spilled = ps.ps_spilled /\
  LIST_REL (op_kind_ok fn ret) (REVERSE out.ps_stack) top /\
  last.sym_stack = top ++ srest ==>
  sym_kinds_ok cplan fn ret srest out last
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def]
  >- metis_tac[scratch_frame_durable_kinds] >>
  metis_tac[scratch_frame_region, scratch_region_context_transport]
QED

Theorem scratch_swap_indices_bounded:
  2 <= n /\ LENGTH offsets = n /\
  EVERY (\off. off < dimword(:256)) offsets ==>
  EVERY (\k. k < n /\ EL k offsets < dimword(:256))
    (REVERSE ([n-1] ++ GENLIST (\i. i+1) (n-2) ++ [0]))
Proof
  rw[EVERY_EL] >> imp_res_tac desired_indices_bound >> gvs[]
QED


Theorem sym_kinds_ok_restore_change:
  sym_kinds_ok cplan fn ret srest ps ss /\ op_kind_ok fn ret op v /\
  last.sym_stack = v :: ss.sym_stack /\
  last.sym_mem_labels = ss.sym_mem_labels ==>
  sym_kinds_ok cplan fn ret srest
    (ps with <| ps_stack := stack_push op ps.ps_stack;
      ps_spilled := ps.ps_spilled \\ op; ps_alloc := al |>) last
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def, stackModelTheory.stack_push_def,
     finite_mapTheory.DOMSUB_FLOOKUP_THM]
  >- (qexists `v :: top` >> simp[]) >> metis_tac[]
QED

Theorem sym_exec_restore_kind:
  mem_sval_at ss.sym_mem_labels off sv /\ op_kind_ok fn ret op sv /\
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SORestore off]) ==>
  ?last v. sym_steps p env 2 ss = SymOK last /\
    last.sym_stack = v :: ss.sym_stack /\ op_kind_ok fn ret op v /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  strip_tac >> drule_all sym_steps_scratch_load_eq >>
  mp_tac (Q.INST [`ss` |-> `scratch_push_state off ss`, `stk` |-> `ss.sym_stack`] sym_mload_kind) >>
  simp[arithmeticTheory.ADD_ASSOC]
QED

Theorem sym_do_restore_present:
  FLOOKUP ps.ps_spilled op = SOME off /\ off < dimword(:256) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SORestore off]) ==>
  ?last. sym_steps p env 2 ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with <| ps_stack := stack_push op ps.ps_stack;
        ps_spilled := ps.ps_spilled \\ op;
        ps_alloc := free_spill_slot off ps.ps_alloc |>) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `?sv. op_kind_ok fn ret op sv /\ mem_sval_at ss.sym_mem_labels off sv`
    by metis_tac[codegenSymRelTheory.sym_kinds_ok_def] >>
  drule_all sym_exec_restore_kind >> metis_tac[sym_kinds_ok_restore_change]
QED

Theorem sym_do_restore:
  do_restore op ps = (ops,out) /\
  EVERY (\s. case s of SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- (simp[do_restore_def, execute_plan_def, sym_steps_def] >> metis_tac[]) >>
  strip_tac >> gvs[do_restore_def, execute_plan_restore_length] >>
  metis_tac[sym_do_restore_present, arithmeticTheory.ADD_COMM]
QED

Theorem sym_kinds_ok_head:
  sym_kinds_ok cplan fn ret srest ps ss /\ ps.ps_stack <> [] ==>
  ?v top. ss.sym_stack = v :: (top ++ srest) /\
    op_kind_ok fn ret (stack_peek 0 ps.ps_stack) v /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (stack_pop 1 ps.ps_stack)) top
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def] >>
  Cases_on `ps.ps_stack` using SNOC_CASES >> gvs[] >>
  gvs[stackModelTheory.stack_peek_def, stackModelTheory.stack_pop_def,
      rich_listTheory.SNOC_APPEND, EL_LENGTH_APPEND, TAKE_LENGTH_APPEND,
      REVERSE_APPEND, LIST_REL_CONS1]
QED

Theorem sym_kinds_ok_spill_change:
  sym_kinds_ok cplan fn ret srest ps ss /\
  scratch_frame [off] ss.sym_mem_labels last.sym_mem_labels /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==> off+32 <= at \/ at+32 <= off) /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end /\
  scratch_kinds_ok fn ret [stack_peek 0 ps.ps_stack] [off] last.sym_mem_labels /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (stack_pop 1 ps.ps_stack)) top /\
  last.sym_stack = top ++ srest ==>
  sym_kinds_ok cplan fn ret srest
    (ps with <| ps_stack := stack_pop 1 ps.ps_stack;
      ps_spilled := ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, off);
      ps_alloc := al |>) last
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def, finite_mapTheory.FLOOKUP_UPDATE]
  >- (Cases_on `stack_peek 0 ps.ps_stack = op` >>
      gvs[scratch_kinds_ok_def, scratch_frame_def] >> metis_tac[]) >>
  drule scratch_frame_region >> simp[] >>
  metis_tac[scratch_region_context_transport]
QED

Theorem sym_exec_spill_kind:
  sym_kinds_ok cplan fn ret srest ps ss /\ ps.ps_stack <> [] /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==> off+32 <= at \/ at+32 <= off) /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end /\
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSpill off]) ==>
  ?last. sym_steps p env 2 ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with <| ps_stack := stack_pop 1 ps.ps_stack;
        ps_spilled := ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, off);
        ps_alloc := al |>) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all sym_kinds_ok_head >> strip_tac >>
  drule_all sym_spill_scratch_head >> disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `last` >> simp[] >>
  reverse conj_tac
  >- (drule scratch_frame_region >> simp[] >> metis_tac[]) >>
  irule sym_kinds_ok_spill_change >> simp[] >> metis_tac[]
QED

Theorem scratch_swap_restore_indices:
  LENGTH items = dist+1 /\ 0 < dist /\ LENGTH offsets = LENGTH items /\
  EVERY (\off. off < dimword(:256)) offsets ==>
  EVERY (\k. k < LENGTH (REVERSE items) /\ EL k offsets < dimword(:256))
    (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))
Proof
  strip_tac >>
  mp_tac (Q.INST [`n` |-> `dist+1`] scratch_swap_indices_bounded) >> simp[]
QED

Theorem LIST_REL_scratch_swap_order[local]:
  LENGTH items = dist+1 /\ 0 < dist /\
  LIST_REL R (MAP (\k. EL k (REVERSE items))
    ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])) top ==>
  LIST_REL R (REVERSE (MAP (\k. EL k items)
    ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))) top
Proof
  simp[reverse_desired_values]
QED

Theorem sym_restore_scratch_swap_bounded:
  scratch_kinds_ok fn ret (REVERSE items) offsets ss.sym_mem_labels /\
  LENGTH items = dist+1 /\ 0 < dist /\
  EVERY (\k. k < LENGTH (REVERSE items) /\ EL k offsets < dimword(:256))
    (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])) /\
  ss.sym_stack = stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])))) ==>
  ?last top. sym_steps p env
    (LENGTH (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets))
        (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))
Proof
  strip_tac >>
  drule_all_then (qspec_then `env` mp_tac o
    PURE_REWRITE_RULE [MAP_REVERSE, REVERSE_REVERSE]) sym_restore_scratch_list >>
  metis_tac[LIST_REL_scratch_swap_order, MAP_REVERSE]
QED

Theorem sym_restore_scratch_swap:
  scratch_kinds_ok fn ret (REVERSE items) offsets ss.sym_mem_labels /\
  LENGTH items = dist+1 /\ 0 < dist /\ LENGTH offsets = LENGTH items /\
  EVERY (\off. off < dimword(:256)) offsets /\
  ss.sym_stack = stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])))) ==>
  ?last top. sym_steps p env
    (LENGTH (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets))
        (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))
Proof
  strip_tac >> drule_all scratch_swap_restore_indices >>
  metis_tac[sym_restore_scratch_swap_bounded]
QED
