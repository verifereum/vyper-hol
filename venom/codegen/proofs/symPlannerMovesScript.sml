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

Theorem sym_spill_scratch_prefix:
  LIST_REL (op_kind_ok fn ret) items vals /\
  LENGTH offsets = LENGTH items /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets /\ ss.sym_stack = vals ++ stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (MAP SOSpill offsets ++ loads)) ==>
  ?mid. sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) ss = SymOK mid /\
    mid.sym_stack = stk /\ scratch_kinds_ok fn ret items offsets mid.sym_mem_labels /\
    scratch_frame offsets ss.sym_mem_labels mid.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (MAP SOSpill offsets)) /\
    asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp loads)
Proof
  rw[execute_plan_append, asm_block_at_append] >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_spill_scratch_list >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem sym_scratch_swap_continue[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) ss = SymOK mid /\
  mid.sym_stack = stk /\
  scratch_kinds_ok fn ret (REVERSE items) offsets mid.sym_mem_labels /\
  scratch_frame offsets ss.sym_mem_labels mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (MAP SOSpill offsets)) /\
  LENGTH items = dist+1 /\ 0 < dist /\ LENGTH offsets = LENGTH items /\
  EVERY (\off. off < dimword(:256)) offsets /\
  asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp
    (MAP (\k. SORestore (EL k offsets)) (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
    (MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))) top /\
    scratch_kinds_ok fn ret (REVERSE items) offsets last.sym_mem_labels /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
        (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))
Proof
  strip_tac >> drule_all_then (qspec_then `env` strip_assume_tac) sym_restore_scratch_swap >>
  drule_all_then MATCH_ACCEPT_TAC scratch_roundtrip_finish
QED

Theorem sym_scratch_swap_roundtrip:
  LIST_REL (op_kind_ok fn ret) (REVERSE items) vals /\
  LENGTH items = dist+1 /\ 0 < dist /\ LENGTH offsets = LENGTH items /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets /\ ss.sym_stack = vals ++ stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
    (MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))) top /\
    scratch_kinds_ok fn ret (REVERSE items) offsets last.sym_mem_labels /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
        (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))))
Proof
  strip_tac >>
  drule_all_then (qspec_then `env` strip_assume_tac)
    (PURE_REWRITE_RULE [LENGTH_REVERSE]
      (Q.INST [`items` |-> `REVERSE items`] sym_spill_scratch_prefix)) >>
  drule_all_then MATCH_ACCEPT_TAC sym_scratch_swap_continue
QED

Theorem LIST_REL_prefix_split[local]:
  !xs ys zs. LIST_REL R (xs ++ ys) zs ==>
  ?front back. zs = front ++ back /\ LIST_REL R xs front /\ LIST_REL R ys back
Proof
  Induct >> simp[LIST_REL_CONS1] >> metis_tac[APPEND]
QED

Theorem sym_kinds_ok_scratch_split:
  sym_kinds_ok cplan fn ret srest ps ss /\ n <= LENGTH ps.ps_stack ==>
  ?vals rest. ss.sym_stack = vals ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (top_n n ps.ps_stack)) vals /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (TAKE (LENGTH ps.ps_stack - n) ps.ps_stack)) rest
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def] >>
  drule top_n_suffix >> disch_then (fn th =>
    qpat_x_assum `LIST_REL _ _ _`
      (mp_tac o PURE_REWRITE_RULE [REVERSE_APPEND] o ONCE_REWRITE_RULE [GSYM th])) >>
  metis_tac[LIST_REL_prefix_split, APPEND_ASSOC]
QED

Theorem scratch_layout_region_facts[local]:
  LENGTH offsets = LENGTH items /\ al.sa_spill_base = bot /\
  lo <= bot /\ al.sa_next_offset <= hi /\
  EVERY (\off. al.sa_spill_base <= off /\ off+32 <= al.sa_next_offset) offsets /\
  (!k. k < LENGTH offsets ==>
    (!op old. FLOOKUP spilled op = SOME old ==>
      old+32 <= EL k offsets \/ EL k offsets+32 <= old) /\
    (!j. j < LENGTH offsets /\ j <> k ==>
      EL j offsets+32 <= EL k offsets \/ EL k offsets+32 <= EL j offsets)) ==>
  LENGTH offsets = LENGTH items /\
  EVERY (\off. lo <= off /\ off+32 <= hi) offsets /\
  (!op at. FLOOKUP spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets)
Proof
  gvs[EVERY_EL] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem scratch_swap_allocation_facts:
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc items) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc items)) offsets /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\ al.sa_next_offset <= r.sr_spill_end ==>
  LENGTH offsets = LENGTH items /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac spill_alloc_n_temporary_layout >>
  drule_all_then MATCH_ACCEPT_TAC scratch_layout_region_facts
QED

Theorem sym_scratch_swap_finish[local]:
  sym_kinds_ok cplan fn ret srest ps ss /\
  scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  MEM r cplan.cp_regions /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  out.ps_spilled = ps.ps_spilled /\ out.ps_stack = bottom ++ restored /\
  LIST_REL (op_kind_ok fn ret) (REVERSE bottom) rest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE restored) top /\
  last.sym_stack = top ++ (rest ++ srest) ==>
  sym_kinds_ok cplan fn ret srest out last /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
    FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> conj_tac
  >- (irule sym_kinds_ok_scratch_change >>
      simp[REVERSE_APPEND, APPEND_ASSOC] >>
      metis_tac[LIST_REL_APPEND_suff]) >>
  metis_tac[scratch_frame_region]
QED


Theorem sym_scratch_swap_complete[local]:
  sym_kinds_ok cplan fn ret srest ps ss /\
  scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  MEM r cplan.cp_regions /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  out.ps_spilled = ps.ps_spilled /\ out.ps_stack = bottom ++ restored /\
  LIST_REL (op_kind_ok fn ret) (REVERSE bottom) rest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE restored) top /\
  last.sym_stack = top ++ (rest ++ srest) /\
  sym_steps p env n ss = SymOK last /\ last.sym_base.as_pc = ss.sym_base.as_pc + n ==>
  ?last. sym_steps p env n ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + n /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all_then strip_assume_tac sym_scratch_swap_finish >>
  metis_tac[]
QED

Theorem sym_scratch_swap_sim:
  sym_kinds_ok cplan fn ret srest ps ss /\
  LIST_REL (op_kind_ok fn ret) (REVERSE items) vals /\
  LIST_REL (op_kind_ok fn ret) (REVERSE bottom) rest /\
  ss.sym_stack = vals ++ (rest ++ srest) /\
  LENGTH items = dist+1 /\ 0 < dist /\ LENGTH offsets = LENGTH items /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  MEM r cplan.cp_regions /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  out.ps_spilled = ps.ps_spilled /\
  out.ps_stack = bottom ++ MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]) /\
  ops = MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
    (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  qpat_assum `ops = _` (fn th =>
    drule_all_then (qspec_then `env` strip_assume_tac)
      (PURE_REWRITE_RULE [GSYM th] sym_scratch_swap_roundtrip)) >>
  drule_all_then MATCH_ACCEPT_TAC sym_scratch_swap_complete
QED

Theorem sym_do_swap_big_shape:
  16 < dist /\ dist < LENGTH ps.ps_stack /\ do_swap dist ps = (ops,out) /\
  items = top_n (dist+1) ps.ps_stack /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc items) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc items)) offsets ==>
  LENGTH items = dist+1 /\ 0 < dist /\
  out.ps_spilled = ps.ps_spilled /\ out.ps_alloc = al /\
  out.ps_stack = TAKE (LENGTH ps.ps_stack - (dist+1)) ps.ps_stack ++
    MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]) /\
  ops = MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
    (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))
Proof
  strip_tac >> drule_all (SRULE [arithmeticTheory.GREATER_DEF] do_swap_big_decompose) >>
  gvs[top_n_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem sym_swap_shape_witnesses[local]:
  do_swap dist ps = (ops,out) /\ 16 < dist /\ dist < LENGTH ps.ps_stack ==>
  ?items offsets al.
    items = top_n (dist+1) ps.ps_stack /\
    offsets = FST (spill_alloc_n [] ps.ps_alloc items) /\
    al = FOLDL (\a off. free_spill_slot off a)
      (SND (spill_alloc_n [] ps.ps_alloc items)) offsets /\
    LENGTH items = dist+1 /\ 0 < dist /\
    out.ps_spilled = ps.ps_spilled /\ out.ps_alloc = al /\
    out.ps_stack = TAKE (LENGTH ps.ps_stack - (dist+1)) ps.ps_stack ++
      MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]) /\
    ops = MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
      (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]))
Proof
  strip_tac >> simp_tac bool_ss [] >> metis_tac[sym_do_swap_big_shape]
QED

Theorem sym_swap_frame_ready[local]:
  sym_kinds_ok cplan fn ret srest ps ss /\
  dist < LENGTH ps.ps_stack /\ items = top_n (dist+1) ps.ps_stack ==>
  ?vals rest. ss.sym_stack = vals ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE items) vals /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (TAKE (LENGTH ps.ps_stack - (dist+1)) ps.ps_stack)) rest
Proof
  rw_tac bool_ss [] >>
  irule (Q.INST [`cplan` |-> `cplan`] sym_kinds_ok_scratch_split) >>
  simp[SF SFY_ss]
QED

Theorem sym_spill_encoding_projection[local]:
  ops = MAP SOSpill offsets ++ tail /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops ==>
  EVERY (\off. off < dimword(:256)) offsets
Proof
  rw[] >> gvs[EVERY_APPEND, EVERY_MAP]
QED

Theorem sym_swap_geometry[local]:
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc items) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc items)) offsets /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\ al.sa_next_offset <= r.sr_spill_end /\
  ops = MAP SOSpill offsets ++ tail /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops ==>
  LENGTH offsets = LENGTH items /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets
Proof
  strip_tac >> drule_all_then strip_assume_tac scratch_swap_allocation_facts >>
  metis_tac[sym_spill_encoding_projection]
QED

Theorem sym_swap_shaped_ready[local]:
  items = top_n (dist+1) ps.ps_stack /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc items) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc items)) offsets /\
  out.ps_alloc = al /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  ops = MAP SOSpill offsets ++ tail /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  ?vals rest. ss.sym_stack = vals ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE items) vals /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (TAKE (LENGTH ps.ps_stack - (dist+1)) ps.ps_stack)) rest /\
    LENGTH offsets = LENGTH items /\
    EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
    (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
      EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
    (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets) /\
    EVERY (\off. off < dimword(:256)) offsets
Proof
  strip_tac >> drule_all_then strip_assume_tac sym_swap_frame_ready >>
  metis_tac[sym_swap_geometry]
QED

Theorem sym_swap_shaped_sim[local]:
  items = top_n (dist+1) ps.ps_stack /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc items) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc items)) offsets /\
  out.ps_alloc = al /\ dist < LENGTH ps.ps_stack /\
  LENGTH items = dist+1 /\ 0 < dist /\
  out.ps_spilled = ps.ps_spilled /\
  out.ps_stack = TAKE (LENGTH ps.ps_stack - (dist+1)) ps.ps_stack ++
    MAP (\k. EL k items) ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0]) /\
  ops = MAP SOSpill offsets ++ MAP (\k. SORestore (EL k offsets))
    (REVERSE ([dist] ++ GENLIST (\i. i+1) (dist-1) ++ [0])) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
  strip_tac >> drule_all_then strip_assume_tac sym_swap_shaped_ready >>
  drule_all_then MATCH_ACCEPT_TAC sym_scratch_swap_sim
QED

Theorem sym_do_swap_big:
  do_swap dist ps = (ops,out) /\ 16 < dist /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
  strip_tac >> drule_all_then strip_assume_tac sym_swap_shape_witnesses >>
  drule_all_then MATCH_ACCEPT_TAC sym_swap_shaped_sim
QED

Theorem sym_do_swap:
  do_swap dist ps = (ops,out) /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
  strip_tac >> Cases_on `dist <= 16`
  >- (drule_all_then MATCH_ACCEPT_TAC sym_do_swap_small) >>
  `16 < dist` by decide_tac >> drule_all_then MATCH_ACCEPT_TAC sym_do_swap_big
QED

Theorem sym_swap_one_stack[local]:
  ss.sym_stack = w::v::stk ==>
  ?last. sym_swap 1 ss = SymOK last /\
    last.sym_stack = v::w::stk /\ last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[sym_swap_def, sym_set_stack_def, asm_next_def, LUPDATE_compute]
QED

Theorem sym_exec_swap_one_stack:
  ss.sym_stack = w::v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSwap 1]) ==>
  ?last. sym_steps p env 1 ss = SymOK last /\
    last.sym_stack = v::w::stk /\ last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rw[execute_plan_def, exec_stack_op_def] >>
  drule sym_steps_singleton >>
  simp[sym_step_swap_name, sym_swap_one_stack]
QED

Theorem sym_steps_unchanged_mem_compose[local]:
  sym_steps p env m ss = SymOK mid /\
  sym_steps p env n mid = SymOK last /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + m /\
  last.sym_base.as_pc = mid.sym_base.as_pc + n ==>
  sym_steps p env (m+n) ss = SymOK last /\
  last.sym_mem_labels = ss.sym_mem_labels /\
  last.sym_base.as_pc = ss.sym_base.as_pc + (m+n)
Proof
  strip_tac >> drule_all_then assume_tac sym_steps_compose_ok >>
  asm_simp_tac bool_ss [arithmeticTheory.ADD_ASSOC]
QED

Theorem sym_swap_one_stack_transport[local]:
  mid.sym_stack = w::v::stk /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  asm_block_at p (ss.sym_base.as_pc + 2)
    (execute_plan initial_fmp [SOSwap 1]) ==>
  ?last. sym_steps p env 1 mid = SymOK last /\
    last.sym_stack = v::w::stk /\ last.sym_mem_labels = mid.sym_mem_labels /\
    last.sym_base.as_pc = mid.sym_base.as_pc + 1
Proof
  strip_tac >> irule sym_exec_swap_one_stack >> simp[SF SFY_ss]
QED

Theorem sym_restore_swap_pair_post[local]:
  sym_steps p env 2 ss = SymOK mid /\
  sym_steps p env 1 mid = SymOK last /\
  last.sym_stack = v::w::stk /\ op_kind_ok fn ret op w /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  last.sym_base.as_pc = mid.sym_base.as_pc + 1 ==>
  ?last w. sym_steps p env 3 ss = SymOK last /\
    last.sym_stack = v::w::stk /\ op_kind_ok fn ret op w /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 3
Proof
  strip_tac >> drule_all sym_steps_unchanged_mem_compose >>
  simp[SF SFY_ss]
QED

Theorem sym_restore_swap_one_finish[local]:
  sym_steps p env 2 ss = SymOK mid /\
  mid.sym_stack = w::v::stk /\ op_kind_ok fn ret op w /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  asm_block_at p (ss.sym_base.as_pc + 2)
    (execute_plan initial_fmp [SOSwap 1]) ==>
  ?last w. sym_steps p env 3 ss = SymOK last /\
    last.sym_stack = v::w::stk /\ op_kind_ok fn ret op w /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 3
Proof
  strip_tac >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_swap_one_stack_transport >>
  metis_tac[sym_restore_swap_pair_post]
QED

Theorem asm_block_at_restore_swap[local]:
  asm_block_at p pc (execute_plan f [SORestore off; SOSwap 1]) ==>
  asm_block_at p pc (execute_plan f [SORestore off]) /\
  asm_block_at p (pc+2) (execute_plan f [SOSwap 1])
Proof
  gvs[execute_plan_def, exec_stack_op_def,
    stackOpSimTheory.asm_block_at_cons]
QED

Theorem sym_restore_swap_one:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  j < LENGTH items /\ EL j offsets < dimword(:256) /\
  ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp [SORestore (EL j offsets); SOSwap 1]) ==>
  ?last w. sym_steps p env 3 ss = SymOK last /\
    last.sym_stack = v::w::stk /\ op_kind_ok fn ret (EL j items) w /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 3
Proof
  strip_tac >> drule_then strip_assume_tac asm_block_at_restore_swap >>
  metis_tac[sym_restore_scratch_index, sym_restore_swap_one_finish]
QED

Theorem execute_plan_restore_swap_cons[local]:
  execute_plan f (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))) =
  execute_plan f [SORestore (EL j offsets); SOSwap 1] ++
  execute_plan f (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js))
Proof
  simp[execute_plan_def]
QED

Theorem execute_plan_restore_swap_length[local]:
  LENGTH (execute_plan f [SORestore off; SOSwap 1]) = 3
Proof
  simp[execute_plan_def, exec_stack_op_def]
QED

Theorem execute_plan_restore_swap_cons_length[local]:
  LENGTH (execute_plan f (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js)))) =
  3 + LENGTH (execute_plan f (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))
Proof
  rewrite_tac[execute_plan_restore_swap_cons, LENGTH_APPEND,
    execute_plan_restore_swap_length]
QED

Theorem carried_restore_rel_snoc[local]:
  LIST_REL R (REVERSE (MAP g js)) top /\ R (g j) w ==>
  LIST_REL R (REVERSE (MAP g (j::js))) (top ++ [w])
Proof
  simp[rich_listTheory.LIST_REL_APPEND_SING]
QED

Theorem carried_restore_pack[local]:
  sym_steps p env n ss = SymOK last /\
  last.sym_stack = v::(top ++ w::stk) /\
  LIST_REL R (REVERSE (MAP g js)) top /\ R (g j) w /\
  last.sym_mem_labels = ss.sym_mem_labels /\
  last.sym_base.as_pc = ss.sym_base.as_pc + n ==>
  ?top'. sym_steps p env n ss = SymOK last /\
    last.sym_stack = v::(top' ++ stk) /\
    LIST_REL R (REVERSE (MAP g (j::js))) top' /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + n
Proof
  strip_tac >> qexists_tac `top ++ [w]` >>
  asm_simp_tac bool_ss [carried_restore_rel_snoc, GSYM APPEND_ASSOC, APPEND]
QED

Theorem carried_restore_compose[local]:
  sym_steps p env 3 ss = SymOK mid /\
  sym_steps p env n mid = SymOK last /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 3 /\
  last.sym_stack = v::(top ++ w::stk) /\
  LIST_REL R (REVERSE (MAP g js)) top /\ R (g j) w /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  last.sym_base.as_pc = mid.sym_base.as_pc + n ==>
  ?top'. sym_steps p env (3+n) ss = SymOK last /\
    last.sym_stack = v::(top' ++ stk) /\
    LIST_REL R (REVERSE (MAP g (j::js))) top' /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + (3+n)
Proof
  strip_tac >> drule_all_then strip_assume_tac sym_steps_unchanged_mem_compose >>
  metis_tac[carried_restore_pack]
QED

Theorem sym_restore_swap_fold_post[local]:
  sym_steps p env 3 ss = SymOK mid /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 3 /\
  op_kind_ok fn ret (EL j items) w /\
  sym_steps p env (LENGTH (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))) mid = SymOK last /\
  last.sym_stack = v::(top ++ w::stk) /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) js)) top /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  last.sym_base.as_pc = mid.sym_base.as_pc + LENGTH (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js))) ==>
  ?top'. sym_steps p env (LENGTH (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))))) ss = SymOK last /\
    last.sym_stack = v::(top' ++ stk) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) (j::js))) top' /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan f
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))))
Proof
  pure_rewrite_tac[execute_plan_restore_swap_cons_length] >>
  strip_tac >> simp[carried_restore_compose]
QED

Theorem sym_restore_carried_finish[local]:
  sym_steps p env 3 ss = SymOK mid /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 3 /\
  op_kind_ok fn ret (EL j items) w /\
  (?last top. sym_steps p env (LENGTH (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))) mid = SymOK last /\
  last.sym_stack = v::(top ++ w::stk) /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) js)) top /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  last.sym_base.as_pc = mid.sym_base.as_pc + LENGTH (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) (j::js))) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan f
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))))
Proof
  strip_tac >> qexists_tac `last` >> simp[sym_restore_swap_fold_post]
QED

Theorem sym_restore_carried_continue[local]:
  (!ss stk.
    scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
    EVERY (\j. j < LENGTH items /\ EL j offsets < dimword(:256)) js /\
    ss.sym_stack = v::stk /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js))) ==>
    ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
        (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))) ss = SymOK last /\
      last.sym_stack = v::(top ++ stk) /\
      LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) js)) top /\
      last.sym_mem_labels = ss.sym_mem_labels /\
      last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
        (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))) /\
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\j. j < LENGTH items /\ EL j offsets < dimword(:256)) js /\
  sym_steps p env 3 ss = SymOK mid /\ mid.sym_stack = v::w::stk /\
  op_kind_ok fn ret (EL j items) w /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 3 /\
  asm_block_at p (ss.sym_base.as_pc + 3) (execute_plan initial_fmp
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) (j::js))) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js))))
Proof
  strip_tac >> irule sym_restore_carried_finish >> metis_tac[]
QED

Theorem asm_block_at_restore_swap_cons[local]:
  asm_block_at p pc (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) (j::js)))) <=>
  asm_block_at p pc (execute_plan f [SORestore (EL j offsets); SOSwap 1]) /\
  asm_block_at p (pc+3) (execute_plan f
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) js)))
Proof
  rewrite_tac[execute_plan_restore_swap_cons, stackOpSimTheory.asm_block_at_append,
    execute_plan_restore_swap_length]
QED

Theorem sym_restore_scratch_carried:
  !indices ss stk.
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\j. j < LENGTH items /\ EL j offsets < dimword(:256)) indices /\
  ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) indices))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) indices)))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) indices)) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) indices)))
Proof
  Induct >- simp[execute_plan_def, codegenSymRelTheory.sym_steps_compute] >>
  rw_tac bool_ss [EVERY_DEF, asm_block_at_restore_swap_cons] >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_restore_swap_one >>
  simp[sym_restore_carried_continue]
QED

Theorem reverse_top_n_partition:
  k <= LENGTH xs ==>
  REVERSE xs = REVERSE (top_n k xs) ++ REVERSE (TAKE (LENGTH xs-k) xs)
Proof
  strip_tac >> drule top_n_suffix >> metis_tac[REVERSE_APPEND]
QED

Theorem deep_dup_residual_lengths[local]:
  15 < dist /\ dist < LENGTH xs /\ k = dist-15 ==>
  LENGTH (REVERSE (top_n k xs)) = k /\
  15 < LENGTH (REVERSE (TAKE (LENGTH xs-k) xs))
Proof
  simp[top_n_def, LENGTH_TAKE] >> decide_tac
QED

Theorem deep_dup_residual_index[local]:
  REVERSE xs = a ++ b /\ LENGTH a = dist-15 /\ 15 < dist ==>
  EL 15 b = EL dist (REVERSE xs)
Proof
  strip_tac >> simp[EL_APPEND_EQN]
QED

Theorem deep_dup_residual_shape:
  15 < dist /\ dist < LENGTH xs /\ k = dist-15 /\
  a = REVERSE (top_n k xs) /\ b = REVERSE (TAKE (LENGTH xs-k) xs) ==>
  REVERSE xs = a ++ b /\ LENGTH a = k /\ 15 < LENGTH b /\
  EL 15 b = EL dist (REVERSE xs)
Proof
  strip_tac >>
  `k <= LENGTH xs` by decide_tac >>
  metis_tac[reverse_top_n_partition, deep_dup_residual_lengths, deep_dup_residual_index]
QED

Theorem sym_dup_sixteen_stack[local]:
  15 < LENGTH rest /\ ss.sym_stack = rest ++ srest ==>
  ?mid. sym_dup 15 ss = SymOK mid /\
    mid.sym_stack = EL 15 rest :: (rest ++ srest) /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[sym_dup_def, sym_set_stack_def, asm_next_def, EL_APPEND_EQN]
QED

Theorem sym_exec_dup_sixteen_stack:
  15 < LENGTH rest /\ ss.sym_stack = rest ++ srest /\
  asm_block_at p ss.sym_base.as_pc (execute_plan f [SODup 16]) ==>
  ?mid. sym_steps p env 1 ss = SymOK mid /\
    mid.sym_stack = EL 15 rest :: (rest ++ srest) /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rw[execute_plan_def, exec_stack_op_def] >>
  drule sym_steps_singleton >>
  simp[SRULE [] (Q.INST [`d` |-> `15`] sym_step_dup_name), sym_dup_sixteen_stack]
QED

Theorem asm_block_at_dup_sixteen[local]:
  asm_block_at p pc (execute_plan f ([SODup 16] ++ tail)) ==>
  asm_block_at p pc (execute_plan f [SODup 16]) /\
  asm_block_at p (pc+1) (execute_plan f tail)
Proof
  simp[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons]
QED

Theorem sym_dup_sixteen_residual_finish[local]:
  LIST_REL (op_kind_ok fn ret) b rest /\ 15 < LENGTH b /\
  sym_steps p env 1 ss = SymOK mid /\
  mid.sym_stack = EL 15 rest :: (rest ++ srest) /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
  asm_block_at p (ss.sym_base.as_pc+1) (execute_plan f tail) ==>
  ?mid. sym_steps p env 1 ss = SymOK mid /\
    mid.sym_stack = EL 15 rest :: (rest ++ srest) /\
    op_kind_ok fn ret (EL 15 b) (EL 15 rest) /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    asm_block_at p mid.sym_base.as_pc (execute_plan f tail)
Proof
  rw[LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem sym_dup_sixteen_residual:
  LIST_REL (op_kind_ok fn ret) b rest /\ 15 < LENGTH b /\
  ss.sym_stack = rest ++ srest /\
  asm_block_at p ss.sym_base.as_pc (execute_plan f ([SODup 16] ++ tail)) ==>
  ?mid. sym_steps p env 1 ss = SymOK mid /\
    mid.sym_stack = EL 15 rest :: (rest ++ srest) /\
    op_kind_ok fn ret (EL 15 b) (EL 15 rest) /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    asm_block_at p mid.sym_base.as_pc (execute_plan f tail)
Proof
  strip_tac >> drule_then strip_assume_tac asm_block_at_dup_sixteen >>
  metis_tac[LIST_REL_LENGTH, sym_exec_dup_sixteen_stack, sym_dup_sixteen_residual_finish]
QED

Theorem dup_restore_descending_values:
  LENGTH a = k /\ 0 < k ==>
  MAP (\j. EL j a) (GENLIST (\i. k-1-i) k) = REVERSE a
Proof
  strip_tac >> drule_then strip_assume_tac dup_restore_indices_reverse >>
  gvs[map_el_reverse_indices]
QED

Theorem map_el_initial_indices[local]:
  n <= LENGTH a ==> MAP (\j. EL j a) (GENLIST I n) = TAKE n a
Proof
  strip_tac >> irule LIST_EQ >>
  simp[EL_MAP, EL_GENLIST, EL_TAKE, LENGTH_TAKE]
QED

Theorem map_el_reverse_initial_snoc[local]:
  n <= LENGTH a ==>
  REVERSE (MAP (\j. EL j a) (REVERSE (GENLIST I n) ++ [last])) =
  [EL last a] ++ TAKE n a
Proof
  simp[MAP_REVERSE, map_el_initial_indices]
QED

Theorem dup_restore_short_values:
  LENGTH a = k /\ 0 < k ==>
  REVERSE (MAP (\j. EL j a)
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1])) =
  [EL (k-1) a] ++ TAKE (k-1) a
Proof
  strip_tac >> drule_then strip_assume_tac dup_restore_indices_reverse >>
  asm_simp_tac bool_ss [map_el_reverse_initial_snoc, arithmeticTheory.SUB_LESS_EQ]
QED

Theorem dup_restore_descending_bound:
  0 < k ==> EVERY (\j. j < k) (GENLIST (\i. k-1-i) k)
Proof
  rw[EVERY_GENLIST] >> decide_tac
QED

Theorem dup_restore_short_bound:
  0 < k ==> EVERY (\j. j < k)
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1])
Proof
  rw[EVERY_GENLIST] >> decide_tac
QED

Theorem dup_restore_descending_ready[local]:
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\
  EVERY (\off. off < dimword(:256)) offsets ==>
  EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-1-i) k)
Proof
  rw[EVERY_GENLIST, EVERY_EL] >> simp[EL_GENLIST] >> decide_tac
QED

Theorem sym_dup_restore_long_bounded[local]:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ 16 < k /\
  EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-1-i) k) /\ ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k)))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
        (GENLIST (\i. k-1-i) k))))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
        (GENLIST (\i. k-1-i) k))))
Proof
  strip_tac >> drule_all_then (qspec_then `env` strip_assume_tac) sym_restore_scratch_carried >>
  gvs[dup_restore_descending_values, SF SFY_ss]
QED

Theorem sym_dup_restore_long:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ LENGTH offsets = k /\ 16 < k /\
  EVERY (\off. off < dimword(:256)) offsets /\ ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k)))) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
        (GENLIST (\i. k-1-i) k))))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
        (GENLIST (\i. k-1-i) k))))
Proof
  strip_tac >>
  `EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-1-i) k)` by
      (irule dup_restore_descending_ready >> simp[SF SFY_ss]) >>
  drule_all_then MATCH_ACCEPT_TAC sym_dup_restore_long_bounded
QED

Theorem sym_swap_carried_end[local]:
  ss.sym_stack = w::(front ++ v::stk) /\ k = LENGTH front+1 ==>
  ?last. sym_swap k ss = SymOK last /\
    last.sym_stack = v::(front ++ w::stk) /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc+1
Proof
  simp[sym_swap_def, sym_set_stack_def, asm_next_def, EL_APPEND_EQN,
    LUPDATE_def, listTheory.lupdate_append2, GSYM arithmeticTheory.ADD1]
QED

Theorem sym_exec_swap_carried_end:
  ss.sym_stack = w::(front ++ v::stk) /\ k = LENGTH front+1 /\ k <= 16 /\
  asm_block_at p ss.sym_base.as_pc (execute_plan f [SOSwap k]) ==>
  ?last. sym_steps p env 1 ss = SymOK last /\
    last.sym_stack = v::(front ++ w::stk) /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc+1
Proof
  rw[execute_plan_def, exec_stack_op_def] >> drule sym_steps_singleton >>
  simp[sym_step_swap_name, SRULE [] sym_swap_carried_end]
QED

Theorem dup_restore_short_ready[local]:
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\
  EVERY (\off. off < dimword(:256)) offsets ==>
  EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1])
Proof
  rw[EVERY_GENLIST, EVERY_EL] >> simp[EL_GENLIST] >> decide_tac
QED

Theorem take_last_partition[local]:
  LENGTH a = k /\ 0 < k ==> TAKE (k-1) a ++ [EL (k-1) a] = a
Proof
  strip_tac >>
  qspec_then `k-1` (qspec_then `a` mp_tac) TAKE_DROP_SUC >>
  simp[arithmeticTheory.ADD1, DROP_LENGTH_TOO_LONG]
QED


Theorem take_last_partition_normalized[local]:
  0 < LENGTH a /\ LENGTH a - 1 = LENGTH front ==>
  TAKE (LENGTH front) a ++ [EL (LENGTH front) a] = a
Proof
  strip_tac >>
  mp_tac (Q.INST [`k` |-> `LENGTH a`] take_last_partition) >>
  asm_rewrite_tac[]
QED

Theorem list_rel_snoc_normalized[local]:
  0 < LENGTH a /\ LENGTH a - 1 = LENGTH front /\
  LIST_REL R (TAKE (LENGTH front) a) front /\
  R (EL (LENGTH front) a) w ==> LIST_REL R a (front ++ [w])
Proof
  strip_tac >>
  `LIST_REL R (TAKE (LENGTH front) a ++ [EL (LENGTH front) a])
     (front ++ [w])` by simp[LIST_REL_APPEND_SING] >>
  drule_all_then (fn th =>
    qpat_x_assum `LIST_REL R (_ ++ [_]) (front ++ [w])`
      (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [th])) take_last_partition_normalized
QED

Theorem list_rel_take_last_length[local]:
  0 < LENGTH a /\ LIST_REL R (TAKE (LENGTH a-1) a) front ==>
  LENGTH a-1 = LENGTH front /\ LENGTH a = LENGTH front+1
Proof
  strip_tac >> drule_then mp_tac LIST_REL_LENGTH >> simp[LENGTH_TAKE]
QED

Theorem list_rel_take_last_rotate_finish[local]:
  0 < LENGTH a /\ R (EL (LENGTH a-1) a) w /\
  LIST_REL R (TAKE (LENGTH a-1) a) front ==>
  LENGTH a = LENGTH front+1 /\ LIST_REL R a (front ++ [w])
Proof
  strip_tac >> drule_all_then strip_assume_tac list_rel_take_last_length >>
  metis_tac[list_rel_snoc_normalized]
QED

Theorem list_rel_short_rotate[local]:
  LENGTH a = k /\ 0 < k /\
  LIST_REL R ([EL (k-1) a] ++ TAKE (k-1) a) top ==>
  ?w front. top = w::front /\ k = LENGTH front+1 /\
    LIST_REL R a (front ++ [w])
Proof
  Cases_on `top` >> simp[LIST_REL_def] >>
  rw[LENGTH_TAKE] >>
  drule_all_then (simp o single) list_rel_take_last_rotate_finish
QED

Theorem sym_swap_carried_end_transport[local]:
  mid.sym_stack = w::(front ++ v::stk) /\ k = LENGTH front+1 /\ k <= 16 /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + n /\
  asm_block_at p (ss.sym_base.as_pc+n) (execute_plan f [SOSwap k]) ==>
  ?last. sym_steps p env 1 mid = SymOK last /\
    last.sym_stack = v::(front ++ w::stk) /\
    last.sym_mem_labels = mid.sym_mem_labels /\
    last.sym_base.as_pc = mid.sym_base.as_pc+1
Proof
  rw_tac bool_ss [] >> metis_tac[sym_exec_swap_carried_end]
QED

Theorem sym_restore_short_swap_post[local]:
  sym_steps p env n ss = SymOK mid /\
  sym_steps p env 1 mid = SymOK last /\
  last.sym_stack = v::(front ++ w::stk) /\
  LIST_REL (op_kind_ok fn ret) a (front ++ [w]) /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc+n /\
  last.sym_base.as_pc = mid.sym_base.as_pc+1 ==>
  ?last top. sym_steps p env (n+1) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc+(n+1)
Proof
  strip_tac >> drule_all_then strip_assume_tac sym_steps_unchanged_mem_compose >>
  metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem sym_restore_short_swap_rotated[local]:
  sym_steps p env n ss = SymOK mid /\
  mid.sym_stack = w::(front ++ v::stk) /\ k = LENGTH front+1 /\ k <= 16 /\
  LIST_REL (op_kind_ok fn ret) a (front ++ [w]) /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc+n /\
  asm_block_at p (ss.sym_base.as_pc+n) (execute_plan initial_fmp [SOSwap k]) ==>
  ?last top. sym_steps p env (n+1) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc+(n+1)
Proof
  strip_tac >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_swap_carried_end_transport >>
  metis_tac[sym_restore_short_swap_post]
QED

Theorem sym_restore_short_swap_finish[local]:
  sym_steps p env n ss = SymOK mid /\
  mid.sym_stack = top ++ v::stk /\ LENGTH a = k /\ 0 < k /\ k <= 16 /\
  LIST_REL (op_kind_ok fn ret) ([EL (k-1) a] ++ TAKE (k-1) a) top /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc+n /\
  asm_block_at p (ss.sym_base.as_pc+n) (execute_plan initial_fmp [SOSwap k]) ==>
  ?last top. sym_steps p env (n+1) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc+(n+1)
Proof
  strip_tac >> drule_all_then strip_assume_tac list_rel_short_rotate >>
  metis_tac[sym_restore_short_swap_rotated, APPEND]
QED

Theorem asm_block_at_restores_swap[local]:
  asm_block_at p pc (execute_plan f (ops ++ [SOSwap k])) ==>
  asm_block_at p pc (execute_plan f ops) /\
  asm_block_at p (pc + LENGTH (execute_plan f ops)) (execute_plan f [SOSwap k])
Proof
  simp[execute_plan_def, stackOpSimTheory.asm_block_at_append]
QED

Theorem list_rel_dup_restore_short_values[local]:
  LENGTH a = k /\ 0 < k /\ LIST_REL R
    (REVERSE (MAP (\j. EL j a) (GENLIST (\i. k-2-i) (k-1) ++ [k-1]))) top ==>
  LIST_REL R ([EL (k-1) a] ++ TAKE (k-1) a) top
Proof
  strip_tac >> gvs[dup_restore_short_values]
QED

Theorem sym_dup_restore_short_prefix[local]:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ 0 < k /\
  EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) /\ ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets)) (GENLIST (\i. k-2-i) (k-1) ++ [k-1]))) ==>
  ?mid top. sym_steps p env (LENGTH (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets)) (GENLIST (\i. k-2-i) (k-1) ++ [k-1])))) ss = SymOK mid /\
    mid.sym_stack = top ++ v::stk /\
    LIST_REL (op_kind_ok fn ret) ([EL (k-1) a] ++ TAKE (k-1) a) top /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets)) (GENLIST (\i. k-2-i) (k-1) ++ [k-1])))
Proof
  strip_tac >> drule_all_then (qspec_then `env` strip_assume_tac) sym_restore_scratch_list >>
  metis_tac[list_rel_dup_restore_short_values]
QED

Theorem sym_restore_short_swap_finish_plan[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK mid /\
  mid.sym_stack = top ++ v::stk /\ LENGTH a = k /\ 0 < k /\ k <= 16 /\
  LIST_REL (op_kind_ok fn ret) ([EL (k-1) a] ++ TAKE (k-1) a) top /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
  asm_block_at p (ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops))
    (execute_plan initial_fmp [SOSwap k]) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp (ops ++ [SOSwap k]))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (ops ++ [SOSwap k]))
Proof
  strip_tac >> drule_all sym_restore_short_swap_finish >>
  simp[execute_plan_def, exec_stack_op_def]
QED

Theorem sym_dup_restore_short_bounded[local]:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ 0 < k /\ k <= 16 /\
  EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) /\ ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k])) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]))
Proof
  rw_tac bool_ss [stackOpSimTheory.execute_plan_append,
    stackOpSimTheory.asm_block_at_append] >>
  drule_all_then (qspec_then `env` strip_assume_tac)
    (SIMP_RULE bool_ss [] (Q.INST [`k` |-> `LENGTH a`] sym_dup_restore_short_prefix)) >>
  drule_all_then (simp o single o REWRITE_RULE [stackOpSimTheory.execute_plan_append])
    (SIMP_RULE bool_ss [] (Q.INST [`k` |-> `LENGTH a`] sym_restore_short_swap_finish_plan))
QED

Theorem sym_dup_restore_short:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\ k <= 16 /\
  EVERY (\off. off < dimword(:256)) offsets /\ ss.sym_stack = v::stk /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k])) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
    (MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]))
Proof
  strip_tac >>
  `EVERY (\j. j < LENGTH a /\ EL j offsets < dimword(:256))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1])` by
      (irule dup_restore_short_ready >> simp[SF SFY_ss]) >>
  drule_all_then MATCH_ACCEPT_TAC sym_dup_restore_short_bounded
QED

Theorem sym_do_dup_big_shape:
  15 < dist /\ dist < LENGTH ps.ps_stack /\ do_dup dist ps = (ops,out) /\
  k = dist-15 /\ a = REVERSE (top_n k ps.ps_stack) /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc a) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc a)) offsets ==>
  LENGTH a = k /\ 0 < k /\
  out.ps_spilled = ps.ps_spilled /\ out.ps_alloc = al /\
  out.ps_stack = stack_dup dist ps.ps_stack /\
  ops = MAP SOSpill offsets ++ [SODup 16] ++
    (if k <= 16 then MAP (\j. SORestore (EL j offsets))
       (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
     else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
       (GENLIST (\i. k-1-i) k)))
Proof
  strip_tac >> drule_all (SRULE [arithmeticTheory.GREATER_DEF] do_dup_big_decompose) >>
  Cases_on `k <= 16` >> gvs[top_n_def, MAP_MAP_o, combinTheory.o_DEF, flat_map_singleton]
QED

Theorem sym_dup_restore_tail[local]:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\
  EVERY (\off. off < dimword(:256)) offsets /\ ss.sym_stack = v::stk /\
  tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
    else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k))) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp tail) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp tail)) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp tail)
Proof
  strip_tac >> Cases_on `k <= 16`
  >- (full_simp_tac bool_ss [] >> metis_tac[sym_dup_restore_short]) >>
  full_simp_tac bool_ss [] >> metis_tac[sym_dup_restore_long, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem sym_dup_residual_restore_finish[local]:
  sym_steps p env 1 ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp tail)) mid = SymOK last /\
  last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
  op_kind_ok fn ret op v /\ mid.sym_mem_labels = ss.sym_mem_labels /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc+1 /\
  last.sym_base.as_pc = mid.sym_base.as_pc + LENGTH (execute_plan initial_fmp tail) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp ([SODup 16] ++ tail))) ss = SymOK last /\
    last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
    op_kind_ok fn ret op v /\ last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ([SODup 16] ++ tail))
Proof
  strip_tac >> drule_all_then strip_assume_tac sym_steps_unchanged_mem_compose >>
  gvs[execute_plan_append, execute_plan_def,
    exec_stack_op_def, arithmeticTheory.ADD1, SF SFY_ss]
QED

Theorem sym_dup_residual_restore[local]:
  scratch_kinds_ok fn ret a offsets ss.sym_mem_labels /\
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\
  EVERY (\off. off < dimword(:256)) offsets /\
  LIST_REL (op_kind_ok fn ret) b rest /\ 15 < LENGTH b /\
  ss.sym_stack = rest ++ srest /\
  tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
    else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k))) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ([SODup 16] ++ tail)) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp ([SODup 16] ++ tail))) ss = SymOK last /\
    last.sym_stack = EL 15 rest::(top ++ (rest ++ srest)) /\
    LIST_REL (op_kind_ok fn ret) a top /\
    op_kind_ok fn ret (EL 15 b) (EL 15 rest) /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ([SODup 16] ++ tail))
Proof
  disch_then (fn th => CHOOSE_THEN (fn result => strip_assume_tac
    (CONJ (PURE_ONCE_REWRITE_RULE [GSYM (cj 4 result)] th) result))
    (SIMP_RULE bool_ss [] (CONV_RULE
      (LAND_CONV (SIMP_CONV bool_ss (CONJUNCTS th)))
      (Q.INST [`f` |-> `initial_fmp`] sym_dup_sixteen_residual)))) >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_dup_restore_tail >>
  drule_all_then MATCH_ACCEPT_TAC sym_dup_residual_restore_finish
QED

Theorem sym_dup_save_finish[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp saves)) ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp loads)) mid = SymOK last /\
  last.sym_stack = v::(top ++ stk) /\ LIST_REL (op_kind_ok fn ret) a top /\
  op_kind_ok fn ret op v /\ scratch_frame offsets ss.sym_mem_labels mid.sym_mem_labels /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp saves) /\
  last.sym_base.as_pc = mid.sym_base.as_pc + LENGTH (execute_plan initial_fmp loads) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp (saves ++ loads))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\ LIST_REL (op_kind_ok fn ret) (op::a) top /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (saves ++ loads))
Proof
  strip_tac >> drule_all_then assume_tac sym_steps_compose_ok >>
  gvs[execute_plan_append, LENGTH_APPEND, APPEND,
    LIST_REL_def, SF SFY_ss]
QED

Theorem sym_dup_save_continue[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) ss = SymOK mid /\
  mid.sym_stack = rest ++ srest /\
  scratch_kinds_ok fn ret a offsets mid.sym_mem_labels /\
  scratch_frame offsets ss.sym_mem_labels mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (MAP SOSpill offsets)) /\
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\
  EVERY (\off. off < dimword(:256)) offsets /\
  LIST_REL (op_kind_ok fn ret) b rest /\ 15 < LENGTH b /\
  tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
    else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k))) /\
  asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp ([SODup 16] ++ tail)) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ [SODup 16] ++ tail))) ss = SymOK last /\
    last.sym_stack = top ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) (EL 15 b::a) top /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ [SODup 16] ++ tail))
Proof
  strip_tac >> drule_all_then (qspec_then `env` strip_assume_tac) sym_dup_residual_restore >>
  drule_all_then (fn th => simp_tac bool_ss [APPEND_ASSOC,
    PURE_REWRITE_RULE [APPEND_ASSOC] th]) sym_dup_save_finish
QED

(* Normalize a shared equality witness without eliminating its name. *)
Theorem conj_eq_shared_right[local]:
  (x = z /\ y = z /\ P) = (x = z /\ y = x /\ P)
Proof
  metis_tac[]
QED

Theorem sym_dup_scratch_roundtrip[local]:
  LIST_REL (op_kind_ok fn ret) a vals /\
  LENGTH a = k /\ LENGTH offsets = k /\ 0 < k /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets /\
  LIST_REL (op_kind_ok fn ret) b rest /\ 15 < LENGTH b /\
  ss.sym_stack = vals ++ (rest ++ srest) /\
  tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
    else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k))) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
    (MAP SOSpill offsets ++ [SODup 16] ++ tail)) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ [SODup 16] ++ tail))) ss = SymOK last /\
    last.sym_stack = top ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) (EL 15 b::a) top /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ [SODup 16] ++ tail))
Proof
  disch_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [conj_eq_shared_right]) >>
  drule_all_then (qspec_then `env` strip_assume_tac)
    (PURE_REWRITE_RULE [APPEND_ASSOC]
      (Q.INST [`loads` |-> `[SODup 16] ++ tail`] sym_spill_scratch_prefix)) >>
  gvs[sym_dup_save_continue]
QED

Theorem LIST_REL_deep_dup_join[local]:
  dist < LENGTH xs /\ REVERSE xs = a ++ b /\
  EL 15 b = EL dist (REVERSE xs) /\
  LIST_REL R (EL 15 b::a) top /\ LIST_REL R b rest ==>
  LIST_REL R (REVERSE (stack_dup dist xs)) (top ++ rest)
Proof
  strip_tac >>
  `REVERSE (stack_dup dist xs) = EL 15 b::(a ++ b)` by
    simp[stackModelTheory.stack_dup_def, stackModelTheory.stack_peek_def, REVERSE_SNOC, EL_REVERSE, arithmeticTheory.PRE_SUB1] >>
  metis_tac[LIST_REL_APPEND_suff, APPEND]
QED

Theorem sym_dup_scratch_kinds[local]:
  sym_kinds_ok cplan fn ret srest ps ss /\
  scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  MEM r cplan.cp_regions /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  out.ps_spilled = ps.ps_spilled /\ out.ps_stack = stack_dup dist ps.ps_stack /\
  dist < LENGTH ps.ps_stack /\ REVERSE ps.ps_stack = a ++ b /\
  EL 15 b = EL dist (REVERSE ps.ps_stack) /\
  LIST_REL (op_kind_ok fn ret) (EL 15 b::a) top /\
  LIST_REL (op_kind_ok fn ret) b rest /\ last.sym_stack = top ++ (rest ++ srest) ==>
  sym_kinds_ok cplan fn ret srest out last
Proof
  strip_tac >> drule_all_then assume_tac LIST_REL_deep_dup_join >>
  metis_tac[sym_kinds_ok_scratch_change, APPEND_ASSOC]
QED

Theorem sym_dup_scratch_complete[local]:
  sym_kinds_ok cplan fn ret srest ps ss /\
  scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
  (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
    EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
  MEM r cplan.cp_regions /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
  out.ps_spilled = ps.ps_spilled /\ out.ps_stack = stack_dup dist ps.ps_stack /\
  dist < LENGTH ps.ps_stack /\ REVERSE ps.ps_stack = a ++ b /\
  EL 15 b = EL dist (REVERSE ps.ps_stack) /\
  LIST_REL (op_kind_ok fn ret) (EL 15 b::a) top /\
  LIST_REL (op_kind_ok fn ret) b rest /\ last.sym_stack = top ++ (rest ++ srest) /\
  sym_steps p env n ss = SymOK last /\ last.sym_base.as_pc = ss.sym_base.as_pc+n ==>
  ?last. sym_steps p env n ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc+n /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all_then assume_tac sym_dup_scratch_kinds >>
  metis_tac[scratch_frame_region]
QED

Theorem sym_dup_frame_ready[local]:
  sym_kinds_ok cplan fn ret srest ps ss /\
  15 < dist /\ dist < LENGTH ps.ps_stack /\ k = dist-15 /\
  a = REVERSE (top_n k ps.ps_stack) /\
  b = REVERSE (TAKE (LENGTH ps.ps_stack-k) ps.ps_stack) ==>
  ?vals rest. ss.sym_stack = vals ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) a vals /\ LIST_REL (op_kind_ok fn ret) b rest /\
    REVERSE ps.ps_stack = a ++ b /\ 15 < LENGTH b /\
    EL 15 b = EL dist (REVERSE ps.ps_stack)
Proof
  strip_tac >> drule_all_then strip_assume_tac deep_dup_residual_shape >>
  metis_tac[sym_kinds_ok_scratch_split, LENGTH_APPEND, LENGTH_REVERSE,
    arithmeticTheory.LESS_EQ_ADD]
QED

Theorem sym_dup_shape_witnesses[local]:
  do_dup dist ps = (ops,out) /\ 15 < dist /\ dist < LENGTH ps.ps_stack ==>
  ?k a b offsets al tail.
    k = dist-15 /\ a = REVERSE (top_n k ps.ps_stack) /\
    b = REVERSE (TAKE (LENGTH ps.ps_stack-k) ps.ps_stack) /\
    offsets = FST (spill_alloc_n [] ps.ps_alloc a) /\
    al = FOLDL (\a off. free_spill_slot off a)
      (SND (spill_alloc_n [] ps.ps_alloc a)) offsets /\
    LENGTH a = k /\ 0 < k /\
    out.ps_spilled = ps.ps_spilled /\ out.ps_alloc = al /\
    out.ps_stack = stack_dup dist ps.ps_stack /\
    tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
      (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
      else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
        (GENLIST (\i. k-1-i) k))) /\
    ops = MAP SOSpill offsets ++ [SODup 16] ++ tail
Proof
  strip_tac >> simp_tac bool_ss [] >> metis_tac[sym_do_dup_big_shape]
QED

Theorem sym_dup_shaped_ready[local]:
  k = dist-15 /\ a = REVERSE (top_n k ps.ps_stack) /\
  b = REVERSE (TAKE (LENGTH ps.ps_stack-k) ps.ps_stack) /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc a) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc a)) offsets /\
  out.ps_alloc = al /\ 15 < dist /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  ops = MAP SOSpill offsets ++ [SODup 16] ++ tail /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  ?vals rest. ss.sym_stack = vals ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) a vals /\ LIST_REL (op_kind_ok fn ret) b rest /\
    REVERSE ps.ps_stack = a ++ b /\ 15 < LENGTH b /\
    EL 15 b = EL dist (REVERSE ps.ps_stack) /\
    LENGTH offsets = LENGTH a /\
    EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets /\
    (!op at. FLOOKUP ps.ps_spilled op = SOME at ==>
      EVERY (\off. off+32 <= at \/ at+32 <= off) offsets) /\
    (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets) /\
    EVERY (\off. off < dimword(:256)) offsets
Proof
  strip_tac >> drule_all_then strip_assume_tac sym_dup_frame_ready >>
  metis_tac[PURE_REWRITE_RULE [APPEND_ASSOC]
    (Q.INST [`tail` |-> `[SODup 16] ++ tail`] sym_swap_geometry)]
QED

Theorem sym_dup_shaped_run[local]:
  LIST_REL (op_kind_ok fn ret) a vals /\
  LENGTH a = k /\ LENGTH offsets = LENGTH a /\ 0 < k /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets+32 <= EL j offsets \/ EL j offsets+32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets /\
  LIST_REL (op_kind_ok fn ret) b rest /\ 15 < LENGTH b /\
  ss.sym_stack = vals ++ (rest ++ srest) /\
  tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
    else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k))) /\
  ops = MAP SOSpill offsets ++ [SODup 16] ++ tail /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last top. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    last.sym_stack = top ++ (rest ++ srest) /\
    LIST_REL (op_kind_ok fn ret) (EL 15 b::a) top /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> gvs[sym_dup_scratch_roundtrip]
QED

Theorem sym_dup_shaped_sim[local]:
  k = dist-15 /\ a = REVERSE (top_n k ps.ps_stack) /\
  b = REVERSE (TAKE (LENGTH ps.ps_stack-k) ps.ps_stack) /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc a) /\
  al = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc a)) offsets /\
  LENGTH a = k /\ 0 < k /\ out.ps_spilled = ps.ps_spilled /\
  out.ps_alloc = al /\ out.ps_stack = stack_dup dist ps.ps_stack /\
  tail = (if k <= 16 then MAP (\j. SORestore (EL j offsets))
    (GENLIST (\i. k-2-i) (k-1) ++ [k-1]) ++ [SOSwap k]
    else FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1])
      (GENLIST (\i. k-1-i) k))) /\
  ops = MAP SOSpill offsets ++ [SODup 16] ++ tail /\
  15 < dist /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
  disch_then (fn th => strip_assume_tac
    (CONJ th (SIMP_RULE bool_ss [] (CONV_RULE
      (LAND_CONV (SIMP_CONV bool_ss (CONJUNCTS th))) sym_dup_shaped_ready)))) >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_dup_shaped_run >>
  drule_all_then MATCH_ACCEPT_TAC sym_dup_scratch_complete
QED

Theorem sym_do_dup_big:
  do_dup dist ps = (ops,out) /\ 15 < dist /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
  strip_tac >> drule_all_then strip_assume_tac sym_dup_shape_witnesses >>
  drule_all_then MATCH_ACCEPT_TAC sym_dup_shaped_sim
QED

Theorem sym_do_dup:
  do_dup dist ps = (ops,out) /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
  strip_tac >> Cases_on `dist <= 15`
  >- (drule_all_then MATCH_ACCEPT_TAC sym_do_dup_small) >>
  `15 < dist` by decide_tac >> drule_all_then MATCH_ACCEPT_TAC sym_do_dup_big
QED
