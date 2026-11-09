(* Occurrence-indexed scratch slots: operand equality is immaterial. *)
Theory symPlannerScratch
Ancestors
  symPlannerBase doSwapSim contextCodegenRelProps list rich_list
  asmSymSem asmSem asmToBytecodeProofs codegenSymRel stackOpSim

Definition scratch_kinds_ok_def:
  scratch_kinds_ok fn ret items offsets labs <=>
  LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\ mem_sval_at labs off sv)
    items offsets
End

Theorem scratch_kinds_ok_nil:
  scratch_kinds_ok fn ret [] [] labs
Proof
  simp[scratch_kinds_ok_def]
QED

Theorem scratch_kinds_ok_cons:
  scratch_kinds_ok fn ret (op::items) (off::offsets) labs <=>
  (?sv. op_kind_ok fn ret op sv /\ mem_sval_at labs off sv) /\
  scratch_kinds_ok fn ret items offsets labs
Proof
  simp[scratch_kinds_ok_def]
QED

Theorem scratch_kinds_ok_load:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  k < LENGTH items /\ EL k offsets < dimword(:256) /\
  ss.sym_stack = Val (n2w (EL k offsets)) :: stk ==>
  ?last v. sym_mload ss = SymOK last /\
    last.sym_stack = v :: stk /\ op_kind_ok fn ret (EL k items) v /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rw[scratch_kinds_ok_def, LIST_REL_EL_EQN] >>
  first_x_assum (qspec_then `k` mp_tac) >>
  metis_tac[sym_mload_kind]
QED

Theorem scratch_kinds_ok_two_equal:
  op_kind_ok fn ret op a /\ op_kind_ok fn ret op b /\
  mem_sval_at labs off a /\ mem_sval_at labs at b ==>
  scratch_kinds_ok fn ret [op;op] [off;at] labs
Proof
  simp[scratch_kinds_ok_cons, scratch_kinds_ok_nil] >> metis_tac[]
QED

Theorem scratch_kinds_ok_transport:
  scratch_kinds_ok fn ret items offsets labs /\
  (!off sv. MEM off offsets /\ mem_sval_at labs off sv ==> mem_sval_at labs' off sv) ==>
  scratch_kinds_ok fn ret items offsets labs'
Proof
  rw[scratch_kinds_ok_def, LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < LENGTH items ==> _` (qspec_then `n` mp_tac) >>
  metis_tac[MEM_EL]
QED

Theorem scratch_kinds_ok_save:
  scratch_kinds_ok fn ret items offsets labs /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  (!at sv. (off+32 <= at \/ at+32 <= off) ==>
      (mem_sval_at labs' at sv <=> mem_sval_at labs at sv)) /\
  op_kind_ok fn ret op v /\ mem_sval_at labs' off v ==>
  scratch_kinds_ok fn ret (op::items) (off::offsets) labs'
Proof
  rw[scratch_kinds_ok_cons, EVERY_MEM] >- metis_tac[] >>
  metis_tac[scratch_kinds_ok_transport]
QED

Theorem sym_mstore_scratch_cons:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  op_kind_ok fn ret op v /\
  ss.sym_stack = Val (n2w off) :: v :: stk /\ off < dimword(:256) ==>
  ?last. sym_mstore ss = SymOK last /\ last.sym_stack = stk /\
    scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
    (!i. ~in_mem_range off 32 i ==>
       FLOOKUP last.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i) /\
    (!at sv. (off+32 <= at \/ at+32 <= off) ==>
       (mem_sval_at last.sym_mem_labels at sv <=> mem_sval_at ss.sym_mem_labels at sv)) /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt strip_tac >> drule_all sym_mstore_kind >>
  metis_tac[scratch_kinds_ok_save]
QED

Theorem sym_step_push_bytes:
  sym_step p env (AsmPush bytes) ss =
  SymOK (ss with <| sym_base := (asm_next ss.sym_base) with as_stack := [];
    sym_stack := Val (word_of_bytes F (0w:bytes32) (REVERSE bytes)) :: ss.sym_stack |> )
Proof
  simp[sym_step_def, asmSemTheory.asm_step_def, sym_lift_def,
       asmSemTheory.asm_next_def, sym_state_component_equality]
QED

Theorem sym_push_offset_step:
  off < dimword(:256) ==>
  ?mid. sym_step p env (AsmPush (encode_num_bytes off)) ss = SymOK mid /\
    mid.sym_stack = Val (n2w off) :: ss.sym_stack /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[sym_step_push_bytes, raw_spill_push_encode_num_roundtrip, asm_next_def]
QED

Theorem sym_steps_push_memory:
  asm_block_at p ss.sym_base.as_pc [AsmPush bytes; AsmOp name] /\
  sym_step p env (AsmPush bytes) ss = SymOK mid /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
  sym_step_op p env name mid = SymOK last ==>
  sym_steps p env 2 ss = SymOK last
Proof
  strip_tac >> fs[asm_block_at_cons, sym_step_def] >>
  simp[codegenSymRelTheory.sym_steps_compute, sym_step_def]
QED


Definition scratch_push_state_def:
  scratch_push_state off ss = ss with
    <| sym_base := (asm_next ss.sym_base) with as_stack := [];
       sym_stack := Val (n2w off) :: ss.sym_stack |>
End

Theorem scratch_push_state_projections[simp]:
  (scratch_push_state off ss).sym_stack = Val (n2w off) :: ss.sym_stack /\
  (scratch_push_state off ss).sym_mem_labels = ss.sym_mem_labels /\
  (scratch_push_state off ss).sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[scratch_push_state_def, asm_next_def]
QED

Theorem sym_step_scratch_push:
  off < dimword(:256) ==>
  sym_step p env (AsmPush (encode_num_bytes off)) ss =
    SymOK (scratch_push_state off ss)
Proof
  simp[sym_step_push_bytes, scratch_push_state_def, raw_spill_push_encode_num_roundtrip]
QED

Theorem sym_steps_scratch_store:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSpill off]) /\
  sym_mstore (scratch_push_state off ss) = SymOK last ==>
  sym_steps p env 2 ss = SymOK last
Proof
  rw[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
  drule sym_steps_push_memory >>
  simp[sym_step_scratch_push, sym_step_op_def, scratch_push_state_projections]
QED

Theorem sym_steps_scratch_load:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SORestore off]) /\
  sym_mload (scratch_push_state off ss) = SymOK last ==>
  sym_steps p env 2 ss = SymOK last
Proof
  rw[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
  drule sym_steps_push_memory >>
  simp[sym_step_scratch_push, sym_step_op_def, scratch_push_state_projections]
QED

Theorem sym_scratch_store_post:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSpill off]) ==>
  ((?last. sym_mstore (scratch_push_state off ss) = SymOK last /\ P last) ==>
   ?last. sym_steps p env 2 ss = SymOK last /\ P last)
Proof
  rpt strip_tac >> qexists_tac `last` >> metis_tac[sym_steps_scratch_store]
QED


Theorem sym_result_case_identity[local]:
  (case result of SymOK s => SymOK s | SymHalt s => SymHalt s
   | SymRevert s => SymRevert s | SymFault s => SymFault s
   | SymError e => SymError e | SymBad e => SymBad e) = result
Proof
  Cases_on `result` >> simp[]
QED

Theorem sym_steps_scratch_store_eq:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSpill off]) ==>
  sym_steps p env 2 ss = sym_mstore (scratch_push_state off ss)
Proof
  rw[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def,
     asm_block_at_cons] >>
  simp[codegenSymRelTheory.sym_steps_compute, sym_step_scratch_push] >>
  simp[sym_step_def, sym_step_op_def, sym_result_case_identity]
QED

Theorem sym_steps_scratch_load_eq:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SORestore off]) ==>
  sym_steps p env 2 ss = sym_mload (scratch_push_state off ss)
Proof
  rw[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def,
     asm_block_at_cons] >>
  simp[codegenSymRelTheory.sym_steps_compute, sym_step_scratch_push] >>
  simp[sym_step_def, sym_step_op_def, sym_result_case_identity]
QED

Theorem sym_mstore_scratch_push_cons[local]:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  op_kind_ok fn ret op v /\ ss.sym_stack = v :: stk /\
  off < dimword(:256) ==>
  ?last. sym_mstore (scratch_push_state off ss) = SymOK last /\
    last.sym_stack = stk /\
    scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
    (!i. ~in_mem_range off 32 i ==>
       FLOOKUP last.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i) /\
    (!at sv. (off+32 <= at \/ at+32 <= off) ==>
       (mem_sval_at last.sym_mem_labels at sv <=> mem_sval_at ss.sym_mem_labels at sv)) /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  mp_tac (Q.INST [`ss` |-> `scratch_push_state off ss`] sym_mstore_scratch_cons) >>
  simp[arithmeticTheory.ADD_ASSOC]
QED

Theorem sym_spill_scratch_cons:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  op_kind_ok fn ret op v /\ ss.sym_stack = v :: stk /\
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSpill off]) ==>
  ?last. sym_steps p env 2 ss = SymOK last /\ last.sym_stack = stk /\
    scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
    (!i. ~in_mem_range off 32 i ==>
       FLOOKUP last.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i) /\
    (!at sv. (off+32 <= at \/ at+32 <= off) ==>
       (mem_sval_at last.sym_mem_labels at sv <=> mem_sval_at ss.sym_mem_labels at sv)) /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >> drule_all sym_steps_scratch_store_eq >>
  simp[sym_mstore_scratch_push_cons]
QED
Theorem sym_mload_scratch_push_index[local]:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  k < LENGTH items /\ EL k offsets < dimword(:256) /\ ss.sym_stack = stk ==>
  ?last v. sym_mload (scratch_push_state (EL k offsets) ss) = SymOK last /\
    last.sym_stack = v :: stk /\ op_kind_ok fn ret (EL k items) v /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  mp_tac (Q.INST [`ss` |-> `scratch_push_state (EL k offsets) ss`]
    scratch_kinds_ok_load) >> simp[arithmeticTheory.ADD_ASSOC]
QED

Theorem sym_restore_scratch_index:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  k < LENGTH items /\ EL k offsets < dimword(:256) /\ ss.sym_stack = stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp [SORestore (EL k offsets)]) ==>
  ?last v. sym_steps p env 2 ss = SymOK last /\
    last.sym_stack = v :: stk /\ op_kind_ok fn ret (EL k items) v /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >> drule_all sym_steps_scratch_load_eq >>
  simp[sym_mload_scratch_push_index]
QED

Theorem scratch_write_region_frame:
  r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
  (!i. ~in_mem_range off 32 i ==> FLOOKUP labs' i = FLOOKUP labs i) ==>
  !i. ~(r.sr_spill_base <= i /\ i < r.sr_spill_end) ==>
    FLOOKUP labs' i = FLOOKUP labs i
Proof
  rw[in_mem_range_def] >> first_x_assum irule >> decide_tac
QED

Theorem scratch_write_durable_kinds:
  (!op at. FLOOKUP spilled op = SOME at ==>
    ?v. op_kind_ok fn ret op v /\ mem_sval_at labs at v) /\
  (!op at. FLOOKUP spilled op = SOME at ==> off+32 <= at \/ at+32 <= off) /\
  (!at v. (off+32 <= at \/ at+32 <= off) ==>
    (mem_sval_at labs' at v <=> mem_sval_at labs at v)) ==>
  !op at. FLOOKUP spilled op = SOME at ==>
    ?v. op_kind_ok fn ret op v /\ mem_sval_at labs' at v
Proof
  metis_tac[]
QED

Theorem scratch_region_context_transport:
  MEM r cplan.cp_regions /\
  (!i. ~(r.sr_spill_base <= i /\ i < r.sr_spill_end) ==>
    FLOOKUP labs' i = FLOOKUP labs i) /\
  (!i. i IN FDOM labs ==> context_spill_byte cplan i) ==>
  !i. i IN FDOM labs' ==> context_spill_byte cplan i
Proof
  rpt strip_tac >> Cases_on `r.sr_spill_base <= i /\ i < r.sr_spill_end` >>
  metis_tac[context_spill_byte_of_region, finite_mapTheory.FLOOKUP_DEF,
            optionTheory.NOT_SOME_NONE]
QED

Definition scratch_frame_def:
  scratch_frame offsets labs labs' <=>
  (!i. EVERY (\off. ~in_mem_range off 32 i) offsets ==>
    FLOOKUP labs' i = FLOOKUP labs i) /\
  (!at sv. EVERY (\off. off+32 <= at \/ at+32 <= off) offsets ==>
    (mem_sval_at labs' at sv <=> mem_sval_at labs at sv))
End

Theorem scratch_frame_refl:
  scratch_frame offsets labs labs
Proof
  simp[scratch_frame_def]
QED

Theorem scratch_frame_singleton:
  scratch_frame [off] labs labs' <=>
  (!i. ~in_mem_range off 32 i ==> FLOOKUP labs' i = FLOOKUP labs i) /\
  (!at sv. (off+32 <= at \/ at+32 <= off) ==>
    (mem_sval_at labs' at sv <=> mem_sval_at labs at sv))
Proof
  simp[scratch_frame_def]
QED

Theorem scratch_frame_append:
  scratch_frame xs a b /\ scratch_frame ys b c ==>
  scratch_frame (xs ++ ys) a c
Proof
  rw[scratch_frame_def, EVERY_APPEND] >> metis_tac[]
QED

Theorem scratch_frame_cons:
  scratch_frame [off] a b /\ scratch_frame offsets b c ==>
  scratch_frame (off::offsets) a c
Proof
  metis_tac[scratch_frame_append, listTheory.APPEND]
QED

Theorem scratch_frame_cell:
  scratch_frame offsets labs labs' /\
  EVERY (\off. off+32 <= at \/ at+32 <= off) offsets ==>
  (mem_sval_at labs' at sv <=> mem_sval_at labs at sv)
Proof
  simp[scratch_frame_def]
QED

Theorem scratch_frame_kinds:
  scratch_frame written labs labs' /\ scratch_kinds_ok fn ret items offsets labs /\
  EVERY (\at. EVERY (\off. off+32 <= at \/ at+32 <= off) written) offsets ==>
  scratch_kinds_ok fn ret items offsets labs'
Proof
  rw[scratch_frame_def, EVERY_MEM] >>
  metis_tac[scratch_kinds_ok_transport]
QED

Theorem scratch_slot_inside_region:
  r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end /\
  in_mem_range off 32 i ==>
  r.sr_spill_base <= i /\ i < r.sr_spill_end
Proof
  simp[in_mem_range_def] >> decide_tac
QED

Theorem scratch_frame_region:
  scratch_frame offsets labs labs' /\
  EVERY (\off. r.sr_spill_base <= off /\ off+32 <= r.sr_spill_end) offsets ==>
  !i. ~(r.sr_spill_base <= i /\ i < r.sr_spill_end) ==>
    FLOOKUP labs' i = FLOOKUP labs i
Proof
  rw[scratch_frame_def, EVERY_MEM] >>
  first_x_assum irule >> metis_tac[scratch_slot_inside_region]
QED

Theorem sym_spill_scratch_head:
  op_kind_ok fn ret op v /\ ss.sym_stack = v::stk /\ off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOSpill off]) ==>
  ?last. sym_steps p env 2 ss = SymOK last /\ last.sym_stack = stk /\
    scratch_kinds_ok fn ret [op] [off] last.sym_mem_labels /\
    scratch_frame [off] ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  mp_tac (Q.INST [`items` |-> `[]`, `offsets` |-> `[]`] sym_spill_scratch_cons) >>
  simp[scratch_kinds_ok_nil, scratch_frame_singleton] >> metis_tac[]
QED

Theorem scratch_save_cons_post[local]:
  scratch_kinds_ok fn ret [op] [off] middle /\
  scratch_frame [off] before middle /\
  scratch_kinds_ok fn ret items offsets after /\
  scratch_frame offsets middle after /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets ==>
  scratch_kinds_ok fn ret (op::items) (off::offsets) after /\
  scratch_frame (off::offsets) before after
Proof
  rw[scratch_kinds_ok_cons, scratch_kinds_ok_nil, scratch_frame_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem execute_plan_spill_cons[local]:
  execute_plan initial_fmp (MAP SOSpill (off::offsets)) =
  execute_plan initial_fmp [SOSpill off] ++
  execute_plan initial_fmp (MAP SOSpill offsets)
Proof
  simp[planExecTheory.execute_plan_def]
QED

Theorem execute_plan_spill_length[local]:
  LENGTH (execute_plan initial_fmp [SOSpill off]) = 2
Proof
  simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

Theorem sym_steps_spill_cons_compose[local]:
  sym_steps p env 2 ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) mid =
    SymOK last ==>
  sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))) ss =
    SymOK last
Proof
  strip_tac >>
  pure_rewrite_tac[Once execute_plan_spill_cons, LENGTH_APPEND, execute_plan_spill_length] >>
  metis_tac[sym_steps_compose_ok]
QED

Theorem execute_plan_spill_cons_length[local]:
  LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets))) =
  2 + LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))
Proof
  pure_rewrite_tac[Once execute_plan_spill_cons, LENGTH_APPEND, execute_plan_spill_length] >>
  simp[]
QED

Theorem scratch_save_cons_runs[local]:
  sym_steps p env 2 ss = SymOK mid /\
  scratch_kinds_ok fn ret [op] [off] mid.sym_mem_labels /\
  scratch_frame [off] ss.sym_mem_labels mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) mid =
    SymOK last /\
  scratch_kinds_ok fn ret items offsets last.sym_mem_labels /\
  scratch_frame offsets mid.sym_mem_labels last.sym_mem_labels /\
  last.sym_base.as_pc = mid.sym_base.as_pc +
    LENGTH (execute_plan initial_fmp (MAP SOSpill offsets)) /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets ==>
  sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))) ss =
    SymOK last /\
  scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
  scratch_frame (off::offsets) ss.sym_mem_labels last.sym_mem_labels /\
  last.sym_base.as_pc = ss.sym_base.as_pc +
    LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))
Proof
  strip_tac >> drule_all_then strip_assume_tac scratch_save_cons_post >>
  metis_tac[sym_steps_spill_cons_compose, execute_plan_spill_cons_length,
            arithmeticTheory.ADD_ASSOC]
QED

Theorem scratch_save_cons_finish[local]:
  sym_steps p env 2 ss = SymOK mid /\
  scratch_kinds_ok fn ret [op] [off] mid.sym_mem_labels /\
  scratch_frame [off] ss.sym_mem_labels mid.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  (?last. sym_steps p env (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) mid =
    SymOK last /\ last.sym_stack = stk /\
    scratch_kinds_ok fn ret items offsets last.sym_mem_labels /\
    scratch_frame offsets mid.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = mid.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) ==>
  ?last. sym_steps p env
    (LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))) ss = SymOK last /\
    last.sym_stack = stk /\
    scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
    scratch_frame (off::offsets) ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))
Proof
  rpt strip_tac >> qexists_tac `last` >> metis_tac[scratch_save_cons_runs]
QED


Theorem execute_plan_restore_cons[local]:
  execute_plan f (SORestore off::ops) =
  execute_plan f [SORestore off] ++ execute_plan f ops
Proof
  simp[planExecTheory.execute_plan_def]
QED

Theorem execute_plan_restore_length[local]:
  LENGTH (execute_plan f [SORestore off]) = 2
Proof
  simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

Theorem execute_plan_restore_cons_length[local]:
  LENGTH (execute_plan f (SORestore off::ops)) =
  2 + LENGTH (execute_plan f ops)
Proof
  pure_rewrite_tac[Once execute_plan_restore_cons, LENGTH_APPEND,
                   execute_plan_restore_length] >> simp[]
QED

Theorem sym_steps_restore_cons_compose[local]:
  sym_steps p env 2 ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan f ops)) mid = SymOK last ==>
  sym_steps p env (LENGTH (execute_plan f (SORestore off::ops))) ss = SymOK last
Proof
  strip_tac >> pure_rewrite_tac[execute_plan_restore_cons_length] >>
  metis_tac[sym_steps_compose_ok]
QED

Theorem scratch_restore_cons_post[local]:
  last.sym_stack = top ++ (v::stk) /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\k. EL k items) indices)) top /\
  op_kind_ok fn ret (EL k items) v ==>
  last.sym_stack = (top ++ [v]) ++ stk /\
  LIST_REL (op_kind_ok fn ret)
    (REVERSE (MAP (\k. EL k items) (k::indices))) (top ++ [v])
Proof
  simp[LIST_REL_APPEND, APPEND_ASSOC]
QED


Theorem scratch_restore_cons_runs[local]:
  sym_steps p env 2 ss = SymOK mid /\
  op_kind_ok fn ret (EL k items) v /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  sym_steps p env
    (LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) indices))) mid = SymOK last /\
  last.sym_stack = top ++ (v::stk) /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) indices)) top /\
  last.sym_mem_labels = mid.sym_mem_labels /\
  last.sym_base.as_pc = mid.sym_base.as_pc +
    LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) indices)) ==>
  ?out vals. sym_steps p env
    (LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) (k::indices)))) ss = SymOK out /\
    out.sym_stack = vals ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) (k::indices))) vals /\
    out.sym_mem_labels = ss.sym_mem_labels /\
    out.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) (k::indices)))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac scratch_restore_cons_post >>
  drule_all_then assume_tac sym_steps_restore_cons_compose >>
  qexistsl_tac [`last`, `top ++ [v]`] >>
  conj_tac >- (pure_rewrite_tac[listTheory.MAP] >> simp[]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  pure_rewrite_tac[listTheory.MAP] >> BETA_TAC >>
  asm_rewrite_tac[execute_plan_restore_cons_length, arithmeticTheory.ADD_ASSOC]
QED

Theorem asm_block_at_restore_cons[local]:
  asm_block_at p pc (execute_plan f (SORestore off::ops)) ==>
  asm_block_at p pc (execute_plan f [SORestore off]) /\
  asm_block_at p (pc+2) (execute_plan f ops)
Proof
  pure_rewrite_tac[Once execute_plan_restore_cons,
    stackOpSimTheory.asm_block_at_append, execute_plan_restore_length] >> simp[]
QED

Theorem scratch_restore_cons_step[local]:
  (!ss stk. scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
    ss.sym_stack = stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan f (MAP (\j. SORestore (EL j offsets)) indices)) ==>
    ?last top. sym_steps p env
      (LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) indices))) ss = SymOK last /\
      last.sym_stack = top ++ stk /\
      LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) indices)) top /\
      last.sym_mem_labels = ss.sym_mem_labels /\
      last.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) indices))) /\
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  k < LENGTH items /\ EL k offsets < dimword(:256) /\ ss.sym_stack = stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan f (MAP (\j. SORestore (EL j offsets)) (k::indices))) ==>
  ?last top. sym_steps p env
    (LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) (k::indices)))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\j. EL j items) (k::indices))) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan f (MAP (\j. SORestore (EL j offsets)) (k::indices)))
Proof
  strip_tac >>
  qpat_x_assum `asm_block_at _ _ _` (mp_tac o SIMP_RULE (srw_ss()) []) >>
  disch_then (strip_assume_tac o MATCH_MP asm_block_at_restore_cons) >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_restore_scratch_index >>
  rename1 `sym_steps p env 2 ss = SymOK mid` >>
  qpat_x_assum `!ss stk. _` (qspecl_then [`mid`, `mid.sym_stack`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  strip_tac >> simp[scratch_restore_cons_runs]
QED

Theorem sym_restore_scratch_list:
  !indices ss stk.
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\k. k < LENGTH items /\ EL k offsets < dimword(:256)) indices /\
  ss.sym_stack = stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets)) indices)) ==>
  ?last top. sym_steps p env
    (LENGTH (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets)) indices))) ss = SymOK last /\
    last.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\k. EL k items) indices)) top /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP (\k. SORestore (EL k offsets)) indices))
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`ss`, `[]`] >>
      simp[planExecTheory.execute_plan_def, sym_steps_def]) >>
  rpt strip_tac >> irule scratch_restore_cons_step >>
  gvs[listTheory.EVERY_DEF]
QED

Theorem scratch_save_cons_step[local]:
  (!ss. ss.sym_stack = vals ++ stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SOSpill offsets)) ==>
    ?last. sym_steps p env
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) ss = SymOK last /\
      last.sym_stack = stk /\
      scratch_kinds_ok fn ret items offsets last.sym_mem_labels /\
      scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
      last.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) /\
  op_kind_ok fn ret op v /\ ss.sym_stack = v::(vals ++ stk) /\
  off < dimword(:256) /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (MAP SOSpill (off::offsets))) ==>
  ?last. sym_steps p env
    (LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))) ss = SymOK last /\
    last.sym_stack = stk /\
    scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
    scratch_frame (off::offsets) ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP SOSpill (off::offsets)))
Proof
  strip_tac >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[Once execute_plan_spill_cons,
    stackOpSimTheory.asm_block_at_append, execute_plan_spill_length] >>
  strip_tac >>
  drule_all_then (qspec_then `env` strip_assume_tac) sym_spill_scratch_head >>
  rename1 `sym_steps p env 2 ss = SymOK mid` >>
  qpat_x_assum `!ss. _` (qspec_then `mid` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_tac >> drule_all scratch_save_cons_finish >> simp[]
QED

Theorem scratch_separation_head[local]:
  (!i j. i < LENGTH ((off:num)::offsets) /\ j < LENGTH (off::offsets) /\ i <> j ==>
    EL i (off::offsets) + 32 <= EL j (off::offsets) \/
    EL j (off::offsets) + 32 <= EL i (off::offsets)) ==>
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets
Proof
  strip_tac >> rewrite_tac[listTheory.EVERY_EL] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

Theorem scratch_separation_tail[local]:
  (!i j. i < LENGTH ((off:num)::offsets) /\ j < LENGTH (off::offsets) /\ i <> j ==>
    EL i (off::offsets) + 32 <= EL j (off::offsets) \/
    EL j (off::offsets) + 32 <= EL i (off::offsets)) ==>
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets)
Proof
  rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

Theorem sym_spill_scratch_list:
  !offsets items vals ss stk.
  LIST_REL (op_kind_ok fn ret) items vals /\
  LENGTH offsets = LENGTH items /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  EVERY (\off. off < dimword(:256)) offsets /\
  ss.sym_stack = vals ++ stk /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (MAP SOSpill offsets)) ==>
  ?last. sym_steps p env
    (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))) ss = SymOK last /\
    last.sym_stack = stk /\
    scratch_kinds_ok fn ret items offsets last.sym_mem_labels /\
    scratch_frame offsets ss.sym_mem_labels last.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (MAP SOSpill offsets))
Proof
  Induct
  >- (rw[] >>
      gvs[planExecTheory.execute_plan_def, sym_steps_def,
          scratch_kinds_ok_nil, scratch_frame_refl]) >>
  Cases_on `items` >- simp[] >>
  Cases_on `vals` >- simp[] >>
  rpt strip_tac >>
  rename1 `MAP SOSpill (off::offsets)` >>
  `EVERY (\at. off+32 <= at \/ at+32 <= off) offsets` by
    (irule scratch_separation_head >> asm_rewrite_tac[]) >>
  `!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets` by
    (metis_tac[scratch_separation_tail]) >>
  irule scratch_save_cons_step >>
  asm_rewrite_tac[listTheory.EVERY_DEF] >>
  gvs[]
QED
