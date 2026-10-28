(* Physical execution of duplication's restoration schedules.  Values are
   tracked by spill occurrence, allowing repeated values and existing spills.
   TOP-LEVEL: dup_restore_swap_step. *)
Theory doDupSim
Ancestors
  doDupModel deepDupRestore doSwapSim stackOpSim stackOpAsmSim
  asmSem planExec stackPlanOps stackPlanTypes list rich_list arithmetic

Theorem dup_restore_swap_step:
  !lo o2pc st vals top rest.
    0 < LENGTH vals /\ LENGTH vals <= 16 /\
    st.as_stack =
      REVERSE (MAP (\i. EL i vals) (dup_restore_indices (LENGTH vals))) ++
        top::rest ==>
    asm_step lo o2pc (AsmOp (swap_name (LENGTH vals))) st =
      AsmOK (st with <|as_stack := top::(vals ++ rest);
                      as_pc := st.as_pc + 1|>)
Proof
  rpt gen_tac >> strip_tac >>
  `vals <> []` by (Cases_on `vals` >> gvs[]) >>
  mp_tac (Q.SPECL [`lo`,`o2pc`,`LENGTH (vals:bytes32 list)`,`st`]
    asm_step_swap_ok) >>
  (impl_tac >-
    asm_simp_tac (srw_ss()) [dup_restore_indices_length]) >>
  simp[asm_next_def] >> strip_tac >> asm_rewrite_tac [] >>
  mp_tac (Q.ISPECL [`vals:bytes32 list`,`top:bytes32`,`rest:bytes32 list`]
    dup_restore_front_stack) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[LET_THM, asm_state_component_equality]
QED

Theorem asm_block_one_step_ok[local]:
  !lo o2pc prog inst st st'.
    asm_block_at prog st.as_pc [inst] /\
    asm_step lo o2pc inst st = AsmOK st' ==>
    asm_steps lo o2pc prog 1 st = AsmOK st'
Proof
  rpt gen_tac >> strip_tac >> fs[asm_block_at_cons] >>
  rewrite_tac [DECIDE ``1 = SUC 0``, Once asm_steps_def] >>
  `~(st.as_pc >= LENGTH prog)` by decide_tac >>
  asm_rewrite_tac [asm_steps_def] >> simp[]
QED

Theorem dup_restore_swap_steps:
  !lo o2pc prog st vals top rest.
    0 < LENGTH vals /\ LENGTH vals <= 16 /\
    st.as_stack =
      REVERSE (MAP (\i. EL i vals) (dup_restore_indices (LENGTH vals))) ++
        top::rest /\
    asm_block_at prog st.as_pc [AsmOp (swap_name (LENGTH vals))] ==>
    asm_steps lo o2pc prog 1 st =
      AsmOK (st with <|as_stack := top::(vals ++ rest);
                      as_pc := st.as_pc + 1|>)
Proof
  rpt gen_tac >> strip_tac >>
  irule asm_block_one_step_ok >>
  qexists_tac `AsmOp (swap_name (LENGTH (vals:bytes32 list)))` >>
  conj_tac
  >- (irule dup_restore_swap_step >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Theorem dup16_steps:
  !lo o2pc prog st.
    15 < LENGTH st.as_stack /\
    asm_block_at prog st.as_pc [AsmOp "DUP16"] ==>
    asm_steps lo o2pc prog 1 st =
      AsmOK (st with <|as_stack := EL 15 st.as_stack :: st.as_stack;
                      as_pc := st.as_pc + 1|>)
Proof
  rpt gen_tac >> strip_tac >>
  irule asm_block_one_step_ok >> qexists_tac `AsmOp "DUP16"` >>
  conj_tac
  >- (mp_tac (Q.SPECL [`lo`,`o2pc`,`15n`,`st`] asm_step_dup_ok) >>
      asm_simp_tac (srw_ss()) [dup_name_def, asm_next_def]) >>
  first_assum ACCEPT_TAC
QED

Theorem dup_restore_indexed_steps:
  !offsets vals lo o2pc prog st.
    LENGTH offsets = LENGTH vals /\ 0 < LENGTH vals /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!k. k < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL k offsets) st.as_memory)) = EL k vals) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp
        (MAP SORestore (MAP (\i. EL i offsets)
          (dup_restore_indices (LENGTH vals))))) ==>
    asm_steps lo o2pc prog (2 * LENGTH vals) st =
      AsmOK (st with <|
        as_stack :=
          REVERSE (MAP (\i. EL i vals) (dup_restore_indices (LENGTH vals))) ++
            st.as_stack;
        as_memory := FOLDL (\mem off. asm_expand_memory (off + 32) mem)
          st.as_memory
          (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)));
        as_pc := st.as_pc + 2 * LENGTH vals|>)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`offsets`,`vals`,
    `dup_restore_indices (LENGTH (vals:bytes32 list))`,
    `lo`,`o2pc`,`prog`,`st`] raw_restore_indexed_steps) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      asm_simp_tac (srw_ss()) [dup_restore_indices_bound]])) >>
  asm_simp_tac (srw_ss()) [dup_restore_indices_length]
QED

Theorem read_spill_values[local]:
  !offsets vals mem.
    LENGTH offsets = LENGTH vals /\
    (!k. k < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL k offsets) mem)) = EL k vals) ==>
    MAP (\off. word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP off mem))) offsets = vals
Proof
  rpt gen_tac >> strip_tac >> rw[LIST_EQ_REWRITE, EL_MAP] >>
  qpat_x_assum `!k. _` irule >> simp[]
QED

Theorem dup_restore_large_steps:
  !offsets vals lo o2pc prog st top rest.
    LENGTH offsets = LENGTH vals /\ 16 < LENGTH vals /\
    st.as_stack = top::rest /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!k. k < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL k offsets) st.as_memory)) = EL k vals) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp
        (FLAT (MAP (\off. [SORestore off; SOSwap 1])
          (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)))))) ==>
    asm_steps lo o2pc prog (3 * LENGTH vals) st =
      AsmOK (st with <|
        as_stack := top::(vals ++ rest);
        as_memory := FOLDL (\mem off. asm_expand_memory (off + 32) mem)
          st.as_memory
          (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)));
        as_pc := st.as_pc + 3 * LENGTH vals|>)
Proof
  rpt gen_tac >> strip_tac >>
  `~(LENGTH vals <= 16)` by decide_tac >>
  `MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)) =
     REVERSE offsets` by
    (mp_tac (Q.ISPEC `offsets:num list` dup_restore_schedule_map) >>
     asm_simp_tac (srw_ss()) []) >>
  `MAP (\off. word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP off st.as_memory))) offsets = vals` by
    (irule read_spill_values >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[] >>
  mp_tac (Q.SPECL [`REVERSE (offsets:num list)`,`lo`,`o2pc`,`prog`,
    `st`,`top`,`rest`] restore_below_top_steps) >>
  (impl_tac >- asm_simp_tac (srw_ss()) [EVERY_REVERSE]) >>
  asm_simp_tac (srw_ss()) [MAP_REVERSE, asm_state_component_equality, ADD_COMM]
QED

Theorem execute_plan_singleton[local]:
  execute_plan initial_fmp [op] = exec_stack_op initial_fmp op
Proof
  simp[execute_plan_def]
QED

Theorem dup_restore_small_steps:
  !offsets vals lo o2pc prog st top rest.
    LENGTH offsets = LENGTH vals /\ 0 < LENGTH vals /\ LENGTH vals <= 16 /\
    st.as_stack = top::rest /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!k. k < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL k offsets) st.as_memory)) = EL k vals) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp
        (MAP SORestore (MAP (\i. EL i offsets)
          (dup_restore_indices (LENGTH vals))) ++ [SOSwap (LENGTH vals)])) ==>
    asm_steps lo o2pc prog (2 * LENGTH vals + 1) st =
      AsmOK (st with <|
        as_stack := top::(vals ++ rest);
        as_memory := FOLDL (\mem off. asm_expand_memory (off + 32) mem)
          st.as_memory
          (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)));
        as_pc := st.as_pc + 2 * LENGTH vals + 1|>)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `mid = st with <|
    as_stack := REVERSE
      (MAP (\i. EL i vals) (dup_restore_indices (LENGTH vals))) ++ st.as_stack;
    as_memory := FOLDL (\mem off. asm_expand_memory (off + 32) mem)
      st.as_memory (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)));
    as_pc := st.as_pc + 2 * LENGTH vals|>` >>
  `asm_block_at prog st.as_pc
      (execute_plan initial_fmp (MAP SORestore
        (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals))))) /\
   asm_block_at prog (st.as_pc + 2 * LENGTH vals)
      [AsmOp (swap_name (LENGTH vals))]` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     asm_simp_tac (srw_ss()) [execute_plan_append, asm_block_at_append,
       execute_plan_singleton, exec_stack_op_def, execute_plan_map_restore_length,
       dup_restore_indices_length]) >>
  `asm_steps lo o2pc prog (2 * LENGTH vals) st = AsmOK mid` by
    (mp_tac (Q.SPECL [`offsets`,`vals`,`lo`,`o2pc`,`prog`,`st`]
       dup_restore_indexed_steps) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[Abbr `mid`]) >>
  rewrite_tac [asm_steps_add] >> asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`lo`,`o2pc`,`prog`,`mid`,`vals`,`top`,`rest`]
    dup_restore_swap_steps) >>
  (impl_tac >- asm_simp_tac (srw_ss()) [Abbr `mid`]) >>
  simp[Abbr `mid`, asm_state_component_equality]
QED

Theorem flat_restore_map_single[local]:
  !indices offsets.
    FLAT (MAP (\i. [SORestore (EL i offsets)]) indices) =
    MAP SORestore (MAP (\i. EL i offsets) indices)
Proof
  Induct >> simp[]
QED

Theorem flat_restore_swap_map[local]:
  FLAT (MAP (\i. [SORestore (EL i offsets); SOSwap 1]) indices) =
  FLAT (MAP (\off. [SORestore off; SOSwap 1])
    (MAP (\i. EL i offsets) indices))
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem dup_restore_steps:
  !offsets vals lo o2pc prog st top rest.
    LENGTH offsets = LENGTH vals /\ 0 < LENGTH vals /\
    st.as_stack = top::rest /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!k. k < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL k offsets) st.as_memory)) = EL k vals) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp
        (FLAT (MAP (\i. [SORestore (EL i offsets)] ++
            if LENGTH vals <= 16 then [] else [SOSwap 1])
          (dup_restore_indices (LENGTH vals))) ++
         if LENGTH vals <= 16 then [SOSwap (LENGTH vals)] else [])) ==>
    asm_steps lo o2pc prog
      (if LENGTH vals <= 16 then 2 * LENGTH vals + 1 else 3 * LENGTH vals) st =
      AsmOK (st with <|
        as_stack := top::(vals ++ rest);
        as_memory := FOLDL (\mem off. asm_expand_memory (off + 32) mem)
          st.as_memory
          (MAP (\i. EL i offsets) (dup_restore_indices (LENGTH vals)));
        as_pc := st.as_pc +
          (if LENGTH vals <= 16 then 2 * LENGTH vals + 1 else 3 * LENGTH vals)|>)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `LENGTH vals <= 16`
  >- (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
      asm_simp_tac (srw_ss()) [flat_restore_map_single] >> strip_tac >>
      mp_tac (Q.SPECL [`offsets`,`vals`,`lo`,`o2pc`,`prog`,`st`,`top`,`rest`]
        dup_restore_small_steps) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      pure_rewrite_tac [ADD_ASSOC] >> simp_tac bool_ss []) >>
  `16 < LENGTH vals` by decide_tac >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  asm_simp_tac (srw_ss()) [flat_restore_swap_map] >> strip_tac >>
  mp_tac (Q.SPECL [`offsets`,`vals`,`lo`,`o2pc`,`prog`,`st`,`top`,`rest`]
    dup_restore_large_steps) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem dup_restore_code_length:
  !offsets k.
    LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\i. [SORestore (EL i offsets)] ++
          if k <= 16 then [] else [SOSwap 1]) (dup_restore_indices k)) ++
       if k <= 16 then [SOSwap k] else [])) =
    if k <= 16 then 2 * k + 1 else 3 * k
Proof
  rpt gen_tac >> Cases_on `k = 0`
  >- gvs[dup_restore_indices_def, execute_plan_def, exec_stack_op_def] >>
  `0 < k` by decide_tac >>
  `LENGTH (dup_restore_indices k) = k` by simp[dup_restore_indices_length] >>
  Cases_on `k <= 16` >>
  asm_simp_tac (srw_ss()) [flat_restore_map_single, flat_restore_swap_map,
    execute_plan_append, execute_plan_map_restore_length,
    execute_plan_singleton, exec_stack_op_def, restore_below_top_code_length] >>
  simp[execute_plan_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed duplication simulation theorem: " ^ name)
  end) (DB.thms "doDupSim")
