(* Physical spill-occurrence simulation for deep duplication.  Stack words
   may repeat; no operand ownership map is used in these execution lemmas.
   TOP-LEVEL: spill_dup16_steps. *)
Theory doDupRaw
Ancestors
  doDupSim doSwapSim stackOpSim stackOpAsmSim asmSem planExec
  stackPlanTypes list rich_list arithmetic

Theorem execute_plan_singleton[local]:
  execute_plan initial_fmp [op] = exec_stack_op initial_fmp op
Proof
  simp[execute_plan_def]
QED

Theorem spill_dup16_steps:
  !offsets lo o2pc prog st.
    LENGTH offsets + 15 < LENGTH st.as_stack /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/
      EL j offsets + 32 <= EL i offsets) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (MAP SOSpill offsets ++ [SODup 16])) ==>
    let vals = TAKE (LENGTH offsets) st.as_stack;
        spill_mem = FOLDL (\mem p. mem_write32 (FST p) (SND p) mem)
          st.as_memory (ZIP (offsets, vals));
        remaining = DROP (LENGTH offsets) st.as_stack
    in asm_steps lo o2pc prog (2 * LENGTH offsets + 1) st =
         AsmOK (st with <|
           as_stack := EL 15 remaining :: remaining;
           as_memory := spill_mem;
           as_pc := st.as_pc + 2 * LENGTH offsets + 1|>) /\
       (!k. k < LENGTH offsets ==>
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (EL k offsets) spill_mem)) = EL k vals)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  `LENGTH offsets <= LENGTH st.as_stack` by decide_tac >>
  `15 < LENGTH st.as_stack - LENGTH offsets` by decide_tac >>
  qabbrev_tac `spill_mem =
    FOLDL (\mem p. mem_write32 (FST p) (SND p) mem)
      st.as_memory (ZIP (offsets, TAKE (LENGTH offsets) st.as_stack))` >>
  qabbrev_tac `mid = st with <|
    as_stack := DROP (LENGTH offsets) st.as_stack;
    as_memory := spill_mem; as_pc := st.as_pc + 2 * LENGTH offsets|>` >>
  `asm_block_at prog st.as_pc
      (execute_plan initial_fmp (MAP SOSpill offsets)) /\
   asm_block_at prog (st.as_pc + 2 * LENGTH offsets) [AsmOp "DUP16"]` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     simp[execute_plan_append, asm_block_at_append,
       execute_plan_map_spill_length, execute_plan_singleton,
       exec_stack_op_def, dup_name_def]) >>
  `asm_steps lo o2pc prog (2 * LENGTH offsets) st = AsmOK mid /\
   (!k. k < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL k offsets) spill_mem)) =
      EL k (TAKE (LENGTH offsets) st.as_stack))` by
    (mp_tac (Q.SPECL [`offsets`,
       `TAKE (LENGTH (offsets:num list)) st.as_stack`,
       `lo`,`o2pc`,`prog`,`st`] raw_spill_occurrence_sim) >>
     (impl_tac >- asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ]) >>
     simp[LET_THM, Abbr `mid`, Abbr `spill_mem`]) >>
  conj_tac
  >- (rewrite_tac [asm_steps_add] >> asm_rewrite_tac [] >>
      mp_tac (Q.SPECL [`lo`,`o2pc`,`prog`,`mid`] dup16_steps) >>
      (impl_tac >- asm_simp_tac (srw_ss()) [Abbr `mid`]) >>
      simp[Abbr `mid`, asm_state_component_equality]) >>
  first_assum ACCEPT_TAC
QED

Theorem spill_dup16_code_length[local]:
  LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++ [SODup 16])) =
  2 * LENGTH offsets + 1
Proof
  simp[execute_plan_append, execute_plan_map_spill_length,
       execute_plan_singleton, exec_stack_op_def]
QED

Theorem asm_block_at_plan_append[local]:
  asm_block_at prog pc (execute_plan initial_fmp (ops1 ++ ops2)) <=>
  asm_block_at prog pc (execute_plan initial_fmp ops1) /\
  asm_block_at prog (pc + LENGTH (execute_plan initial_fmp ops1))
    (execute_plan initial_fmp ops2)
Proof
  simp[execute_plan_append, asm_block_at_append]
QED

Theorem el_after_spill_prefix[local]:
  !xs k. k + 15 < LENGTH xs ==>
    EL 15 (DROP k xs) = EL (k + 15) xs
Proof
  rpt gen_tac >> strip_tac >> `15 + k < LENGTH xs` by decide_tac >>
  simp[EL_DROP, ADD_COMM]
QED

Theorem add_middle_one[local]:
  !x y:num. x + 1 + y = x + y + 1
Proof
  rpt gen_tac >> decide_tac
QED

Theorem deep_dup_raw_steps:
  !offsets lo o2pc prog st.
    let k = LENGTH offsets;
        vals = TAKE k st.as_stack;
        spill_mem = FOLDL (\mem p. mem_write32 (FST p) (SND p) mem)
          st.as_memory (ZIP (offsets,vals));
        restore_offsets = MAP (\i. EL i offsets) (dup_restore_indices k)
    in 0 < k /\ k + 15 < LENGTH st.as_stack /\
      EVERY (\off. off < dimword(:256)) offsets /\
      (!i j. i < k /\ j < k /\ i <> j ==>
        EL i offsets + 32 <= EL j offsets \/
        EL j offsets + 32 <= EL i offsets) /\
      asm_block_at prog st.as_pc
        (execute_plan initial_fmp
          ((MAP SOSpill offsets ++ [SODup 16]) ++
           (FLAT (MAP (\i. [SORestore (EL i offsets)] ++
               if k <= 16 then [] else [SOSwap 1]) (dup_restore_indices k)) ++
            if k <= 16 then [SOSwap k] else []))) ==>
      asm_steps lo o2pc prog
        ((2 * k + 1) + (if k <= 16 then 2 * k + 1 else 3 * k)) st =
      AsmOK (st with <|
        as_stack := EL (k + 15) st.as_stack :: st.as_stack;
        as_memory := FOLDL (\mem off. asm_expand_memory (off + 32) mem)
          spill_mem restore_offsets;
        as_pc := st.as_pc + 2 * k + 1 +
          (if k <= 16 then 2 * k + 1 else 3 * k)|>)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `LENGTH offsets <= LENGTH st.as_stack` by decide_tac >>
  `LENGTH (TAKE (LENGTH offsets) st.as_stack) = LENGTH offsets` by
    simp[LENGTH_TAKE_EQ] >>
  qabbrev_tac `spill_mem =
    FOLDL (\mem p. mem_write32 (FST p) (SND p) mem)
      st.as_memory (ZIP (offsets, TAKE (LENGTH offsets) st.as_stack))` >>
  qabbrev_tac `mid = st with <|
    as_stack := EL 15 (DROP (LENGTH offsets) st.as_stack) ::
      DROP (LENGTH offsets) st.as_stack;
    as_memory := spill_mem; as_pc := st.as_pc + 2 * LENGTH offsets + 1|>` >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  once_rewrite_tac [asm_block_at_plan_append] >>
  simp_tac std_ss [spill_dup16_code_length] >> strip_tac >>
  `asm_steps lo o2pc prog (2 * LENGTH offsets + 1) st = AsmOK mid /\
   (!j. j < LENGTH offsets ==>
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (EL j offsets) spill_mem)) =
      EL j (TAKE (LENGTH offsets) st.as_stack))` by
    (mp_tac (Q.SPECL [`offsets`,`lo`,`o2pc`,`prog`,`st`] spill_dup16_steps) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[LET_THM, Abbr `mid`, Abbr `spill_mem`]) >>
  once_rewrite_tac [asm_steps_add] >> asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`offsets`,
    `TAKE (LENGTH (offsets:num list)) st.as_stack`,
    `lo`,`o2pc`,`prog`,`mid`,
    `EL 15 (DROP (LENGTH (offsets:num list)) st.as_stack)`,
    `DROP (LENGTH (offsets:num list)) st.as_stack`] dup_restore_steps) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [Abbr `mid`, LENGTH_TAKE_EQ] >>
    qpat_x_assum `asm_block_at prog (st.as_pc + _) _` mp_tac >>
    pure_rewrite_tac [APPEND, ADD_ASSOC] >> simp_tac bool_ss [])) >>
  pure_rewrite_tac [ADD_ASSOC] >>
  asm_simp_tac (srw_ss()) [Abbr `mid`, LENGTH_TAKE_EQ,
    TAKE_DROP, el_after_spill_prefix, asm_state_component_equality]
QED

Theorem deep_dup_raw_code_length:
  !offsets.
    LENGTH (execute_plan initial_fmp
      ((MAP SOSpill offsets ++ [SODup 16]) ++
       (FLAT (MAP (\i. [SORestore (EL i offsets)] ++
           if LENGTH offsets <= 16 then [] else [SOSwap 1])
         (dup_restore_indices (LENGTH offsets))) ++
        if LENGTH offsets <= 16 then [SOSwap (LENGTH offsets)] else []))) =
    (2 * LENGTH offsets + 1) +
      (if LENGTH offsets <= 16 then 2 * LENGTH offsets + 1
       else 3 * LENGTH offsets)
Proof
  gen_tac >> once_rewrite_tac [execute_plan_append] >>
  simp_tac std_ss [LENGTH_APPEND, spill_dup16_code_length, dup_restore_code_length]
QED

Theorem do_dup_spill_word_bounds:
  !dist ps lo.
    15 < dist /\ dist < LENGTH ps.ps_stack /\
    prefix_spill_wf initial_fmp lo (FST (do_dup dist ps)) ps ==>
    EVERY (\off. off < dimword(:256))
      (FST (spill_alloc_n [] ps.ps_alloc
        (TAKE (dist - 15) (REVERSE ps.ps_stack))))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`] do_dup_big_decompose) >>
  (impl_tac >- decide_tac) >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `prefix_spill_wf initial_fmp lo _ ps` mp_tac >>
  asm_rewrite_tac [] >> simp[prefix_spill_wf_append] >> strip_tac >>
  mp_tac (Q.SPECL
    [`FST (spill_alloc_n [] ps.ps_alloc
       (TAKE (dist - 15) (REVERSE ps.ps_stack)))`,`lo`,`ps`]
    prefix_spill_wf_map_spill_bounds) >> asm_simp_tac std_ss []
QED

Theorem spill_alloc_n_offsets_separated[local]:
  !items al spilled.
    spill_alloc_layout_wf al spilled /\
    EVERY (\off. off < dimword(:256)) (FST (spill_alloc_n [] al items)) ==>
    let offsets = FST (spill_alloc_n [] al items)
    in !i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/
      EL j offsets + 32 <= EL i offsets
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  mp_tac (Q.SPECL [`items`,`al`,`spilled`] spill_alloc_n_slot_facts) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac std_ss [LET_THM] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!k. _` (qspec_then `j` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!j. j < _ /\ j <> _ ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem do_dup_deep_ops:
  !dist ps.
    15 < dist /\ dist < LENGTH ps.ps_stack ==>
    let items = TAKE (dist - 15) (REVERSE ps.ps_stack);
        offsets = FST (spill_alloc_n [] ps.ps_alloc items)
    in FST (do_dup dist ps) =
      ((MAP SOSpill offsets ++ [SODup 16]) ++
       (FLAT (MAP (\i. [SORestore (EL i offsets)] ++
           if LENGTH offsets <= 16 then [] else [SOSwap 1])
         (dup_restore_indices (LENGTH offsets))) ++
        if LENGTH offsets <= 16 then [SOSwap (LENGTH offsets)] else []))
Proof
  rpt gen_tac >> strip_tac >>
  `dist - 15 <= LENGTH ps.ps_stack` by decide_tac >>
  `dist <= 15 + LENGTH ps.ps_stack` by decide_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`] do_dup_big_decompose) >>
  (impl_tac >- decide_tac) >> simp_tac std_ss [LET_THM] >> strip_tac >>
  asm_simp_tac (srw_ss()) [LET_THM, spill_alloc_n_offsets_length,
    LENGTH_TAKE_EQ, APPEND_ASSOC]
QED

Theorem do_dup_deep_alloc:
  !dist ps.
    15 < dist /\ dist < LENGTH ps.ps_stack ==>
    (SND (do_dup dist ps)).ps_alloc =
    let items = TAKE (dist - 15) (REVERSE ps.ps_stack);
        offsets = FST (spill_alloc_n [] ps.ps_alloc items)
    in FOLDL (\a off. free_spill_slot off a)
      (SND (spill_alloc_n [] ps.ps_alloc items)) offsets
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`] do_dup_big_decompose) >>
  (impl_tac >- decide_tac) >> simp_tac std_ss [LET_THM] >> strip_tac >>
  asm_simp_tac (srw_ss()) [LET_THM]
QED

Theorem do_dup_deep_execution:
  !dist ps ops ps' lo o2pc prog st.
    let k = dist - 15;
        items = TAKE k (REVERSE ps.ps_stack);
        offsets = FST (spill_alloc_n [] ps.ps_alloc items);
        written = FOLDL (\m p. mem_write32 (FST p) (SND p) m)
          st.as_memory (ZIP (offsets,TAKE k st.as_stack));
        restore_offsets = MAP (\i. EL i offsets) (dup_restore_indices k)
    in 15 < dist /\ dist < LENGTH ps.ps_stack /\
      LENGTH ps.ps_stack = LENGTH st.as_stack /\
      spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
      EVERY (\off. off < dimword(:256)) offsets /\
      do_dup dist ps = (ops,ps') /\
      asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK (st with <|
        as_stack := EL dist st.as_stack :: st.as_stack;
        as_memory := FOLDL (\m off. asm_expand_memory (off + 32) m)
          written restore_offsets;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp ops)|>)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `0 < dist - 15 /\ dist - 15 + 15 = dist /\
   dist - 15 <= LENGTH ps.ps_stack /\
   dist <= 15 + LENGTH ps.ps_stack /\ dist <= 15 + LENGTH st.as_stack`
    by decide_tac >>
  qabbrev_tac `items = TAKE (dist - 15) (REVERSE ps.ps_stack)` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  `LENGTH offsets = dist - 15` by
    asm_simp_tac (srw_ss()) [Abbr `offsets`, Abbr `items`,
      spill_alloc_n_offsets_length, LENGTH_TAKE_EQ] >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    (qpat_x_assum `EVERY (\off. off < dimword(:256)) _` mp_tac >>
     simp[Abbr `offsets`, Abbr `items`]) >>
  `!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
     EL i offsets + 32 <= EL j offsets \/
     EL j offsets + 32 <= EL i offsets` by
    (mp_tac (Q.ISPECL [`items:operand list`,`ps.ps_alloc`,`ps.ps_spilled`]
       spill_alloc_n_offsets_separated) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       qpat_x_assum `EVERY (\off. off < dimword(:256)) _` mp_tac >>
       simp[Abbr `offsets`, Abbr `items`])) >>
     simp[LET_THM, Abbr `offsets`]) >>
  `ops = (MAP SOSpill offsets ++ [SODup 16]) ++
     (FLAT (MAP (\i. [SORestore (EL i offsets)] ++
         if LENGTH offsets <= 16 then [] else [SOSwap 1])
       (dup_restore_indices (LENGTH offsets))) ++
      if LENGTH offsets <= 16 then [SOSwap (LENGTH offsets)] else [])` by
    (mp_tac (Q.SPECL [`dist`,`ps`] do_dup_deep_ops) >>
     (impl_tac >- decide_tac) >>
     asm_simp_tac (srw_ss()) [LET_THM, Abbr `offsets`, Abbr `items`]) >>
  `LENGTH (execute_plan initial_fmp ops) = (2 * LENGTH offsets + 1) +
     (if LENGTH offsets <= 16 then 2 * LENGTH offsets + 1 else 3 * LENGTH offsets)` by
    (qpat_x_assum `ops = _` (fn th => pure_rewrite_tac [th]) >>
     ACCEPT_TAC (Q.SPEC `offsets` deep_dup_raw_code_length)) >>
  `0 < LENGTH offsets /\ LENGTH offsets + 15 < LENGTH st.as_stack` by decide_tac >>
  gvs[] >> `dist - 15 + 15 = dist` by decide_tac >>
  mp_tac (Q.SPECL [`offsets`,`lo`,`o2pc`,`prog`,`st`] deep_dup_raw_steps) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
  pure_rewrite_tac [ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >>
  pure_rewrite_tac [add_middle_one] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed raw duplication theorem: " ^ name)
  end) (DB.thms "doDupRaw")
