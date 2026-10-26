(* Framed relation transport for temporary deep-DUP spills. *)
Theory deepDupFrameSim
Ancestors doSwapSim spillSim codegenRel asmSem finite_map list
Libs BasicProvers

Theorem venom_asm_rel_spill_frame_transfer:
  !lo initial via target vs before after.
    venom_asm_rel lo initial vs before /\
    venom_asm_rel lo via vs after /\
    target.ps_stack = via.ps_stack /\
    target.ps_alloc.sa_spill_base = via.ps_alloc.sa_spill_base /\
    target.ps_alloc.sa_next_offset = via.ps_alloc.sa_next_offset /\
    (!op off. FLOOKUP target.ps_spilled op = SOME off ==>
       FLOOKUP via.ps_spilled op = SOME off \/
       (FLOOKUP initial.ps_spilled op = SOME off /\
        word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off after.as_memory)) =
        word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off before.as_memory)))) ==>
    venom_asm_rel lo target vs after
Proof
  rpt gen_tac >> strip_tac >>
  `plan_spill_rel lo vs target.ps_spilled after.as_memory` by
    (gvs[venom_asm_rel_def, plan_spill_rel_def] >> metis_tac[]) >>
  gvs[venom_asm_rel_def, memory_rel_def] >> metis_tac[]
QED

Theorem spill_asm_read32_frame:
  !lo o2pc prog tmp off before after.
    tmp < dimword(:256) /\ 1 <= LENGTH before.as_stack /\
    asm_block_at prog before.as_pc
      [AsmPush (encode_num_bytes tmp); AsmOp "MSTORE"] /\
    asm_steps lo o2pc prog 2 before = AsmOK after /\
    (off + 32 <= tmp \/ tmp + 32 <= off) ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off after.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off before.as_memory))
Proof
  rpt strip_tac >>
  `LENGTH before.as_stack >= 1` by decide_tac >>
  drule_all spill_asm_steps >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >> gvs[] >>
  irule mem_write32_read32_disjoint >> simp[]
QED

Theorem restore_asm_read32_frame:
  !lo o2pc prog tmp off before after.
    tmp < dimword(:256) /\
    asm_block_at prog before.as_pc
      [AsmPush (encode_num_bytes tmp); AsmOp "MLOAD"] /\
    asm_steps lo o2pc prog 2 before = AsmOK after ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off after.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off before.as_memory))
Proof
  rpt strip_tac >> drule_all restore_asm_steps >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  gvs[word_of_bytes_take_drop_expand]
QED

Theorem dup16_asm_steps[local]:
  !lo o2pc prog st.
    15 < LENGTH st.as_stack /\
    asm_block_at prog st.as_pc [AsmOp (dup_name 16)] ==>
    asm_steps lo o2pc prog 1 st =
      AsmOK (asm_next (st with as_stack := EL 15 st.as_stack :: st.as_stack))
Proof
  rpt strip_tac >>
  `st.as_pc < LENGTH prog /\ EL st.as_pc prog = AsmOp (dup_name 16)` by
    (gvs[asm_block_at_def] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  SUBST1_TAC (DECIDE ``1 = SUC 0``) >>
  simp[Once asm_steps_def] >>
  mp_tac (Q.SPECL [`lo`, `o2pc`, `15`, `st`] stackOpAsmSimTheory.asm_step_dup_ok) >>
  simp[asm_steps_def]
QED

Theorem swap1_asm_steps[local]:
  !lo o2pc prog st.
    1 < LENGTH st.as_stack /\
    asm_block_at prog st.as_pc [AsmOp (swap_name 1)] ==>
    asm_steps lo o2pc prog 1 st =
      AsmOK (asm_next (st with as_stack :=
        LUPDATE (HD st.as_stack) 1 (LUPDATE (EL 1 st.as_stack) 0 st.as_stack)))
Proof
  rpt strip_tac >>
  `st.as_pc < LENGTH prog /\ EL st.as_pc prog = AsmOp (swap_name 1)` by
    (gvs[asm_block_at_def] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  SUBST1_TAC (DECIDE ``1 = SUC 0``) >>
  simp[Once asm_steps_def] >>
  mp_tac (Q.SPECL [`lo`, `o2pc`, `1`, `st`] stackOpAsmSimTheory.asm_step_swap_ok) >>
  simp[asm_steps_def]
QED

Theorem singleton_dup_asm_read32_frame:
  !lo o2pc prog tmp off before after.
    tmp < dimword(:256) /\ 16 < LENGTH before.as_stack /\
    asm_block_at prog before.as_pc
      ([AsmPush (encode_num_bytes tmp); AsmOp "MSTORE"] ++
       [AsmOp (dup_name 16)] ++
       [AsmPush (encode_num_bytes tmp); AsmOp "MLOAD"] ++
       [AsmOp (swap_name 1)]) /\
    asm_steps lo o2pc prog 6 before = AsmOK after /\
    (off + 32 <= tmp \/ tmp + 32 <= off) ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off after.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off before.as_memory))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  rewrite_tac[stackOpSimTheory.asm_block_at_append] >> simp[] >> strip_tac >>
  `?s1. asm_steps lo o2pc prog 2 before = AsmOK s1 /\
        s1.as_stack = TL before.as_stack /\ s1.as_pc = before.as_pc + 2 /\
        word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off s1.as_memory)) =
        word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off before.as_memory))` by
    (`LENGTH before.as_stack >= 1` by decide_tac >>
     drule_all spill_asm_steps >>
     disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
     qexists_tac `st'` >> simp[] >>
     irule mem_write32_read32_disjoint >> simp[]) >>
  `15 < LENGTH s1.as_stack` by
    (simp[] >> Cases_on `before.as_stack` >> gvs[]) >>
  `asm_block_at prog s1.as_pc [AsmOp (dup_name 16)]` by metis_tac[] >>
  qabbrev_tac `s2 = asm_next (s1 with as_stack := EL 15 s1.as_stack :: s1.as_stack)` >>
  `asm_steps lo o2pc prog 1 s1 = AsmOK s2` by
    (simp[Abbr `s2`, NoAsms] >> irule dup16_asm_steps >> simp[]) >>
  `s2.as_pc = before.as_pc + 3 /\ s2.as_memory = s1.as_memory` by
    simp[Abbr `s2`, asm_next_def] >>
  suspend "restore"
QED

Resume singleton_dup_asm_read32_frame[restore]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `asm_block_at prog s2.as_pc
     [AsmPush (encode_num_bytes tmp); AsmOp "MLOAD"]` by metis_tac[] >>
  `?s3. asm_steps lo o2pc prog 2 s2 = AsmOK s3 /\
        s3.as_pc = before.as_pc + 5 /\
        LENGTH s3.as_stack = LENGTH s2.as_stack + 1 /\
        word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off s3.as_memory)) =
        word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off s2.as_memory))` by
    (drule_all restore_asm_steps >>
     disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
     qexists_tac `st'` >> simp[word_of_bytes_take_drop_expand]) >>
  `1 < LENGTH s3.as_stack` by
    (gvs[Abbr `s2`, asm_next_def] >> decide_tac) >>
  `asm_block_at prog s3.as_pc [AsmOp (swap_name 1)]` by metis_tac[] >>
  qabbrev_tac `s4 = asm_next (s3 with as_stack :=
    LUPDATE (HD s3.as_stack) 1 (LUPDATE (EL 1 s3.as_stack) 0 s3.as_stack))` >>
  `asm_steps lo o2pc prog 1 s3 = AsmOK s4` by
    (simp[Abbr `s4`, NoAsms] >> irule swap1_asm_steps >> simp[]) >>
  `s4.as_memory = s3.as_memory` by simp[Abbr `s4`, asm_next_def] >>
  `asm_steps lo o2pc prog 6 before = AsmOK s4` by
    (pure_rewrite_tac[DECIDE ``(6:num) = 2 + (1 + (2 + 1))``] >>
     rewrite_tac[stackOpSimTheory.asm_steps_add] >> simp[]) >>
  gvs[]
QED

Finalise singleton_dup_asm_read32_frame

Theorem singleton_dup_plan_read32_frame:
  !initial_fmp lo o2pc prog tmp off before after.
    tmp < dimword(:256) /\ 16 < LENGTH before.as_stack /\
    asm_block_at prog before.as_pc
      (execute_plan initial_fmp [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1]) /\
    asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1]))
      before = AsmOK after /\
    (off + 32 <= tmp \/ tmp + 32 <= off) ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off after.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off before.as_memory))
Proof
  rpt strip_tac >>
  (irule singleton_dup_asm_read32_frame >>
   (conj_tac >- simp[]) >> qexistsl [`lo`, `o2pc`, `prog`, `tmp`] >>
   gvs[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def])
QED

(* This boundary deliberately restores the initial spill map in the semantic
   target: a symbolic restore may have deleted the overwritten TOS binding. *)
Theorem singleton_dup_venom_asm_rel_frame:
  !ps tmp lo o2pc prog vs before.
    16 < LENGTH ps.ps_stack /\ tmp < dimword(:256) /\
    (!op off. FLOOKUP ps.ps_spilled op = SOME off ==>
       off + 32 <= tmp \/ tmp + 32 <= off) /\
    prefix_wf lo (LENGTH ps.ps_stack)
      [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1] /\
    prefix_spill_wf initial_fmp lo
      [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1] ps /\
    venom_asm_rel lo ps vs before /\
    asm_block_at prog before.as_pc
      (execute_plan initial_fmp [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1]) ==>
    ?after.
      asm_steps lo o2pc prog
        (LENGTH (execute_plan initial_fmp [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1]))
        before = AsmOK after /\
      venom_asm_rel lo
        (ps with <|ps_stack := stack_dup 16 ps.ps_stack;
          ps_alloc := ps.ps_alloc with sa_next_offset :=
            MAX ps.ps_alloc.sa_next_offset (tmp + 32)|>) vs after /\
      after.as_pc = before.as_pc +
        LENGTH (execute_plan initial_fmp [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1])
Proof
  rpt gen_tac >> strip_tac >>
  `!op. FLOOKUP ps.ps_spilled op <> SOME tmp` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `16 < LENGTH before.as_stack` by
    (gvs[codegenRelTheory.venom_asm_rel_def, codegenRelTheory.plan_stack_rel_def] >>
     metis_tac[listTheory.LIST_REL_LENGTH, LENGTH_REVERSE]) >>
  `EVERY is_prefix_op [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1]` by
    simp[prefixSimTheory.is_prefix_op_def, strongPrefixSimTheory.is_simple_stack_op_def] >>
  drule_all mixedPrefixSimTheory.mixed_prefix_venom_asm_rel >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_spill_frame_transfer >>
  qexistsl [`before`, `ps`, `apply_prefix_ops initial_fmp lo
    [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1] ps`] >>
  mp_tac (Q.SPECL [`ps`, `tmp`, `lo`] singleton_dup_apply) >>
  simp[LET_THM] >> strip_tac >> simp[] >>
  rpt strip_tac >> disj2_tac >> simp[] >>
  irule singleton_dup_plan_read32_frame >> (conj_tac >- simp[]) >>
  qexistsl [`initial_fmp`, `lo`, `o2pc`, `prog`, `tmp`] >> simp[] >> metis_tac[]
QED

Theorem do_dup16_decompose:
  !ps tmp al.
    16 < LENGTH ps.ps_stack /\ alloc_spill_slot ps.ps_alloc = (tmp,al) ==>
    do_dup 16 ps =
      ([SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1],
       ps with <|ps_stack := stack_dup 16 ps.ps_stack;
                 ps_alloc := free_spill_slot tmp al|>)
Proof
  rpt strip_tac >>
  `?item. REVERSE (top_n 1 ps.ps_stack) = [item]` by
    (simp[stackPlanOpsTheory.top_n_def] >>
     Cases_on `REVERSE ps.ps_stack` >> gvs[LENGTH_REVERSE]) >>
  simp[stackPlanOpsTheory.do_dup_def, LET_THM]
QED

Theorem do_dup16_venom_asm_rel_frame:
  !ps ops target lo o2pc prog vs before.
    do_dup 16 ps = (ops,target) /\ 16 < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    prefix_spill_wf initial_fmp lo ops ps /\
    venom_asm_rel lo ps vs before /\
    asm_block_at prog before.as_pc (execute_plan initial_fmp ops) ==>
    ?after.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) before = AsmOK after /\
      venom_asm_rel lo target vs after /\
      after.as_pc = before.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  rename1 `alloc_spill_slot ps.ps_alloc = (tmp,al)` >>
  drule_all do_dup16_decompose >> strip_tac >> gvs[] >>
  `tmp < dimword(:256) /\
   (!op off. FLOOKUP ps.ps_spilled op = SOME off ==>
       off + 32 <= tmp \/ tmp + 32 <= off)` by
    (gvs[mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def] >>
     metis_tac[]) >>
  `prefix_wf lo (LENGTH ps.ps_stack)
      [SOSpill tmp; SODup 16; SORestore tmp; SOSwap 1]` by
    (mp_tac (Q.ISPECL [`16:num`, `ps:plan_state`, `lo:string |-> num`]
       planWfTheory.do_dup_wf_len) >> simp[LET_THM]) >>
  drule_all singleton_dup_venom_asm_rel_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `after` >> simp[] >>
  irule venom_asm_rel_ps_transfer >>
  qexists_tac `ps with <|ps_stack := stack_dup 16 ps.ps_stack;
     ps_alloc := ps.ps_alloc with sa_next_offset :=
       MAX ps.ps_alloc.sa_next_offset (tmp + 32)|>` >>
  simp[stackPlanTypesTheory.free_spill_slot_def] >>
  metis_tac[alloc_spill_slot_max_agree, alloc_spill_slot_spill_base]
QED
