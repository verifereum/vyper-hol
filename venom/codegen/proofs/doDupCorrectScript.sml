(* Duplication simulation: stack and temporary-memory frame helpers. *)
Theory doDupCorrect
Ancestors
  doDupRaw doDupModel doSwapSim stackOpSim codegenRel stackModel stackPlanOps
  asmSem planExec allocMono planAlign strongPrefixSim mixedPrefixSim prefixExec
  instSimHelpers list rich_list arithmetic finite_map

Theorem plan_stack_rel_dup[local]:
  !lo vs pstk astk dist.
    plan_stack_rel lo vs pstk astk /\ dist < LENGTH pstk ==>
    plan_stack_rel lo vs (stack_dup dist pstk)
      (EL dist astk :: astk)
Proof
  rpt gen_tac >> strip_tac >> simp[stack_dup_def] >>
  irule plan_stack_rel_push >> conj_tac
  >- (`LENGTH pstk - dist - 1 = LENGTH pstk - 1 - dist` by decide_tac >>
      mp_tac (Q.SPECL [`lo`,`vs`,`pstk`,`astk`,`dist`] plan_stack_rel_el) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      asm_simp_tac (srw_ss()) [stack_peek_def, EL_REVERSE, PRE_SUB1]) >>
  first_assum ACCEPT_TAC
QED

Theorem dup_spill_memory_frame[local]:
  !lo vs spilled old_alloc final_alloc offsets vals restore_offsets mem.
    LENGTH offsets = LENGTH vals /\
    memory_rel old_alloc vs.vs_memory mem /\
    plan_spill_rel lo vs spilled mem /\
    final_alloc.sa_spill_base = old_alloc.sa_spill_base /\
    old_alloc.sa_next_offset <= final_alloc.sa_next_offset /\
    EVERY (\off. final_alloc.sa_spill_base <= off /\
      off + 32 <= final_alloc.sa_next_offset) offsets /\
    (!k op off. k < LENGTH offsets /\ FLOOKUP spilled op = SOME off ==>
      off + 32 <= EL k offsets \/ EL k offsets + 32 <= off) ==>
    let written = FOLDL (\m p. mem_write32 (FST p) (SND p) m) mem
          (ZIP (offsets,vals));
        final_mem = FOLDL (\m off. asm_expand_memory (off + 32) m)
          written restore_offsets
    in memory_rel final_alloc vs.vs_memory final_mem /\
       plan_spill_rel lo vs spilled final_mem
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  `memory_rel final_alloc vs.vs_memory mem` by
    (irule memory_rel_widen >> qexists_tac `old_alloc` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `written =
    FOLDL (\m p. mem_write32 (FST p) (SND p) m) mem (ZIP (offsets,vals))` >>
  `memory_rel final_alloc vs.vs_memory written` by
    (simp[Abbr `written`] >> irule memory_rel_write_fold >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `plan_spill_rel lo vs spilled written` by
    (simp[Abbr `written`] >> irule plan_spill_rel_raw_fold >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule memory_rel_expand_fold >> first_assum ACCEPT_TAC) >>
  irule plan_spill_rel_expand_fold >> first_assum ACCEPT_TAC
QED

Theorem spill_alloc_n_memory_frame:
  !lo vs al spilled items vals restore_offsets mem.
    spill_alloc_layout_wf al spilled /\ LENGTH items = LENGTH vals /\
    memory_rel al vs.vs_memory mem /\ plan_spill_rel lo vs spilled mem /\
    EVERY (\off. off < dimword(:256)) (FST (spill_alloc_n [] al items)) ==>
    let offsets = FST (spill_alloc_n [] al items);
        final_alloc = FOLDL (\a off. free_spill_slot off a)
          (SND (spill_alloc_n [] al items)) offsets;
        written = FOLDL (\m p. mem_write32 (FST p) (SND p) m) mem
          (ZIP (offsets,vals));
        final_mem = FOLDL (\m off. asm_expand_memory (off + 32) m)
          written restore_offsets
    in memory_rel final_alloc vs.vs_memory final_mem /\
       plan_spill_rel lo vs spilled final_mem
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] al items)` >>
  qabbrev_tac `final_alloc = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] al items)) offsets` >>
  `spill_alloc_layout_wf final_alloc spilled /\
   final_alloc.sa_spill_base = al.sa_spill_base /\
   al.sa_next_offset <= final_alloc.sa_next_offset /\
   EVERY (\off. final_alloc.sa_spill_base <= off /\
     off + 32 <= final_alloc.sa_next_offset) offsets` by
    (mp_tac (Q.SPECL [`al`,`spilled`,`items`] spill_alloc_n_released_layout) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[LET_THM, Abbr `offsets`, Abbr `final_alloc`]) >>
  `!k op off. k < LENGTH offsets /\ FLOOKUP spilled op = SOME off ==>
     off + 32 <= EL k offsets \/ EL k offsets + 32 <= off` by
    (mp_tac (Q.SPECL [`items`,`al`,`spilled`] spill_alloc_n_slot_facts) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       qpat_x_assum `EVERY (\off. off < dimword(:256)) _` mp_tac >>
       simp[Abbr `offsets`])) >>
     simp_tac std_ss [LET_THM] >> strip_tac >>
     rpt gen_tac >> strip_tac >> fs[Abbr `offsets`] >>
     qpat_x_assum `!k. k < _ ==> _` (qspec_then `k` mp_tac) >>
     asm_simp_tac std_ss [] >> strip_tac >>
     qpat_x_assum `!op off. FLOOKUP spilled op = SOME off ==> _`
       (qspecl_then [`op`,`off`] mp_tac) >> asm_simp_tac std_ss []) >>
  `LENGTH offsets = LENGTH vals` by
    asm_simp_tac (srw_ss()) [Abbr `offsets`, spill_alloc_n_offsets_length] >>
  mp_tac (Q.SPECL [`lo`,`vs`,`spilled`,`al`,`final_alloc`,
    `offsets`,`vals`,`restore_offsets`,`mem`] dup_spill_memory_frame) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[LET_THM, Abbr `offsets`, Abbr `final_alloc`]
QED

Theorem do_dup_deep_state[local]:
  !dist ps ops ps'.
    15 < dist /\ dist < LENGTH ps.ps_stack /\ do_dup dist ps = (ops,ps') ==>
    let items = TAKE (dist - 15) (REVERSE ps.ps_stack);
        offsets = FST (spill_alloc_n [] ps.ps_alloc items)
    in ps'.ps_stack = stack_dup dist ps.ps_stack /\
       ps'.ps_spilled = ps.ps_spilled /\
       ps'.ps_alloc = FOLDL (\a off. free_spill_slot off a)
         (SND (spill_alloc_n [] ps.ps_alloc items)) offsets
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`] do_dup_big_decompose) >>
  (impl_tac >- decide_tac) >> simp_tac std_ss [LET_THM] >> strip_tac >>
  gvs[LET_THM]
QED

Theorem do_dup_deep_frame[local]:
  !dist ps ops ps' lo vs st new_pc.
    let k = dist - 15;
        items = TAKE k (REVERSE ps.ps_stack);
        offsets = FST (spill_alloc_n [] ps.ps_alloc items);
        written = FOLDL (\m p. mem_write32 (FST p) (SND p) m)
          st.as_memory (ZIP (offsets,TAKE k st.as_stack));
        final_mem = FOLDL (\m off. asm_expand_memory (off + 32) m)
          written (MAP (\i. EL i offsets) (dup_restore_indices k))
    in 15 < dist /\ dist < LENGTH ps.ps_stack /\
      spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
      EVERY (\off. off < dimword(:256)) offsets /\
      do_dup dist ps = (ops,ps') /\ venom_asm_rel lo ps vs st ==>
      venom_asm_rel lo ps' vs
        (st with <|as_stack := EL dist st.as_stack :: st.as_stack;
                   as_memory := final_mem; as_pc := new_pc|>)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `plan_stack_rel lo vs ps.ps_stack st.as_stack /\
   plan_spill_rel lo vs ps.ps_spilled st.as_memory /\
   memory_rel ps.ps_alloc vs.vs_memory st.as_memory` by fs[venom_asm_rel_def] >>
  drule_all plan_stack_rel_length >> strip_tac >>
  `dist <= 15 + LENGTH ps.ps_stack /\ dist <= 15 + LENGTH st.as_stack`
    by decide_tac >>
  qabbrev_tac `items = TAKE (dist - 15) (REVERSE ps.ps_stack)` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `final_mem = FOLDL (\m off. asm_expand_memory (off + 32) m)
    (FOLDL (\m p. mem_write32 (FST p) (SND p) m) st.as_memory
      (ZIP (offsets,TAKE (dist - 15) st.as_stack)))
    (MAP (\i. EL i offsets) (dup_restore_indices (dist - 15)))` >>
  `ps'.ps_stack = stack_dup dist ps.ps_stack /\
   ps'.ps_spilled = ps.ps_spilled /\
   ps'.ps_alloc = FOLDL (\a off. free_spill_slot off a)
     (SND (spill_alloc_n [] ps.ps_alloc items)) offsets` by
    (mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`] do_dup_deep_state) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[LET_THM, Abbr `items`, Abbr `offsets`]) >>
  `plan_stack_rel lo vs ps'.ps_stack (EL dist st.as_stack :: st.as_stack)` by
    (asm_rewrite_tac [] >> irule plan_stack_rel_dup >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `memory_rel ps'.ps_alloc vs.vs_memory final_mem /\
   plan_spill_rel lo vs ps'.ps_spilled final_mem` by
    (mp_tac (Q.ISPECL [`lo:(string,num) fmap`,`vs:venom_state`,
       `ps.ps_alloc`,`ps.ps_spilled`,
       `items:operand list`,`TAKE (dist - 15) st.as_stack`,
       `MAP (\i. EL i (offsets:num list)) (dup_restore_indices (dist - 15))`,
       `st.as_memory`] spill_alloc_n_memory_frame) >>
     (impl_tac >- asm_simp_tac (srw_ss())
       [Abbr `items`, Abbr `offsets`, LENGTH_TAKE_EQ]) >>
     asm_simp_tac (srw_ss())
       [LET_THM, Abbr `final_mem`, Abbr `items`, Abbr `offsets`]) >>
  fs[venom_asm_rel_def] >> gvs[]
QED

Theorem do_dup_venom_asm_rel_shallow[local]:
  !dist ps ops ps' lo o2pc prog vs st.
    do_dup dist ps = (ops,ps') /\ dist <= 15 /\
    dist < LENGTH ps.ps_stack /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `ops = [SODup (dist + 1)] /\
   ps' = ps with ps_stack := stack_dup dist ps.ps_stack` by
    (qpat_x_assum `do_dup _ _ = _` mp_tac >>
     asm_simp_tac (srw_ss()) [do_dup_def]) >>
  `LENGTH ps.ps_stack - (dist + 1) = LENGTH ps.ps_stack - 1 - dist`
    by decide_tac >> gvs[] >>
  mp_tac (Q.SPECL [`[SODup (dist + 1)]`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`ps`,`vs`,`st`] simple_prefix_venom_asm_rel) >>
  (impl_tac >- (simp[is_simple_stack_op_def, prefix_wf_def, stack_op_wf_def] >>
    ASM_REWRITE_TAC[] >> decide_tac)) >>
  strip_tac >> qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  fs[apply_simple_ops_def, apply_simple_op_def, stack_dup_def, stack_peek_def]
QED

Theorem do_dup_venom_asm_rel_deep[local]:
  !dist ps ops ps' lo o2pc prog vs st.
    do_dup dist ps = (ops,ps') /\ 15 < dist /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\off. off < dimword(:256))
      (FST (spill_alloc_n [] ps.ps_alloc
        (TAKE (dist - 15) (REVERSE ps.ps_stack)))) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH ps.ps_stack = LENGTH st.as_stack` by
    fs[venom_asm_rel_def, plan_stack_rel_def] >>
  qabbrev_tac `items = TAKE (dist - 15) (REVERSE ps.ps_stack)` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `final_mem = FOLDL (\m off. asm_expand_memory (off + 32) m)
    (FOLDL (\m p. mem_write32 (FST p) (SND p) m) st.as_memory
      (ZIP (offsets,TAKE (dist - 15) st.as_stack)))
    (MAP (\i. EL i offsets) (dup_restore_indices (dist - 15)))` >>
  qabbrev_tac `post = st with <|
    as_stack := EL dist st.as_stack :: st.as_stack;
    as_memory := final_mem;
    as_pc := st.as_pc + LENGTH (execute_plan initial_fmp ops)|>` >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    asm_simp_tac (srw_ss()) [Abbr `offsets`, Abbr `items`] >>
  `asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
     AsmOK post` by
    (mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`lo`,`o2pc`,`prog`,`st`]
       do_dup_deep_execution) >> simp_tac std_ss [LET_THM] >>
     (impl_tac >- (fs[Abbr `items`, Abbr `offsets`] >>
       rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
     simp[Abbr `post`, Abbr `final_mem`, Abbr `items`, Abbr `offsets`]) >>
  `venom_asm_rel lo ps' vs post` by
    (mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`lo`,`vs`,`st`,
       `st.as_pc + LENGTH (execute_plan initial_fmp ops)`] do_dup_deep_frame) >>
     simp_tac std_ss [LET_THM] >>
     (impl_tac >- (fs[Abbr `items`, Abbr `offsets`] >>
       rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
     simp[Abbr `post`, Abbr `final_mem`, Abbr `items`, Abbr `offsets`]) >>
  qexists_tac `post` >> ASM_REWRITE_TAC[] >> simp[Abbr `post`]
QED

Theorem do_dup_venom_asm_rel_prefix:
  !dist ps ops ps' initial_fmp lo o2pc prog vs st.
    do_dup dist ps = (ops,ps') /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    prefix_spill_wf initial_fmp lo ops ps /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist <= 15`
  >- (mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`lo`,`o2pc`,`prog`,`vs`,`st`]
        do_dup_venom_asm_rel_shallow) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac bool_ss []) >>
  `15 < dist` by decide_tac >>
  `EVERY (\off. off < dimword(:256))
    (FST (spill_alloc_n [] ps.ps_alloc
      (TAKE (dist - 15) (REVERSE ps.ps_stack))))` by
    (mp_tac (Q.SPECL [`dist`,`ps`,`lo`] do_dup_spill_word_bounds) >>
     (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
       rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
     simp[]) >>
  mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`lo`,`o2pc`,`prog`,`vs`,`st`]
    do_dup_venom_asm_rel_deep) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

(* Physical duplication only needs encodable fresh spill addresses.  The
   temporary spill map may overwrite equal operands while restoring their
   distinct physical slots, so its threaded lookup condition is unnecessary. *)
Theorem do_dup_venom_asm_rel:
  !dist ps ops ps' initial_fmp lo o2pc prog vs st.
    do_dup dist ps = (ops,ps') /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist <= 15`
  >- (mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`lo`,`o2pc`,`prog`,`vs`,`st`]
        do_dup_venom_asm_rel_shallow) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac bool_ss []) >>
  `15 < dist` by decide_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`] do_dup_deep_ops) >>
  (impl_tac >- decide_tac) >> simp_tac std_ss [LET_THM] >>
  asm_simp_tac (srw_ss()) [] >> disch_tac >>
  `EVERY (\off. off < dimword(:256))
    (FST (spill_alloc_n [] ps.ps_alloc
      (TAKE (dist - 15) (REVERSE ps.ps_stack))))` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!off. MEM (SOSpill off) ops ==> _` irule >>
     asm_simp_tac (srw_ss()) [MEM_MAP]) >>
  mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`lo`,`o2pc`,`prog`,`vs`,`st`]
    do_dup_venom_asm_rel_deep) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> asm_rewrite_tac []
QED

(* PHI may duplicate at any depth before naming the new top value. *)
Theorem do_dup_poke_venom_asm_rel:
  !lo ps vs st dist out v ops ps'.
    venom_asm_rel lo ps' vs st /\ do_dup dist ps = (ops,ps') /\
    dist < LENGTH ps.ps_stack /\
    operand_val vs lo (stack_peek dist ps.ps_stack) = SOME v /\
    stack_peek dist ps.ps_stack <> dead_stack_marker /\
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
      case op of Var x => x <> out | _ => T) ==>
    venom_asm_rel lo
      (ps' with ps_stack := stack_poke 0 (Var out) ps'.ps_stack)
      (update_var out v vs) st
Proof
  rpt gen_tac >> strip_tac >>
  `ps'.ps_stack = stack_dup dist ps.ps_stack /\
   ps'.ps_spilled = ps.ps_spilled` by
    (qpat_assum `do_dup dist ps = _` (fn eq =>
       map_every assume_tac (map (REWRITE_RULE [eq,pairTheory.SND])
         [Q.SPECL [`dist`,`ps`] do_dup_stack,
          Q.SPECL [`dist`,`ps`] do_dup_spilled])) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH ps.ps_stack - (dist + 1) = LENGTH ps.ps_stack - 1 - dist`
    by decide_tac >>
  `MEM (stack_peek dist ps.ps_stack) ps.ps_stack` by
    (pure_rewrite_tac[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
  mp_tac (Q.SPECL [`lo`,`ps'`,`vs`,`st`,`out`,`v`,`0`]
    venom_asm_rel_poke_update_var) >>
  (impl_tac >- (asm_simp_tac std_ss
      [stack_dup_def, stack_peek_def, EL_LENGTH_SNOC, EVERY_SNOC,
       LENGTH_SNOC, ADD_SUB] >>
    qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >>
    asm_simp_tac std_ss [EVERY_MEM, GSYM stack_peek_def])) >>
  simp_tac bool_ss []
QED

Theorem do_dup_poke_sim:
  !dist ps ops ps' initial_fmp lo o2pc prog vs st out v.
    do_dup dist ps = (ops,ps') /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    prefix_spill_wf initial_fmp lo ops ps /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    operand_val vs lo (stack_peek dist ps.ps_stack) = SOME v /\
    stack_peek dist ps.ps_stack <> dead_stack_marker /\
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
      case op of Var x => x <> out | _ => T) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\
      venom_asm_rel lo
        (ps' with ps_stack := stack_poke 0 (Var out) ps'.ps_stack)
        (update_var out v vs) st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_dup_venom_asm_rel_prefix) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `st'` >> asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`lo`,`ps`,`vs`,`st'`,`dist`,`out`,`v`,`ops`,`ps'`]
    do_dup_poke_venom_asm_rel) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED
