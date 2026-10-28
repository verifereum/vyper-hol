(* Physical swaps need encodable fresh spill slots, including when values
   repeat.  TOP-LEVEL: do_swap_venom_asm_rel, do_swap_checked_sim. *)
Theory doSwapCorrect
Ancestors
  doSwapSim spillWordBounds stackPlanTypes stackPlanOps stackModel
  codegenRel asmSem planExec planWf stackOpSim list rich_list arithmetic

Theorem do_swap_venom_asm_rel:
  !dist ps ops post initial_fmp lo o2pc prog vs st.
    do_swap dist ps = (ops,post) /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist <= 16`
  >- (mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`post`,`lo`,`o2pc`,`prog`,`vs`,`st`]
        do_swap_venom_asm_rel_small) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac bool_ss []) >>
  `16 < dist` by decide_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`] do_swap_big_decompose) >>
  (impl_tac >- decide_tac) >> simp_tac std_ss [LET_THM] >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `EVERY (\off. off < dimword(:256))
    (FST (spill_alloc_n [] ps.ps_alloc (top_n (dist + 1) ps.ps_stack)))` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!off. MEM (SOSpill off) ops ==> _` irule >>
     asm_simp_tac (srw_ss()) [MEM_MAP]) >>
  mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_swap_deep_venom_asm_rel) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac)) >> asm_rewrite_tac []
QED

Theorem do_swap_checked_sim:
  !dist ps ops post initial_fmp lo o2pc prog vs st.
    do_swap dist ps = (ops,post) /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_swap_venom_asm_rel) >>
  (impl_tac >- (asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
    mp_tac (Q.SPECL [`initial_fmp`,`ops`,`prog`,`st.as_pc`,`off`]
      plan_spill_offset_word_bound) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp_tac bool_ss [])) >> simp_tac bool_ss []
QED

Theorem two_swaps_checked_sim:
  !d1 d2 ps ops1 mid ops2 post initial_fmp lo o2pc prog vs st.
    d1 < LENGTH ps.ps_stack /\ d2 < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    do_swap d1 ps = (ops1,mid) /\ do_swap d2 mid = (ops2,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
    ?st'. asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) st = AsmOK st' /\
      venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2)) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH post.ps_stack = LENGTH ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH mid.ps_stack = LENGTH ps.ps_stack` by
    (mp_tac (Q.SPECL [`d1`,`ps`] do_swap_length) >> asm_simp_tac (srw_ss()) []) >>
  `d2 < LENGTH mid.ps_stack` by decide_tac >>
  `LENGTH post.ps_stack = LENGTH ps.ps_stack` by
    (mp_tac (Q.SPECL [`d2`,`mid`] do_swap_length) >> asm_simp_tac (srw_ss()) []) >>
  `spill_alloc_layout_wf mid.ps_alloc mid.ps_spilled` by
    (mp_tac (Q.SPECL [`d1`,`ps`] do_swap_layout_wf) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac (srw_ss()) []) >>
  `spill_alloc_layout_wf post.ps_alloc post.ps_spilled` by
    (mp_tac (Q.SPECL [`d2`,`mid`] do_swap_layout_wf) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac (srw_ss()) []) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp ops1) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp ops1))
     (execute_plan initial_fmp ops2)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`d1`,`ps`,`ops1`,`mid`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_swap_checked_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  mp_tac (Q.SPECL [`d2`,`mid`,`ops2`,`post`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st1`] do_swap_checked_sim) >>
  (impl_tac >- asm_simp_tac (srw_ss()) []) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >> qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked-swap proof: " ^ name)
  end) (DB.thms "doSwapCorrect")
