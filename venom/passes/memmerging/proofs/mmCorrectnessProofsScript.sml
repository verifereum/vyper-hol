(* Structural and execution bridges used by memmerging proofs. *)

Theory mmCorrectnessProofs
Ancestors
  mmTransform mmCopyEquiv passSimulationDefs passSimulationProofs
  crossBlockSimProofs crossBlockSimDefs passSimulationProps stateEquivProps
  stateEquiv stateEquivProofs venomExecSemantics execEquivParamProofs
  analysisSimProofsBase analysisSimDefs venomInstProofs venomWf
  venomInst venomState pred_set finite_map
  list rich_list arithmetic words execEquivProps

Theorem all_distinct_inst_id_idx:
  !insts i j.
    ALL_DISTINCT (MAP (\inst. inst.inst_id) insts) /\
    i < LENGTH insts /\ j < LENGTH insts /\
    (EL i insts).inst_id = (EL j insts).inst_id ==>
    i = j
Proof
  rpt strip_tac >>
  `EL i (MAP (\inst. inst.inst_id) insts) =
   EL j (MAP (\inst. inst.inst_id) insts)`
    by simp[EL_MAP] >>
  `i < LENGTH (MAP (\inst. inst.inst_id) insts) /\
   j < LENGTH (MAP (\inst. inst.inst_id) insts)` by simp[] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED


Theorem lift_result_state_equiv_mono:
  !fresh1 fresh2 r1 r2.
    lift_result (state_equiv fresh1) (execution_equiv fresh1) (execution_equiv fresh1) r1 r2 /\
    fresh1 SUBSET fresh2 ==>
    lift_result (state_equiv fresh2) (execution_equiv fresh2) (execution_equiv fresh2) r1 r2
Proof
  rpt strip_tac >>
  irule lift_result_weaken_proof >>
  qexists_tac `state_equiv fresh1` >>
  qexists_tac `execution_equiv fresh1` >>
  qexists_tac `execution_equiv fresh1` >>
  simp[] >> metis_tac[state_equiv_subset, execution_equiv_subset]
QED


Theorem exec_block_at_terminator[local]:
  !fuel ctx bb j inst s.
    get_instruction bb j = SOME inst /\
    is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
       OK s'' => if s''.vs_halted then Halt s'' else OK s''
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet rv ss => IntRet rv ss
     | Error e => Error e)
Proof
  rw[Once exec_block_def]
QED


Theorem lift_result_wrap_terminator[local]:
  !R_ok R_term R_abort r1 r2.
    (∀s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted) /\
    (∀s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    lift_result R_ok R_term R_abort r1 r2 ==>
    lift_result R_ok R_term R_abort
      (case r1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case r2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def] >>
  `v.vs_halted = v'.vs_halted` by metis_tac[] >>
  Cases_on `v.vs_halted` >> fs[lift_result_def]
QED


Theorem terminator_step_equiv[local]:
  !fresh fuel ctx inst s1 s2 j1 j2.
    state_equiv fresh s1 s2 /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (case step_inst fuel ctx inst (s1 with vs_inst_idx := j1) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst (s2 with vs_inst_idx := j2) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `valid_state_rel (state_equiv fresh) (execution_equiv fresh)` by
    simp[state_equiv_execution_equiv_valid_state_rel_proof] >>
  (* Step 1: s1 with j1 -> s1 via _rev *)
  qspecl_then [`state_equiv fresh`, `execution_equiv fresh`]
    mp_tac terminator_exec_block_step_lift_rev >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `j1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Step 2: s2 -> s2 with j2 via _fwd *)
  qspecl_then [`state_equiv fresh`, `execution_equiv fresh`]
    mp_tac terminator_exec_block_step_lift >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s2`, `j2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Step 3: s1 -> s2 via result_equiv on raw step_inst *)
  `result_equiv fresh (step_inst fuel ctx inst s1)
                       (step_inst fuel ctx inst s2)` by
    (irule step_inst_result_equiv >> simp[]) >>
  fs[result_equiv_is_lift_result] >>
  (* Wrap the raw lift_result into the terminator form *)
  `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
     (case step_inst fuel ctx inst s1 of
        OK s'' => if s''.vs_halted then Halt s'' else OK s''
      | Halt s' => Halt s' | Abort a s' => Abort a s'
      | IntRet rv ss => IntRet rv ss | Error e => Error e)
     (case step_inst fuel ctx inst s2 of
        OK s'' => if s''.vs_halted then Halt s'' else OK s''
      | Halt s' => Halt s' | Abort a s' => Abort a s'
      | IntRet rv ss => IntRet rv ss | Error e => Error e)` by (
    irule lift_result_wrap_terminator >>
    rw[state_equiv_def, execution_equiv_def] >> fs[]
  ) >>
  (* Compose: (s1+j1 -> s1) ∘ (s1 -> s2) ∘ (s2 -> s2+j2) via transitivity *)
  `!r1 r2 r3.
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r2 /\
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r2 r3 ==>
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r3` by
    (match_mp_tac lift_result_trans_proof >>
     metis_tac[state_equiv_trans, execution_equiv_trans]) >>
  metis_tac[]
QED


Theorem bridge_ok_case[local]:
  !f non_terms term bb fresh fuel ctx s s1' s2'.
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    term.inst_opcode <> INVOKE /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      non_terms /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP f non_terms)) /\
    f term = [term] /\
    (!x. MEM (Var x) term.inst_operands ==> x NOTIN fresh) /\
    run_insts fuel ctx non_terms s = OK s1' /\
    run_insts fuel ctx (FLAT (MAP f non_terms)) s = OK s2' /\
    state_equiv fresh s1' s2' /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx
        (bb with bb_instructions := FLAT (MAP f bb.bb_instructions)) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    FLAT (MAP f bb.bb_instructions)` >>
  `bb'.bb_instructions = FLAT (MAP f non_terms) ++ [term]` by
    (unabbrev_all_tac >> simp[MAP_APPEND, FLAT_APPEND]) >>
  `s1'.vs_inst_idx = 0` by
    (qspecl_then [`fuel`, `ctx`, `non_terms`, `s`, `s1'`]
       mp_tac run_insts_preserves_idx >> simp[]) >>
  `s2'.vs_inst_idx = 0` by
    (qspecl_then [`fuel`, `ctx`, `FLAT (MAP f non_terms)`, `s`, `s2'`]
       mp_tac run_insts_preserves_idx >> simp[]) >>
  qspecl_then [`non_terms`, `fuel`, `ctx`, `bb`, `s`, `0`, `s1'`]
    mp_tac exec_block_skip_prefix >>
  (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1])) >>
  qspecl_then [`FLAT (MAP f non_terms)`, `fuel`, `ctx`, `bb'`, `s`, `0`, `s2'`]
    mp_tac exec_block_skip_prefix >>
  (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1])) >>
  rpt strip_tac >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  fs[] >>
  qpat_x_assum `exec_block _ _ bb s = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `exec_block _ _ bb' s = _` (fn th => REWRITE_TAC [th]) >>
  qspecl_then [`fuel`, `ctx`, `bb`, `LENGTH non_terms`, `term`, `s1'`]
    mp_tac exec_block_at_terminator >>
  (impl_tac >- simp[get_instruction_def, EL_APPEND2]) >>
  qspecl_then [`fuel`, `ctx`, `bb'`, `LENGTH (FLAT (MAP f non_terms))`,
               `term`, `s2'`]
    mp_tac exec_block_at_terminator >>
  (impl_tac >- simp[get_instruction_def, EL_APPEND2]) >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ bb _ = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `exec_block _ _ bb' _ = _` (fn th => REWRITE_TAC [th]) >>
  irule terminator_step_equiv >> simp[]
QED


Theorem bridge_non_ok_case[local]:
  !f non_terms term bb fresh fuel ctx s.
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      non_terms /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP f non_terms)) /\
    f term = [term] /\
    (!s1'. run_insts fuel ctx non_terms s <> OK s1') /\
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_insts fuel ctx non_terms s)
      (run_insts fuel ctx (FLAT (MAP f non_terms)) s) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx
        (bb with bb_instructions := FLAT (MAP f bb.bb_instructions)) s)
Proof
  rpt strip_tac
  >> `valid_state_rel (state_equiv fresh) (execution_equiv fresh)` by
       simp[state_equiv_execution_equiv_valid_state_rel_proof]
  >> qabbrev_tac `bb' = bb with bb_instructions :=
       FLAT (MAP f bb.bb_instructions)`
  >> `bb'.bb_instructions = FLAT (MAP f non_terms) ++ [term]` by
       (unabbrev_all_tac >> simp[MAP_APPEND, FLAT_APPEND])
  >> `!s2'. run_insts fuel ctx (FLAT (MAP f non_terms)) s <> OK s2'` by
       (CCONTR_TAC >> fs[] >>
        Cases_on `run_insts fuel ctx non_terms s` >> fs[lift_result_def])
  >> qspecl_then [`state_equiv fresh`, `execution_equiv fresh`,
                   `non_terms`] mp_tac run_insts_lift_exec_block
  >> (impl_tac >- simp[])
  >> disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `0`] mp_tac)
  >> simp[]
  >> (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1]))
  >> strip_tac
  >> qspecl_then [`state_equiv fresh`, `execution_equiv fresh`,
                   `FLAT (MAP f non_terms)`] mp_tac run_insts_lift_exec_block
  >> (impl_tac >- simp[])
  >> disch_then (qspecl_then [`fuel`, `ctx`, `bb'`, `s`, `0`] mp_tac)
  >> simp[]
  >> (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1]))
  >> strip_tac
  >> `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality]
  >> fs[]
  (* Chain: bb ← orig → trans → bb'.
     All three are non-OK, so case-split on result constructors *)
  >> Cases_on `run_insts fuel ctx non_terms s`
  >> fs[lift_result_def]
  >> Cases_on `exec_block fuel ctx bb s`
  >> fs[lift_result_def]
  >> Cases_on `run_insts fuel ctx (FLAT (MAP f non_terms)) s`
  >> fs[lift_result_def]
  >> Cases_on `exec_block fuel ctx bb' s` >> fs[lift_result_def]
  >> metis_tac[execution_equiv_sym, execution_equiv_trans]
QED


Theorem flat_map_same_start_block_bridge:
  !f non_terms term bb fresh P.
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    term.inst_opcode <> INVOKE /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      non_terms /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP f non_terms)) /\
    f term = [term] /\
    (!x. MEM (Var x) term.inst_operands ==> x NOTIN fresh) /\
    (!fuel ctx s. P s ==>
       lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
         (run_insts fuel ctx non_terms s)
         (run_insts fuel ctx (FLAT (MAP f non_terms)) s))
    ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ P s ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAP f bb.bb_instructions)) s)
Proof
  rpt strip_tac
  >> `FLAT (MAP f bb.bb_instructions) = FLAT (MAP f non_terms) ++ [term]`
       by simp[MAP_APPEND, FLAT_APPEND]
  >> first_x_assum (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  >> (impl_tac >- fs[]) >> strip_tac
  >> reverse (Cases_on `?s1'. run_insts fuel ctx non_terms s = OK s1'`)
  >- (fs[] >>
      qspecl_then [`f`, `non_terms`, `term`, `bb`, `fresh`, `fuel`, `ctx`, `s`]
        mp_tac bridge_non_ok_case >> simp[])
  >> fs[]
  >> Cases_on `run_insts fuel ctx (FLAT (MAP f non_terms)) s`
  >> fs[lift_result_def]
  >> qspecl_then [`f`, `non_terms`, `term`, `bb`, `fresh`, `fuel`, `ctx`,
       `s`, `s1'`, `v`] mp_tac bridge_ok_case
  >> simp[]
QED


Theorem flat_map_term_structure:
  !f bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) /\
    (!inst. f inst <> []) /\
    (f (LAST bb.bb_instructions) = [LAST bb.bb_instructions]) /\
    (!inst. MEM inst bb.bb_instructions /\
            ~is_terminator inst.inst_opcode ==>
      EVERY (\i. ~is_terminator i.inst_opcode) (f inst)) ==>
    let bb' = bb with bb_instructions :=
                FLAT (MAP f bb.bb_instructions) in
    bb'.bb_instructions <> [] /\
    is_terminator (LAST bb'.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb'.bb_instructions /\
         is_terminator (EL k bb'.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb'.bb_instructions))
Proof
  rw[LET_THM]
  >- ((* Non-empty *)
    Cases_on `bb.bb_instructions` >> fs[] >>
    simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
    Cases_on `f h` >> fs[])
  >- ((* LAST preserved *)
    `FLAT (MAP f bb.bb_instructions) =
     FLAT (MAP f (FRONT bb.bb_instructions)) ++
     f (LAST bb.bb_instructions)` by (
      `bb.bb_instructions =
       FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
        by metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
      pop_assum (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
        (ONCE_REWRITE_CONV [th]))))) >>
      simp[MAP_APPEND, FLAT_APPEND]) >>
    `FLAT (MAP f bb.bb_instructions) <> []` by
      (Cases_on `bb.bb_instructions` >> fs[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
       Cases_on `f h` >> fs[]) >>
    simp[LAST_APPEND_NOT_NIL])
  >- ((* Only-last terminator *)
    qabbrev_tac `insts = bb.bb_instructions` >>
    qabbrev_tac `result = FLAT (MAP f insts)` >>
    (* Step 1: decompose result = prefix ++ [LAST] *)
    `result = FLAT (MAP f (FRONT insts)) ++ [LAST insts]` by (
      `insts = FRONT insts ++ [LAST insts]`
        by metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
      simp[Abbr `result`] >>
      pop_assum (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
        (ONCE_REWRITE_CONV [th]))))) >>
      simp[MAP_APPEND, FLAT_APPEND]) >>
    (* Step 2: FRONT elements are non-terminators (EL-based, no ALL_DISTINCT) *)
    `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT insts)` by (
      simp[EVERY_EL] >> rpt strip_tac >>
      `n < LENGTH insts` by
        (imp_res_tac rich_listTheory.LENGTH_FRONT >> fs[]) >>
      `EL n (FRONT insts) = EL n insts` by
        (irule rich_listTheory.FRONT_EL >> simp[]) >>
      simp[] >> CCONTR_TAC >> fs[] >>
      `n = PRE (LENGTH insts)` by (first_x_assum irule >> simp[]) >>
      imp_res_tac rich_listTheory.LENGTH_FRONT >> fs[]) >>
    (* Step 3: EVERY non-term for FLAT (MAP f (FRONT insts)) *)
    `EVERY (\i. ~is_terminator i.inst_opcode)
       (FLAT (MAP f (FRONT insts)))` suffices_by (
      strip_tac >>
      `LENGTH result = LENGTH (FLAT (MAP f (FRONT insts))) + 1` suffices_by (
        strip_tac >>
        Cases_on `k < LENGTH (FLAT (MAP f (FRONT insts)))`
        >- (fs[EL_APPEND1, EVERY_EL] >>
            first_x_assum (qspec_then `k` mp_tac) >> simp[])
        >- fs[]) >>
      simp[]) >>
    simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
    imp_res_tac MEM_FRONT_NOT_NIL >>
    fs[EVERY_MEM] >> res_tac >> fs[EVERY_MEM])
QED


Theorem bb_wf_decompose_weak:
  !bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) ==>
    let non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
                      bb.bb_instructions in
    let term = LAST bb.bb_instructions in
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) non_terms
Proof
  rw[LET_THM]
  >- (
    qabbrev_tac `insts = bb.bb_instructions` >>
    `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT insts)` by (
      simp[EVERY_EL] >> rpt strip_tac >>
      `LENGTH (FRONT insts) = PRE (LENGTH insts)` by
        simp[rich_listTheory.FRONT_LENGTH] >>
      `n < PRE (LENGTH insts)` by fs[] >>
      `EL n (FRONT insts) = EL n insts` by
        (irule rich_listTheory.FRONT_EL >> simp[]) >>
      fs[] >> CCONTR_TAC >> fs[] >>
      `n = PRE (LENGTH insts)` by (first_x_assum irule >> simp[]) >>
      fs[]) >>
    `FILTER (\i. ~is_terminator i.inst_opcode) insts = FRONT insts` by (
      `insts = FRONT insts ++ [LAST insts]` by
        metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
      pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[FILTER_APPEND_DISTRIB, FILTER, FILTER_EQ_ID]) >>
    simp[] >> metis_tac[SNOC_LAST_FRONT, SNOC_APPEND])
  >- simp[EVERY_FILTER]
QED


Theorem bb_wf_decompose:
  !bb. bb_well_formed bb ==>
    let non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
                      bb.bb_instructions in
    let term = LAST bb.bb_instructions in
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) non_terms
Proof
  rpt strip_tac >>
  mp_tac (Q.SPEC `bb` bb_wf_decompose_weak) >>
  fs[bb_well_formed_def]
QED

