Theory dftCanonicalDep
Ancestors
  dftDefs dftTopoSort dftStructural dftIdempotent dftPermSim
  dftWf dftFrontEquiv
  venomEffects venomWf venomInst
  passSharedProps passSharedDefs
  relation list rich_list sorting pred_set

(* === Inst-id-based membership: invariant under flip_operands === *)
Definition in_np_body_def:
  in_np_body bi x <=>
    MEM x.inst_id (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
End

(* Bridge: in_np_body can be derived from element-based MEM_FILTER *)
Triviality mem_np_filter_in_np_body:
  !bi x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) ==>
         in_np_body bi x
Proof
  rw[in_np_body_def, MEM_MAP, MEM_FILTER] >>
  qexists `x` >> simp[]
QED

(* === Data dependency: x uses a variable that y defines === *)
Definition data_dep_body_def:
  data_dep_body bi x y <=>
    ?v. MEM (Var v) x.inst_operands /\ MEM v y.inst_outputs /\
        in_np_body bi x /\
        in_np_body bi y
End

(* === from_barrier_dep: barrier x depends on all preceding non-phis === *)
Definition from_barrier_dep_def:
  from_barrier_dep bi x y <=>
    in_np_body bi x /\
    in_np_body bi y /\
    is_barrier x /\
    ?pfx sfx.
      MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)
        = pfx ++ [x.inst_id] ++ sfx /\
      MEM y.inst_id pfx
End

(* === on_barrier_dep: non-barrier x depends on the last barrier y before it === *)
Definition on_barrier_dep_def:
  on_barrier_dep bi x y <=>
    in_np_body bi x /\
    in_np_body bi y /\
    ~is_barrier x /\
    is_barrier y /\
    ?pfx sfx mid.
      FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ [mid] ++ sfx /\
      mid.inst_id = x.inst_id /\
      FILTER is_barrier pfx <> [] /\
      (LAST (FILTER is_barrier pfx)).inst_id = y.inst_id
End

(* canonical_dep: data deps + barrier ordering *)
Definition canonical_dep_def:
  canonical_dep bi x y <=>
    in_np_body bi x /\
    in_np_body bi y /\
    (data_dep_body bi x y \/
     from_barrier_dep bi x y \/
     on_barrier_dep bi x y)
End


(* data_dep_body is a sub-relation of canonical_dep *)
Theorem data_dep_body_imp_canonical_dep:
  !bi x y. data_dep_body bi x y ==> canonical_dep bi x y
Proof
  rw[canonical_dep_def, data_dep_body_def] >>
  simp[]
QED


(* ===== Structural properties ===== *)

(* Helper: y before barrier b implies from_barrier_dep *)
Theorem from_barrier_dep_intro:
  !bi b y pfx sfx.
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    is_barrier b /\ b <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx /\
    MEM y pfx ==>
    from_barrier_dep bi b y
Proof
  rpt strip_tac >> imp_res_tac mem_np_filter_in_np_body >>
  simp[from_barrier_dep_def] >>
  qexistsl_tac [`MAP (\i. i.inst_id) pfx`, `MAP (\i. i.inst_id) sfx`] >>
  simp[MAP_APPEND, MAP, MEM_MAP] >>
  qexists `y` >> simp[]
QED

(* Helper: barrier y after b implies from_barrier_dep(y,b) *)
Triviality barrier_y_before_b_intro:
  !bi b y pfx sfx ypfx ysfx.
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    is_barrier y /\ b <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx /\
    sfx = ypfx ++ y::ysfx ==>
    from_barrier_dep bi y b
Proof
  rpt strip_tac >> imp_res_tac mem_np_filter_in_np_body >>
  simp[from_barrier_dep_def] >>
  qexistsl_tac [`MAP (\i. i.inst_id) (pfx ++ b::ypfx)`,
                `MAP (\i. i.inst_id) ysfx`] >>
  simp[MAP_APPEND, APPEND_ASSOC, MEM_MAP] >>
  qexists `b` >> simp[MEM_APPEND]
QED

(* Helper: on_barrier_dep when last barrier = b *)
Triviality on_barrier_dep_last_is_b:
  !bi b y pfx sfx ypfx ysfx.
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    ~is_barrier y /\ is_barrier b /\ b <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx /\
    sfx = ypfx ++ y::ysfx /\
    FILTER is_barrier (pfx ++ b::ypfx) <> [] /\
    LAST (FILTER is_barrier (pfx ++ b::ypfx)) = b ==>
    on_barrier_dep bi y b
Proof
  rpt gen_tac >> strip_tac >> imp_res_tac mem_np_filter_in_np_body >>
  simp[on_barrier_dep_def] >>
  qexistsl_tac [`pfx ++ b::ypfx`, `ysfx`, `y`] >>
  simp[APPEND_ASSOC]
QED

(* Helper: canonical_dep y → last barrier b' via on_barrier_dep *)
Triviality cd_y_last_barrier:
  !bi y b' pfx sfx.
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    ~is_barrier y /\ is_barrier b' /\ b' <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ y::sfx /\
    FILTER is_barrier pfx <> [] /\
    LAST (FILTER is_barrier pfx) = b' ==>
    canonical_dep bi y b'
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac mem_np_filter_in_np_body >>
  simp[canonical_dep_def] >>
  disj2_tac >> disj2_tac >>
  simp[on_barrier_dep_def] >>
  qexistsl_tac [`pfx`, `sfx`, `y`] >> simp[]
QED


(* Helper: canonical_dep b' → b via from_barrier_dep, b appears before b' in list *)
Triviality cd_b_via_barrier:
  !bi b b' pfx bpfx bsfx rest.
    MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    is_barrier b' /\ b' <> b /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::bpfx ++ b'::bsfx ++ rest ==>
    canonical_dep bi b' b
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac mem_np_filter_in_np_body >>
  simp[canonical_dep_def] >>
  disj2_tac >> disj1_tac >>
  simp[from_barrier_dep_def] >>
  qexistsl_tac [`MAP (\i. i.inst_id) (pfx ++ b::bpfx)`,
                `MAP (\i. i.inst_id) (bsfx ++ rest)`] >>
  simp[MAP_APPEND, APPEND_ASSOC, MEM_MAP] >>
  qexists `b` >> simp[MEM_APPEND]
QED


Triviality barrier_not_eq_non_barrier:
  !x y. is_barrier x /\ ~is_barrier y ==> x <> y
Proof
  metis_tac[]
QED

Triviality on_barrier_dep_last_neq_b:
  !bi b y pfx sfx ypfx ysfx bpfx bsfx.
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    ~is_barrier y /\ is_barrier b /\ b <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx /\
    sfx = ypfx ++ y::ysfx /\
    FILTER is_barrier (pfx ++ b::ypfx) <> [] /\
    LAST (FILTER is_barrier (pfx ++ b::ypfx)) <> b /\
    MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (pfx ++ b::ypfx) /\
    is_barrier (LAST (FILTER is_barrier (pfx ++ b::ypfx))) /\
    ypfx = bpfx ++ LAST (FILTER is_barrier (pfx ++ b::ypfx))::bsfx ==>
    TC (canonical_dep bi) y b
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `b' = LAST (FILTER is_barrier (pfx ++ b::ypfx))` >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by (
    qpat_x_assum `FILTER _ _ = pfx ++ b::sfx` SUBST1_TAC >>
    qpat_x_assum `sfx = _` SUBST1_TAC >>
    qpat_x_assum `ypfx = _` SUBST1_TAC >>
    simp[MEM_APPEND]) >>
  `b' <> y` by metis_tac[barrier_not_eq_non_barrier] >>
  match_mp_tac (CONJUNCT2 (SPEC_ALL TC_RULES)) >>
  qexists `b'` >> conj_tac
  >- (match_mp_tac TC_SUBSET >>
      match_mp_tac cd_y_last_barrier >>
      qexistsl_tac [`pfx ++ b::ypfx`, `ysfx`] >>
      simp[])
  >- (match_mp_tac TC_SUBSET >>
      match_mp_tac cd_b_via_barrier >>
      qexistsl_tac [`pfx`, `bpfx`, `bsfx`, `y::ysfx`] >>
      fs[APPEND_ASSOC])
QED

(* Helper: if P h and LAST of FILTER P (l1++h::l2) ≠ h, then LAST is in l2 *)
Triviality last_filter_not_head_mem_tail:
  !P l1 h l2.
    P h /\ LAST (FILTER P (l1 ++ h::l2)) <> h ==>
    MEM (LAST (FILTER P (l1 ++ h::l2))) l2
Proof
  rpt strip_tac >>
  qabbrev_tac `fl = FILTER P (l1 ++ h::l2)` >>
  qabbrev_tac `fl1 = FILTER P l1` >>
  qabbrev_tac `fl2 = FILTER P l2` >>
  `fl = fl1 ++ h::fl2`
    by (qunabbrev_tac `fl` >> qunabbrev_tac `fl1` >> qunabbrev_tac `fl2` >>
       simp[FILTER_APPEND_DISTRIB]) >>
  Cases_on `fl2 = []`
  >- (`fl = fl1 ++ [h]` by fs[] >>
     fs[LAST_APPEND_NOT_NIL, LAST_CONS])
  >- (`LAST fl = LAST fl2` by fs[LAST_APPEND_NOT_NIL, LAST_CONS] >>
     `MEM (LAST fl2) fl2` by metis_tac[LAST_MEM] >>
     `MEM (LAST fl2) l2` by metis_tac[MEM_FILTER] >>
     fs[])
QED

Triviality filter_prefix_not_last:
  !P l pre y sfx e.
    ALL_DISTINCT l /\ FILTER P l = pre ++ [y] ++ sfx /\
    MEM e pre /\ P e /\ MEM e l /\
    (!k. k < LENGTH l /\ is_terminator (EL k l).inst_opcode ==>
         k = PRE (LENGTH l)) /\
    l <> [] /\ is_terminator e.inst_opcode ==>
    F
Proof
  rpt strip_tac >>
  `?n. n < LENGTH pre /\ EL n pre = e` by metis_tac[MEM_EL] >>
  `n < LENGTH (FILTER P l)` by
    (pop_assum kall_tac >>
     qpat_assum `FILTER P l = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  `LENGTH pre < LENGTH (FILTER P l)` by
    (qpat_assum `FILTER P l = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  `EL n (FILTER P l) = e /\
   EL (LENGTH pre) (FILTER P l) = y` by
    (asm_rewrite_tac[] >> conj_tac >>
     simp[EL_APPEND_EQN]) >>
  drule_all filter_el_mono >>
  disch_then (qx_choosel_then [`ne`, `ny`] strip_assume_tac) >>
  `ne = PRE (LENGTH l)` by
    (first_x_assum irule >> gvs[]) >>
  decide_tac
QED

(* Barriers are TC-comparable to all under canonical_dep *)
Theorem canonical_dep_barrier_tc_connected:
  !bi b y.
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    b <> y /\ is_barrier b ==>
    TC (canonical_dep bi) b y \/ TC (canonical_dep bi) y b
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac mem_np_filter_in_np_body >>
  `?pfx sfx. FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx`
    by (fs[MEM_SPLIT] >> metis_tac[]) >>
  `MEM y (pfx ++ b::sfx)` by metis_tac[MEM] >>
  Cases_on `MEM y pfx`
  >- (* Case 1: y before b *)
   (`from_barrier_dep bi b y` by metis_tac[from_barrier_dep_intro] >>
    `canonical_dep bi b y` by simp[canonical_dep_def] >>
    metis_tac[TC_SUBSET])
  >- (* Case 2: y after b *)
   (`MEM y sfx` by metis_tac[MEM_APPEND, MEM] >>
    `?ypfx ysfx. sfx = ypfx ++ y::ysfx` by metis_tac[MEM_SPLIT] >>
    Cases_on `is_barrier y`
    >- (* Case 2a: y is a barrier *)
     (`from_barrier_dep bi y b` by metis_tac[barrier_y_before_b_intro] >>
      `canonical_dep bi y b` by simp[canonical_dep_def] >>
      metis_tac[TC_SUBSET])
    >- (* Case 2b: y not a barrier *)
     (disj2_tac >>
      `FILTER is_barrier (pfx ++ b::ypfx) <> []`
        by (simp[FILTER_NEQ_NIL] >> qexists `b` >> simp[MEM_FILTER]) >>
      `MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (FILTER is_barrier (pfx ++ b::ypfx))`
        by simp[LAST_MEM] >>
      `is_barrier (LAST (FILTER is_barrier (pfx ++ b::ypfx))) /\
       MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (pfx ++ b::ypfx)`
        by metis_tac[MEM_FILTER] >>
      Cases_on `LAST (FILTER is_barrier (pfx ++ b::ypfx)) = b`
      >- (* b' = b *)
       (`on_barrier_dep bi y b` by metis_tac[on_barrier_dep_last_is_b] >>
        `canonical_dep bi y b` by simp[canonical_dep_def] >>
        metis_tac[TC_SUBSET])
      >- (* b' ≠ b *)
       (`MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) ypfx`
          by metis_tac[last_filter_not_head_mem_tail] >>
        `?bpfx bsfx. ypfx = bpfx ++ LAST (FILTER is_barrier (pfx ++ b::ypfx))::bsfx`
          by metis_tac[MEM_SPLIT] >>
        metis_tac[on_barrier_dep_last_neq_b])))
QED
(* Corollary: barriers are TC-comparable to all in body under canonical_dep *)
Theorem canonical_dep_barrier_connected_body:
  !bi b y.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    ~is_terminator b.inst_opcode /\ ~is_terminator y.inst_opcode /\
    b <> y /\ is_barrier b ==>
    TC (canonical_dep bi) b y \/ TC (canonical_dep bi) y b
Proof
  rpt strip_tac >>
  metis_tac[canonical_dep_barrier_tc_connected]
QED

(* TC-incomparable pairs under canonical_dep cannot contain a barrier *)
Theorem canonical_tc_incomp_not_barrier:
  !bi x y.
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    x <> y /\
    ~TC (canonical_dep bi) x y /\ ~TC (canonical_dep bi) y x ==>
    ~is_barrier x /\ ~is_barrier y
Proof
  rpt strip_tac >>
  `~is_barrier x` by metis_tac[canonical_dep_barrier_tc_connected] >>
  `~is_barrier y` by metis_tac[canonical_dep_barrier_tc_connected]
QED

(* TC-incomp under canonical_dep implies no data dep in either direction *)
Theorem canonical_tc_incomp_no_data_dep:
  !bi x y.
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    x <> y /\
    ~TC (canonical_dep bi) x y /\ ~TC (canonical_dep bi) y x ==>
    ~data_dep_body bi x y /\ ~data_dep_body bi y x
Proof
  rpt strip_tac >>
  imp_res_tac mem_np_filter_in_np_body >>
  `!a b. data_dep_body bi a b /\ in_np_body bi a /\ in_np_body bi b ==> canonical_dep bi a b`
    by metis_tac[canonical_dep_def] >>
  metis_tac[TC_SUBSET]
QED

(* Helper: reshuffle canonical_dep + MEM-FBODY conjuncts.
   With the inst-id-based canonical_dep, MEM FBODY can no longer be derived
   from canonical_dep alone (flipped comparators may not be in bi as elements).
   Call sites always have MEM FBODY as a hypothesis, so we just pass it through. *)
Triviality canonical_dep_mem_fbody:
  !bi x y.
    canonical_dep bi x y /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) ==>
    canonical_dep bi x y /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)
Proof
  simp[]
QED

(* Helper: in FBODY implies in FILTER ~is_pseudo *)
Triviality fbody_mem_np:
  !bi x.
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) ==>
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    ~is_terminator x.inst_opcode
Proof
  simp[MEM_FILTER]
QED

(* Helper: element in FILTER ~is_pseudo and before y in the filter list is non-terminator
   when terminators can only be the last element of bi *)
Triviality filter_np_before_not_terminator:
  !bi e pre y sfx.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pre ++ [y] ++ sfx /\
    MEM e pre /\ ~is_pseudo e.inst_opcode /\ MEM e bi /\
    is_terminator e.inst_opcode ==>
    F
Proof
  rpt strip_tac >>
  irule filter_prefix_not_last >>
  qexistsl_tac [`\i. ~is_pseudo i.inst_opcode`, `e`, `bi`, `pre`, `sfx`, `y`] >>
  BETA_TAC >> asm_rewrite_tac[]
QED

(* Helper: element b' in flat FILTER list before y cannot be a terminator
   when terminators are only the last element of bi *)
Triviality last_barrier_not_terminator:
  !bi b' b pfx bpfx bsfx y ysfx.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ [b] ++ bpfx ++ [b'] ++ bsfx ++ [y] ++ ysfx /\
    MEM b' (pfx ++ [b] ++ bpfx ++ [b'] ++ bsfx) /\
    ~is_pseudo b'.inst_opcode /\ MEM b' bi /\
    is_terminator b'.inst_opcode ==>
    F
Proof
  rpt strip_tac >>
  irule filter_np_before_not_terminator >>
  qexistsl_tac [`bi`, `b'`, `pfx ++ [b] ++ bpfx ++ [b'] ++ bsfx`, `ysfx`, `y`] >>
  simp[APPEND_ASSOC, MEM_APPEND]
QED

(* Helper: in the restricted TC proof, b' (the last barrier before y)
   cannot be a terminator because it appears before y in FILTER list *)
Triviality restricted_last_barrier_not_terminator:
  !bi b y pfx sfx ypfx ysfx bpfx bsfx.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    ~is_barrier y /\ is_barrier b /\ b <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx /\
    sfx = ypfx ++ y::ysfx /\
    FILTER is_barrier (pfx ++ b::ypfx) <> [] /\
    LAST (FILTER is_barrier (pfx ++ b::ypfx)) <> b /\
    MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (pfx ++ b::ypfx) /\
    is_barrier (LAST (FILTER is_barrier (pfx ++ b::ypfx))) /\
    is_terminator (LAST (FILTER is_barrier (pfx ++ b::ypfx))).inst_opcode /\
    ypfx = bpfx ++ LAST (FILTER is_barrier (pfx ++ b::ypfx))::bsfx ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `b' = LAST (FILTER is_barrier (pfx ++ b::ypfx))` >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by (
    qpat_x_assum `FILTER _ _ = pfx ++ b::sfx` SUBST1_TAC >>
    qpat_x_assum `sfx = _` SUBST1_TAC >>
    qpat_x_assum `ypfx = _` SUBST1_TAC >>
    simp[MEM_APPEND]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bi =
     pfx ++ [b] ++ bpfx ++ [b'] ++ bsfx ++ [y] ++ ysfx`
    by (qpat_x_assum `FILTER _ _ = pfx ++ b::sfx` SUBST1_TAC >>
        qpat_x_assum `sfx = _` SUBST1_TAC >>
        qpat_x_assum `ypfx = _` SUBST1_TAC >>
        simp[APPEND_ASSOC]) >>
  `MEM b' (pfx ++ [b] ++ bpfx ++ [b'] ++ bsfx)` by simp[MEM_APPEND, APPEND_ASSOC] >>
  `~is_pseudo b'.inst_opcode /\ MEM b' bi` by
    (qpat_x_assum `MEM b' (FILTER _ _)` mp_tac >> simp[MEM_FILTER]) >>
  metis_tac[last_barrier_not_terminator]
QED

(* Helper: restricted TC for b'!=b case using transitivity through last barrier b' *)
Triviality restricted_tc_last_barrier_neq_b:
  !bi b y pfx sfx ypfx ysfx bpfx bsfx.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    ~is_barrier y /\ is_barrier b /\ b <> y /\
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx /\
    sfx = ypfx ++ y::ysfx /\
    FILTER is_barrier (pfx ++ b::ypfx) <> [] /\
    LAST (FILTER is_barrier (pfx ++ b::ypfx)) <> b /\
    MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (pfx ++ b::ypfx) /\
    is_barrier (LAST (FILTER is_barrier (pfx ++ b::ypfx))) /\
    ypfx = bpfx ++ LAST (FILTER is_barrier (pfx ++ b::ypfx))::bsfx ==>
    TC (\a c. canonical_dep bi a c /\
             MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
             MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) y b
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `b' = LAST (FILTER is_barrier (pfx ++ b::ypfx))` >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by (
    qpat_x_assum `FILTER _ _ = pfx ++ b::sfx` SUBST1_TAC >>
    qpat_x_assum `sfx = _` SUBST1_TAC >>
    qpat_x_assum `ypfx = _` SUBST1_TAC >>
    simp[MEM_APPEND]) >>
  `b' <> y` by metis_tac[barrier_not_eq_non_barrier] >>
  `~is_terminator b'.inst_opcode` by metis_tac[restricted_last_barrier_not_terminator] >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)` by
    (qpat_x_assum `MEM b' (FILTER _ _)` mp_tac >> simp[MEM_FILTER]) >>
  `canonical_dep bi y b'` by
    (match_mp_tac cd_y_last_barrier >>
     qexistsl_tac [`pfx ++ b::ypfx`, `ysfx`] >> simp[]) >>
  `canonical_dep bi b' b` by
    (match_mp_tac cd_b_via_barrier >>
     qexistsl_tac [`pfx`, `bpfx`, `bsfx`, `y::ysfx`] >>
     fs[APPEND_ASSOC]) >>
  qabbrev_tac `R = \a c. canonical_dep bi a c /\
                  MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
                  MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)` >>
  `TC R y b'` by
    (irule TC_SUBSET >> simp[Abbr `R`] >> BETA_TAC >>
     metis_tac[canonical_dep_mem_fbody]) >>
  `TC R b' b` by
    (irule TC_SUBSET >> simp[Abbr `R`] >> BETA_TAC >>
     metis_tac[canonical_dep_mem_fbody]) >>
  `transitive (TC R)` by simp[TC_TRANSITIVE] >>
  metis_tac[transitive_def]
QED

(* Barriers are TC-comparable to all within the non-terminator body under canonical_dep *)
Theorem canonical_dep_barrier_tc_connected_restricted:
  !bi b y.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    b <> y /\ is_barrier b ==>
    TC (\a c. canonical_dep bi a c /\
             MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
             MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) b y \/
    TC (\a c. canonical_dep bi a c /\
             MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
             MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) y b
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac fbody_mem_np >>
  `?pfx sfx. FILTER (\i. ~is_pseudo i.inst_opcode) bi = pfx ++ b::sfx`
    by (fs[MEM_SPLIT] >> metis_tac[]) >>
  `MEM y (pfx ++ b::sfx)` by metis_tac[MEM] >>
  Cases_on `MEM y pfx`
  >- (* Case 1: y before b *)
   (disj1_tac >>
    irule TC_SUBSET >> BETA_TAC >>
    `canonical_dep bi b y` by
      metis_tac[from_barrier_dep_intro, canonical_dep_def, mem_np_filter_in_np_body] >>
    simp[canonical_dep_mem_fbody])
  >- (* Case 2: y after b *)
   (`MEM y sfx` by metis_tac[MEM_APPEND, MEM] >>
    `?ypfx ysfx. sfx = ypfx ++ y::ysfx` by metis_tac[MEM_SPLIT] >>
    Cases_on `is_barrier y`
    >- (* Case 2a: y is a barrier *)
     (disj2_tac >>
      irule TC_SUBSET >> BETA_TAC >>
      `canonical_dep bi y b` by
        metis_tac[barrier_y_before_b_intro, canonical_dep_def, mem_np_filter_in_np_body] >>
      simp[canonical_dep_mem_fbody])
    >- (* Case 2b: y not a barrier *)
     (disj2_tac >>
      `FILTER is_barrier (pfx ++ b::ypfx) <> []`
        by (simp[FILTER_NEQ_NIL] >> qexists `b` >> simp[MEM_FILTER]) >>
      `MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (FILTER is_barrier (pfx ++ b::ypfx))`
        by simp[LAST_MEM] >>
      `is_barrier (LAST (FILTER is_barrier (pfx ++ b::ypfx))) /\
       MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) (pfx ++ b::ypfx)`
        by metis_tac[MEM_FILTER] >>
      Cases_on `LAST (FILTER is_barrier (pfx ++ b::ypfx)) = b`
      >- (* b' = b *)
       (irule TC_SUBSET >> BETA_TAC >>
        `canonical_dep bi y b` by
          metis_tac[on_barrier_dep_last_is_b, canonical_dep_def, mem_np_filter_in_np_body] >>
        simp[canonical_dep_mem_fbody])
      >- (* b' != b *)
       (`MEM (LAST (FILTER is_barrier (pfx ++ b::ypfx))) ypfx`
          by metis_tac[last_filter_not_head_mem_tail] >>
        `?bpfx bsfx. ypfx = bpfx ++ LAST (FILTER is_barrier (pfx ++ b::ypfx))::bsfx`
          by metis_tac[MEM_SPLIT] >>
        metis_tac[restricted_tc_last_barrier_neq_b])))
QED

(* Bridge: MEM (Var v) ops iff MEM v (operand_vars ops) *)
Triviality mem_operand_vars_iff[local]:
  !ops v. MEM v (operand_vars ops) <=> MEM (Var v) ops
Proof
  Induct >> simp[operand_vars_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[operand_var_def, operand_vars_def]
QED

(* data_dep_body is inst_id/set-equivariant *)
Triviality data_dep_body_inst_id_equiv[local]:
  !bi x y x' y'.
    in_np_body bi x /\ in_np_body bi y /\
    in_np_body bi x' /\ in_np_body bi y' /\
    set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands) /\
    set x.inst_outputs = set x'.inst_outputs /\
    set y.inst_outputs = set y'.inst_outputs ==>
    (data_dep_body bi x y <=> data_dep_body bi x' y')
Proof
  simp[data_dep_body_def, mem_operand_vars_iff, EXTENSION]
QED

(* from_barrier_dep is inst_id/barrier-equivariant *)
Triviality from_barrier_dep_inst_id_equiv[local]:
  !bi x y x' y'.
    from_barrier_dep bi x y /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id /\
    (is_barrier x = is_barrier x') ==>
    from_barrier_dep bi x' y'
Proof
  rpt strip_tac >> fs[from_barrier_dep_def, in_np_body_def] >>
  qexistsl_tac [`pfx`,`sfx`] >> simp[]
QED

(* from_barrier_dep reverse *)
Triviality from_barrier_dep_inst_id_equiv_rev[local]:
  !bi x y x' y'.
    from_barrier_dep bi x' y' /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id /\
    (is_barrier x = is_barrier x') ==>
    from_barrier_dep bi x y
Proof
  rpt strip_tac >> fs[from_barrier_dep_def, in_np_body_def] >>
  qexistsl_tac [`pfx`,`sfx`] >> simp[]
QED

(* on_barrier_dep is inst_id/barrier-equivariant *)
Triviality on_barrier_dep_inst_id_equiv[local]:
  !bi x y x' y'.
    on_barrier_dep bi x y /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id /\
    (~is_barrier x = ~is_barrier x') /\
    (is_barrier y = is_barrier y') ==>
    on_barrier_dep bi x' y'
Proof
  rpt strip_tac >> fs[on_barrier_dep_def, in_np_body_def] >>
  qexistsl_tac [`pfx`,`sfx`,`mid`] >> simp[]
QED

(* on_barrier_dep reverse *)
Triviality on_barrier_dep_inst_id_equiv_rev[local]:
  !bi x y x' y'.
    on_barrier_dep bi x' y' /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id /\
    (~is_barrier x = ~is_barrier x') /\
    (is_barrier y = is_barrier y') ==>
    on_barrier_dep bi x y
Proof
  rpt strip_tac >>
  `is_barrier x' = is_barrier x` by metis_tac[] >>
  irule on_barrier_dep_inst_id_equiv >>
  qexistsl_tac [`x'`,`y'`] >> simp[]
QED

(* canonical_dep is invariant under inst_id and operand/output set-equivalence *)
Theorem canonical_dep_inst_id_equiv:
  !bi x y x' y'.
    ALL_DISTINCT (MAP (\i. i.inst_id)
                    (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    in_np_body bi x /\ in_np_body bi y /\
    in_np_body bi x' /\ in_np_body bi y' /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id /\
    set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands) /\
    set x.inst_outputs = set x'.inst_outputs /\
    set y.inst_outputs = set y'.inst_outputs /\
    is_barrier x = is_barrier x' /\
    is_barrier y = is_barrier y' ==>
    (canonical_dep bi x y <=> canonical_dep bi x' y')
Proof
  rpt strip_tac >>
  `(in_np_body bi x <=> in_np_body bi x') /\
   (in_np_body bi y <=> in_np_body bi y')`
    by (conj_tac >> fs[in_np_body_def] >> metis_tac[]) >>
  eq_tac >> rpt strip_tac >> fs[canonical_dep_def]
  >- metis_tac[data_dep_body_inst_id_equiv]
  >- metis_tac[from_barrier_dep_inst_id_equiv]
  >- metis_tac[on_barrier_dep_inst_id_equiv]
  >- metis_tac[data_dep_body_inst_id_equiv]
  >- metis_tac[from_barrier_dep_inst_id_equiv]
  >- metis_tac[on_barrier_dep_inst_id_equiv]
QED
