Theory staticAbortOptPruneUnreachableZeroOrigin
Ancestors
  asmSplice codegenSymRel asmSymSem asmSem alist finite_map rich_list list arithmetic
  staticAbortProtectedTraceCoverage asmSymOwnCode asmSymPcOwn asmSpliceOwn

(* A concrete lift cannot introduce a symbolic stack item.  Its byte tags
   come from the supplied map, independently of the concrete result. *)
Theorem lift_preserves_zero_absence[local]:
  sym_lift k labs st r = SymOK st' /\
  ~MEM (Lab l 0) st.sym_stack /\
  (!i j. FLOOKUP labs i <> SOME (l,0,j)) ==>
  ~MEM (Lab l 0) st'.sym_stack /\
  (!i j. FLOOKUP st'.sym_mem_labels i <> SOME (l,0,j))
Proof
  Cases_on `r` >> rw[sym_lift_def] >> gvs[MEM_MAP] >>
  metis_tac[MEM_DROP_IMP]
QED

Theorem concrete_preserves_zero_absence[local]:
  sym_step_concrete name st = SymOK st' /\
  ~MEM (Lab l 0) st.sym_stack /\
  (!i j. FLOOKUP st.sym_mem_labels i <> SOME (l,0,j)) ==>
  ~MEM (Lab l 0) st'.sym_stack /\
  (!i j. FLOOKUP st'.sym_mem_labels i <> SOME (l,0,j))
Proof
  simp[sym_step_concrete_def, AllCaseEqs()] >> strip_tac >>
  irule lift_preserves_zero_absence >>
  qpat_assum `sym_lift _ _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[mem_labels_clear_lookup]
QED

Theorem zero_absence_after_store_tags[local]:
  !i j.
    (l':string,d:num) <> (l,0) /\ (!a b. FLOOKUP labs a <> SOME (l,0,b)) ==>
    FLOOKUP (labs |++ GENLIST (\k. (k+off,(l',d,k))) n) i <> SOME (l,0,j)
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP (REVERSE (GENLIST (\k. (k+off,(l',d,k))) n)) i` >>
  gvs[FLOOKUP_FUPDATE_LIST] >>
  drule ALOOKUP_MEM >> simp[MEM_GENLIST] >> metis_tac[]
QED

Theorem zero_absence_prevents_load[local]:
  (!i j. FLOOKUP labs i <> SOME (l,0,j)) ==>
  mem_label_at labs off <> SOME (l,0)
Proof
  rw[mem_label_at_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem store_preserves_zero_absence[local]:
  sym_mstore st = SymOK st' /\
  ~MEM (Lab l 0) st.sym_stack /\
  (!i j. FLOOKUP st.sym_mem_labels i <> SOME (l,0,j)) ==>
  ~MEM (Lab l 0) st'.sym_stack /\
  (!i j. FLOOKUP st'.sym_mem_labels i <> SOME (l,0,j))
Proof
  simp[sym_mstore_def, AllCaseEqs(), Excl "GENLIST_NUMERALS"] >> strip_tac >>
  IF (qpat_assum `sym_step_concrete _ _ = _` (K ALL_TAC))
    (irule concrete_preserves_zero_absence >>
     qpat_assum `sym_step_concrete _ _ = _` (irule_at Any) >> simp[])
    ALL_TAC >>
  rename1 `_ = Lab other delta` >>
  `(other,delta) <> (l,0)` by (strip_tac >> gvs[Excl "GENLIST_NUMERALS"]) >>
  irule lift_preserves_zero_absence >>
  qpat_assum `sym_lift _ _ _ _ = _` (irule_at Any) >>
  simp[Excl "GENLIST_NUMERALS"] >>
  rpt gen_tac >> irule zero_absence_after_store_tags >> simp[]
QED

Theorem op_preserves_zero_absence[local]:
  sym_step_op p env name st = SymOK st' /\
  ~MEM (Lab l 0) st.sym_stack /\
  (!i j. FLOOKUP st.sym_mem_labels i <> SOME (l,0,j)) ==>
  ~MEM (Lab l 0) st'.sym_stack /\
  (!i j. FLOOKUP st'.sym_mem_labels i <> SOME (l,0,j))
Proof
  simp[sym_step_op_def, AllCaseEqs()] >> strip_tac >>
  IF (qpat_assum `sym_mstore _ = _` (K ALL_TAC))
    (irule store_preserves_zero_absence >>
     qpat_assum `sym_mstore _ = _` (irule_at Any) >> simp[])
    ALL_TAC >>
  gvs[sym_jump_def, sym_jumpi_def, sym_add_def, sym_mload_def,
      sym_codecopy_def, sym_dup_def, sym_swap_def, sym_push_lab_def,
      sym_set_stack_def, AllCaseEqs(), ADD_EQ_0] >>
  IF (qpat_assum `sym_step_concrete _ _ = _` (K ALL_TAC))
    (irule concrete_preserves_zero_absence >>
     qpat_assum `sym_step_concrete _ _ = _` (irule_at Any) >> simp[])
    ALL_TAC >>
  IF (qpat_assum `sym_lift _ _ _ _ = _` (K ALL_TAC))
    (irule lift_preserves_zero_absence >>
     qpat_assum `sym_lift _ _ _ _ = _` (irule_at Any) >>
     simp[] >> rpt strip_tac >> drule mem_labels_clear_lookup >> simp[])
    ALL_TAC
  >- (strip_tac >> gvs[] >> metis_tac[zero_absence_prevents_load])
  >- (`MEM (HD st.sym_stack) st.sym_stack`
        by (Cases_on `st.sym_stack` >> gvs[]) >>
      metis_tac[EL_MEM, MEM_LUPDATE_E]) >>
  metis_tac[EL_MEM]
QED

Theorem step_zero_origin[local]:
  sym_step p env inst st = SymOK st' /\
  (MEM (Lab l 0) st'.sym_stack \/
   (?i j. FLOOKUP st'.sym_mem_labels i = SOME (l,0,j))) ==>
  inst = AsmPushLabel l \/ inst = AsmPushOfst l 0 \/
  MEM (Lab l 0) st.sym_stack \/
  (?i j. FLOOKUP st.sym_mem_labels i = SOME (l,0,j))
Proof
  Cases_on `inst` >> simp[sym_step_def, sym_push_lab_def, sym_set_stack_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[op_preserves_zero_absence, lift_preserves_zero_absence]
QED

Theorem step_zero_origin_mode[local]:
  (if allow_own then sym_step_own p env own inst st else sym_step p env inst st) =
    SymOK st' /\
  (MEM (Lab l 0) st'.sym_stack \/
   (?i j. FLOOKUP st'.sym_mem_labels i = SOME (l,0,j))) ==>
  inst = AsmPushLabel l \/ inst = AsmPushOfst l 0 \/
  MEM (Lab l 0) st.sym_stack \/
  (?i j. FLOOKUP st.sym_mem_labels i = SOME (l,0,j))
Proof
  Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES]
  >- (Cases_on `inst = AsmOp "CODESIZE"`
      >- (gvs[sym_step_own_def, sym_step_op_own_def, sym_set_stack_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
      Cases_on `inst = AsmOp "CODECOPY"`
      >- (strip_tac >> spose_not_then strip_assume_tac >>
          gvs[sym_step_own_def, sym_step_op_own_def, sym_codecopy_own_def, AllCaseEqs()] >>
          `~MEM (Lab l 0) st.sym_stack` by simp[] >>
          qpat_assum `sym_lift _ _ st _ = SymOK st'`
            (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lift_preserves_zero_absence)) >>
          (impl_tac >- first_assum ACCEPT_TAC) >>
          (impl_tac >- metis_tac[mem_labels_clear_lookup]) >>
          metis_tac[]) >>
      simp[sym_step_own_eq] >> MATCH_ACCEPT_TAC step_zero_origin) >>
  MATCH_ACCEPT_TAC step_zero_origin
QED

(* Follow the last step of a successful prefix.  Memory byte tags must be
   included in the induction: MSTORE may preserve a label off-stack. *)
Theorem stopped_zero_origin_mode[local]:
  !n ss.
    sym_steps_mode allow_own q env own n (sym_init s) = SymOK ss /\
    (MEM (Lab l 0) ss.sym_stack \/
     (?i j. FLOOKUP ss.sym_mem_labels i = SOME (l,0,j))) ==>
    ?m u. m<n /\ sym_steps_mode allow_own q env own m (sym_init s) = SymOK u /\
      u.sym_base.as_pc<LENGTH q /\
      (EL u.sym_base.as_pc q = AsmPushLabel l \/
       EL u.sym_base.as_pc q = AsmPushOfst l 0)
Proof
  Induct >- simp[sym_steps_mode_zero, sym_init_def, MEM_MAP] >>
  gen_tac >> rewrite_tac[ADD1, sym_steps_mode_add] >>
  Cases_on `sym_steps_mode allow_own q env own n (sym_init s)` >> simp[] >>
  rename1 `sym_steps_mode allow_own q env own n (sym_init s) = SymOK u` >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `u.sym_base.as_pc < LENGTH q /\
   (if allow_own then sym_step_own q env own (EL u.sym_base.as_pc q) u
    else sym_step q env (EL u.sym_base.as_pc q) u) = SymOK ss`
    by (qpat_x_assum `sym_steps_mode allow_own q env own 1 u = SymOK ss` mp_tac >>
        simp_tac bool_ss [sym_steps_mode_ok_one]) >>
  `EL u.sym_base.as_pc q = AsmPushLabel l \/
   EL u.sym_base.as_pc q = AsmPushOfst l 0 \/
   MEM (Lab l 0) u.sym_stack \/
   (?i j. FLOOKUP u.sym_mem_labels i = SOME (l,0,j))`
    by metis_tac[step_zero_origin_mode]
  >- (qexistsl [`n`, `u`] >> simp[])
  >- (qexistsl [`n`, `u`] >> simp[]) >>
  qpat_x_assum `!x. _ ==> _` (qspec_then `u` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `m` (qx_choose_then `v` strip_assume_tac)) >>
  qexistsl [`m`, `v`] >> simp[] >> decide_tac
QED

Theorem stopped_lab_zero_producer_mode:
  sym_steps_mode allow_own q env own n (sym_init s) = SymOK ss /\ MEM (Lab l 0) ss.sym_stack ==>
  ?m u. m<n /\ sym_steps_mode allow_own q env own m (sym_init s) = SymOK u /\
    u.sym_base.as_pc<LENGTH q /\
    (EL u.sym_base.as_pc q = AsmPushLabel l \/
     EL u.sym_base.as_pc q = AsmPushOfst l 0)
Proof
  metis_tac[stopped_zero_origin_mode]
QED

Theorem stopped_lab_zero_producer:
  sym_steps q env n (sym_init s) = SymOK ss /\ MEM (Lab l 0) ss.sym_stack ==>
  ?m u. m<n /\ sym_steps q env m (sym_init s) = SymOK u /\
    u.sym_base.as_pc<LENGTH q /\
    (EL u.sym_base.as_pc q = AsmPushLabel l \/
     EL u.sym_base.as_pc q = AsmPushOfst l 0)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`]
    stopped_lab_zero_producer_mode |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
