(*
 * DFT Front Equivalence — FRONT decomposition lemma
 *
 * Key lemma: pseudos_prefix_front_decomposition
 * Under pseudos_prefix + bb_well_formed, FRONT bb_instructions =
 *   FILTER is_pseudo bb_instructions ++ FILTER (~is_pseudo/\~is_terminator) bb_instructions
 *)

Theory dftFrontEquiv
Ancestors
  venomWf venomInst list rich_list
Libs
  wordsLib BasicProvers

(* ===== Pseudos-prefix decomposition ===== *)

(* Terminators are never pseudo instructions *)
Triviality terminator_not_pseudo[simp]:
  !op. is_terminator op ==> ~is_pseudo op
Proof
  Cases_on `op` >> simp[is_terminator_def, is_pseudo_def]
QED

(* Generic: if all P-elements form a prefix of a list,
   then l = FILTER P l ++ FILTER (~P) l *)
Triviality prefix_filter_partition:
  !P l.
    (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    l = FILTER P l ++ FILTER (\x. ~P x) l
Proof
  gen_tac >> Induct_on `l`
  >- simp[]
  >> rpt strip_tac >> Cases_on `P h` >> simp[]
  >- (`!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)` by
        (rpt strip_tac >>
         first_x_assum (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[]) >>
      metis_tac[])
  >> `FILTER P l = []` by
       (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
        CCONTR_TAC >>
        `?n. n < LENGTH l /\ EL n l = x` by metis_tac[MEM_EL] >>
        first_x_assum (qspecl_then [`0`,`SUC n`] mp_tac) >> simp[EL_CONS]) >>
     `EVERY (\x. ~P x) l` by metis_tac[FILTER_EQ_NIL] >>
     simp[FILTER_EQ_ID]
QED

(* FILTER congruence: removing ~is_terminator when EVERY holds *)
Triviality FILTER_CONG_CONCRETE:
  !l. EVERY (\i. ~is_terminator i.inst_opcode) l ==>
    FILTER (\i. ~is_pseudo i.inst_opcode) l =
    FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) l
Proof
  simp[FILTER_EQ, EVERY_MEM]
QED

(* FILTER distributes over FRONT/LAST decomposition of a non-empty list *)
Triviality FILTER_APPEND_FRONT_LAST:
  !l P. l <> [] ==> FILTER P l = FILTER P (FRONT l) ++ FILTER P [LAST l]
Proof
  rpt strip_tac >>
  irule EQ_TRANS >>
  qexistsl [`FILTER P (FRONT l ++ [LAST l])`] >>
  conj_tac >- metis_tac[APPEND_FRONT_LAST] >>
  simp[FILTER_APPEND_DISTRIB]
QED

(* If only the last element of a non-empty list is a terminator, then FRONT has no terminators *)
Triviality front_no_terminators:
  !l. l <> [] /\
      (!i. i < LENGTH l /\ is_terminator (EL i l).inst_opcode ==> i = PRE (LENGTH l)) ==>
      EVERY (\i. ~is_terminator i.inst_opcode) (FRONT l)
Proof
  rpt strip_tac >>
  `!n. n < LENGTH (FRONT l) ==> ~is_terminator (EL n (FRONT l)).inst_opcode`
    suffices_by simp[EVERY_EL] >>
  gen_tac >> strip_tac >>
  `EL n (FRONT l) = EL n l` by metis_tac[FRONT_EL] >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `m = LENGTH l` >>
  `LENGTH (FRONT l) = PRE m` by (simp[Abbr `m`, FRONT_LENGTH]) >>
  `n < PRE m` by simp[] >>
  `n < m` by simp[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[Abbr `m`]
QED

(* Under pseudos_prefix and bb_well_formed, FRONT of instructions decomposes
   as pseudos followed by non-pseudo non-terminator instructions (block body) *)
Theorem pseudos_prefix_front_decomposition:
  !bb.
    pseudos_prefix bb /\ bb_well_formed bb ==>
    FRONT bb.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
      FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb.bb_instructions
Proof
  rpt strip_tac >>
  qpat_x_assum `bb_well_formed bb` (STRIP_ASSUME_TAC o REWRITE_RULE[bb_well_formed_def]) >>
  drule terminator_not_pseudo >> strip_tac >>
  `bb.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` by
    (ho_match_mp_tac prefix_filter_partition >> metis_tac[pseudos_prefix_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)` by
    metis_tac[front_no_terminators] >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions =
   FILTER (\i. is_pseudo i.inst_opcode) (FRONT bb.bb_instructions)` by
    (drule FILTER_APPEND_FRONT_LAST >> simp[]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions =
   FILTER (\i. ~is_pseudo i.inst_opcode) (FRONT bb.bb_instructions) ++
   [LAST bb.bb_instructions]` by
    (drule FILTER_APPEND_FRONT_LAST >> simp[]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb.bb_instructions =
   FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)` by
    (drule FILTER_APPEND_FRONT_LAST >> simp[]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) (FRONT bb.bb_instructions) =
   FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)` by
    metis_tac[FILTER_CONG_CONCRETE] >>
  metis_tac[APPEND_FRONT_LAST, APPEND_11, APPEND_ASSOC, APPEND_NIL]
QED
