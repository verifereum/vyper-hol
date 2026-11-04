Theory loadElimStructure
Ancestors
  analysisSimDefs passSimulationProps venomWf venomInst list rich_list sorting

(* Insertion at an arbitrary cut: provenance and uniqueness do not depend
   on the cut, nor on the instruction analysis. *)
Theorem le_insert_mem:
  !n xs ys x.
    MEM x (TAKE n xs ++ ys ++ DROP n xs) <=>
    MEM x xs \/ MEM x ys
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`n`, `xs`] TAKE_DROP) >>
  metis_tac[MEM_APPEND]
QED

Theorem le_insert_perm:
  !n xs ys.
    PERM (TAKE n xs ++ ys ++ DROP n xs) (xs ++ ys)
Proof
  rpt gen_tac >>
  `PERM (TAKE n xs ++ ys ++ DROP n xs)
        ((TAKE n xs ++ DROP n xs) ++ ys)` by
    metis_tac[PERM_APPEND_IFF, PERM_APPEND, PERM_REFL, APPEND_ASSOC] >>
  gvs[TAKE_DROP]
QED

Theorem le_insert_distinct:
  !n xs ys.
    ALL_DISTINCT (TAKE n xs ++ ys ++ DROP n xs) <=>
    ALL_DISTINCT (xs ++ ys)
Proof
  metis_tac[le_insert_perm, ALL_DISTINCT_PERM]
QED

Theorem le_abtp_mem:
  !bottom result prepend f bb inst.
    MEM inst (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions <=>
    MEM inst (analysis_block_transform bottom result f bb).bb_instructions \/
    MEM inst (prepend bb.bb_label)
Proof
  rpt gen_tac >>
  simp[analysis_block_transform_prepend_def, analysis_block_transform_def] >>
  qmatch_goalsub_abbrev_tac `TAKE n xs` >>
  `MEM inst xs <=> MEM inst (TAKE n xs) \/ MEM inst (DROP n xs)` by
    metis_tac[TAKE_DROP, MEM_APPEND] >>
  metis_tac[]
QED

Theorem le_insert_flat_map_perm:
  !f n xs ys.
    PERM (FLAT (MAP f (TAKE n xs ++ ys ++ DROP n xs)))
         (FLAT (MAP f xs) ++ FLAT (MAP f ys))
Proof
  rpt gen_tac >>
  irule PERM_TRANS >>
  qexists_tac `FLAT (MAP f (xs ++ ys))` >>
  conj_tac >- metis_tac[le_insert_perm, PERM_MAP, PERM_FLAT] >>
  simp[MAP_APPEND, FLAT_APPEND]
QED

Theorem le_insert_flat_map_distinct:
  !f n xs ys.
    ALL_DISTINCT (FLAT (MAP f (TAKE n xs ++ ys ++ DROP n xs))) <=>
    ALL_DISTINCT (FLAT (MAP f xs) ++ FLAT (MAP f ys))
Proof
  metis_tac[le_insert_flat_map_perm, ALL_DISTINCT_PERM]
QED

Theorem le_wf_empty:
  !bb. ~bb_well_formed (bb with bb_instructions := [])
Proof
  simp[bb_well_formed_def]
QED

Theorem le_wf_singleton:
  !bb h. bb_well_formed (bb with bb_instructions := [h]) <=>
         is_terminator h.inst_opcode
Proof
  simp[bb_well_formed_def]
QED

Theorem le_forall_num[local]:
  (!n:num. P n) <=> P 0 /\ !n. P (SUC n)
Proof
  eq_tac >- simp[] >> strip_tac >> gen_tac >>
  Cases_on `n` >> simp[]
QED

Theorem le_phi_cons[local]:
  (!i j. i < j /\ j < SUC (LENGTH xs) /\
         (EL j (h::xs)).inst_opcode = PHI ==>
         (EL i (h::xs)).inst_opcode = PHI) <=>
  ((!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
          (EL i xs).inst_opcode = PHI) /\
   (h.inst_opcode = PHI \/ EVERY (\i. i.inst_opcode <> PHI) xs))
Proof
  simp[Once le_forall_num] >>
  simp[Once le_forall_num] >>
  CONV_TAC (LAND_CONV (RAND_CONV (BINDER_CONV (HO_REWR_CONV le_forall_num)))) >>
  simp[EVERY_EL] >> metis_tac[]
QED

Theorem le_wf_cons:
  !bb h xs. xs <> [] ==>
    (bb_well_formed (bb with bb_instructions := h::xs) <=>
     ~is_terminator h.inst_opcode /\
     bb_well_formed (bb with bb_instructions := xs) /\
     (h.inst_opcode = PHI \/ EVERY (\i. i.inst_opcode <> PHI) xs))
Proof
  rpt gen_tac >> strip_tac >>
  simp[bb_well_formed_def, LAST_CONS_cond, EVERY_EL] >>
  simp[Once le_forall_num] >>
  `LENGTH xs = SUC (PRE (LENGTH xs))` by (Cases_on `xs` >> gvs[]) >>
  `!i. (SUC i = LENGTH xs <=> i = PRE (LENGTH xs))` by decide_tac >>
  simp[le_phi_cons, EVERY_EL] >> metis_tac[]
QED

Theorem le_wf_phi_prefix:
  !ps bb xs.
    EVERY (\i. i.inst_opcode = PHI) ps /\
    bb_well_formed (bb with bb_instructions := xs) ==>
    bb_well_formed (bb with bb_instructions := ps ++ xs)
Proof
  Induct_on `ps` >- simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `xs <> []` by (strip_tac >> gvs[le_wf_empty]) >>
  `ps ++ xs <> []` by simp[] >>
  simp[le_wf_cons, is_terminator_def] >>
  first_x_assum irule >> simp[]
QED
