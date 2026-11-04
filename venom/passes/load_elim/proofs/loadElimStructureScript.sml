Theory loadElimStructure
Ancestors
  analysisSimDefs passSimulationProps venomWf venomInst venomExecSemantics list rich_list sorting

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

Theorem le_phi_insert_wf:
  !xs bb ps.
    bb_well_formed (bb with bb_instructions := xs) /\
    EVERY (\i. i.inst_opcode = PHI) ps ==>
    bb_well_formed (bb with bb_instructions :=
      TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs)
Proof
  Induct_on `xs` >- simp[le_wf_empty] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (Cases_on `xs = []`
      >- gvs[le_wf_singleton, is_terminator_def] >>
      gvs[le_wf_cons, phi_prefix_length_def] >>
      `bb_well_formed (bb with bb_instructions :=
        TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs)`
        by (first_x_assum irule >> simp[]) >>
      `TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs <> []`
        by (strip_tac >> gvs[le_wf_empty]) >>
      simp[le_wf_cons, is_terminator_def]) >>
  simp[phi_prefix_length_def] >>
  irule le_wf_phi_prefix >> simp[]
QED

Theorem le_phi_insert_nonempty:
  !xs bb ps.
    bb_well_formed (bb with bb_instructions := xs) /\
    EVERY (\i. i.inst_opcode = PHI) ps ==>
    TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs <> []
Proof
  metis_tac[le_phi_insert_wf, le_wf_empty]
QED

Theorem le_phi_insert_last:
  !xs bb ps.
    bb_well_formed (bb with bb_instructions := xs) /\
    EVERY (\i. i.inst_opcode = PHI) ps ==>
    LAST (TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs) =
    LAST xs
Proof
  Induct_on `xs` >- simp[le_wf_empty] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (Cases_on `xs = []`
      >- gvs[le_wf_singleton, is_terminator_def] >>
      gvs[le_wf_cons, phi_prefix_length_def] >>
      `TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs <> []`
        by metis_tac[le_phi_insert_nonempty] >>
      simp[LAST_CONS_cond] >> metis_tac[]) >>
  simp[phi_prefix_length_def, LAST_APPEND, LAST_CONS_cond]
QED

Theorem le_phi_insert_succs:
  !xs bb ps.
    bb_well_formed (bb with bb_instructions := xs) /\
    EVERY (\i. i.inst_opcode = PHI) ps ==>
    bb_succs (bb with bb_instructions :=
      TAKE (phi_prefix_length xs) xs ++ ps ++ DROP (phi_prefix_length xs) xs) =
    bb_succs (bb with bb_instructions := xs)
Proof
  rpt strip_tac >>
  `xs <> []` by (strip_tac >> gvs[le_wf_empty]) >>
  drule_all le_phi_insert_nonempty >> strip_tac >>
  drule_all le_phi_insert_last >> strip_tac >>
  qmatch_asmsub_abbrev_tac `LAST ys = LAST xs` >>
  Cases_on `ys` >> Cases_on `xs` >> gvs[bb_succs_def]
QED

(* The corresponding simulation fact is a non-exported Triviality.
   Export an update-form boundary for structural consumers. *)
Theorem le_abtp_eq:
  !bottom result prepend f bb.
    analysis_block_transform_prepend bottom result prepend f bb =
    (analysis_block_transform bottom result f bb) with bb_instructions :=
      TAKE (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions)
           (analysis_block_transform bottom result f bb).bb_instructions ++
      prepend bb.bb_label ++
      DROP (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions)
           (analysis_block_transform bottom result f bb).bb_instructions
Proof
  simp[analysis_block_transform_prepend_def, analysis_block_transform_def]
QED

Theorem le_abtp_wf:
  !bottom result prepend f bb.
    bb_well_formed (analysis_block_transform bottom result f bb) /\
    EVERY (\i. i.inst_opcode = PHI) (prepend bb.bb_label) ==>
    bb_well_formed (analysis_block_transform_prepend bottom result prepend f bb)
Proof
  rpt strip_tac >> rewrite_tac[le_abtp_eq] >>
  irule le_phi_insert_wf >> simp[]
QED

Theorem le_abtp_succs:
  !bottom result prepend f bb.
    bb_well_formed (analysis_block_transform bottom result f bb) /\
    EVERY (\i. i.inst_opcode = PHI) (prepend bb.bb_label) ==>
    bb_succs (analysis_block_transform_prepend bottom result prepend f bb) =
    bb_succs (analysis_block_transform bottom result f bb)
Proof
  rpt strip_tac >> rewrite_tac[le_abtp_eq] >>
  qmatch_asmsub_abbrev_tac `bb_well_formed bt` >>
  qspecl_then [`bt.bb_instructions`, `bt`, `prepend bb.bb_label`]
    mp_tac le_phi_insert_succs >> simp[]
QED

Theorem le_global_insert_perm:
  !bs old added cut g.
    PERM
      (FLAT (MAP (\b. FLAT (MAP g
        (TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)))) bs))
      (FLAT (MAP (\b. FLAT (MAP g (old b))) bs) ++
       FLAT (MAP (\b. FLAT (MAP g (added b))) bs))
Proof
  Induct_on `bs` >- simp[] >>
  rpt gen_tac >> pure_rewrite_tac[MAP, FLAT] >>
  first_x_assum (qspecl_then [`old`, `added`, `cut`, `g`] assume_tac) >>
  irule PERM_TRANS >>
  qexists_tac `(FLAT (MAP g (old h)) ++ FLAT (MAP g (added h))) ++
    (FLAT (MAP (\b. FLAT (MAP g (old b))) bs) ++
     FLAT (MAP (\b. FLAT (MAP g (added b))) bs))` >>
  conj_tac
  >- (CONV_TAC (DEPTH_CONV BETA_CONV) >>
      metis_tac[PERM_APPEND_IFF, PERM_TRANS, le_insert_flat_map_perm]) >>
  metis_tac[PERM_APPEND_IFF, PERM_APPEND, PERM_REFL, APPEND_ASSOC]
QED

Theorem le_global_insert_distinct:
  !bs old added cut g.
    ALL_DISTINCT
      (FLAT (MAP (\b. FLAT (MAP g
        (TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)))) bs)) <=>
    ALL_DISTINCT
      (FLAT (MAP (\b. FLAT (MAP g (old b))) bs) ++
       FLAT (MAP (\b. FLAT (MAP g (added b))) bs))
Proof
  metis_tac[le_global_insert_perm, ALL_DISTINCT_PERM]
QED

Theorem le_global_insert_distinct_sufficient:
  !bs old added cut g.
    ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP g (old b))) bs)) /\
    ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP g (added b))) bs)) /\
    (!x. MEM x (FLAT (MAP (\b. FLAT (MAP g (old b))) bs)) ==>
         ~MEM x (FLAT (MAP (\b. FLAT (MAP g (added b))) bs))) ==>
    ALL_DISTINCT
      (FLAT (MAP (\b. FLAT (MAP g
        (TAKE (cut b) (old b) ++ added b ++ DROP (cut b) (old b)))) bs))
Proof
  simp[le_global_insert_distinct, ALL_DISTINCT_APPEND]
QED

Theorem le_abtp_global_distinct:
  !bs bottom result prepend f (g:instruction -> 'b list).
    ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP g
      (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions)) bs)) <=>
    ALL_DISTINCT
      (FLAT (MAP (\bb. FLAT (MAP g
        (analysis_block_transform bottom result f bb).bb_instructions)) bs) ++
       FLAT (MAP (\bb. FLAT (MAP g (prepend bb.bb_label))) bs))
Proof
  rpt gen_tac >>
  pure_rewrite_tac[le_abtp_eq, basic_block_accfupds, combinTheory.K_THM] >>
  qspecl_then [`bs`,
    `\bb. (analysis_block_transform bottom result f bb).bb_instructions`,
    `\bb. prepend bb.bb_label`,
    `\bb. phi_prefix_length
      (analysis_block_transform bottom result f bb).bb_instructions`] mp_tac
    (INST_TYPE [alpha |-> ``:basic_block``, beta |-> ``:instruction``,
                gamma |-> beta] le_global_insert_distinct) >>
  disch_then (qspec_then `g` mp_tac) >> simp[]
QED
