(*
 * SSA Pipeline Structural Characterization
 *
 * Proves that make_ssa_fn produces blocks with a PHI prefix
 * followed by renamed original instructions (opcodes preserved).
 *
 * Main export: pipeline_block_structure
 *)

Theory ssaPipeline
Ancestors
  makeSsaDefs cfgTransformProps venomExecProofs
  list rich_list alist string pair venomState venomInst venomWf

(* ==========================================================================
   Part 1: PHI extension — add_phi_nodes only prepends PHI instructions
   ========================================================================== *)

Definition phi_extends_def:
  phi_extends bbs bbs' <=>
    LENGTH bbs' = LENGTH bbs /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    !j. j < LENGTH bbs ==>
      ?phis.
        (EL j bbs').bb_instructions =
          phis ++ (EL j bbs).bb_instructions /\
        EVERY (\i. i.inst_opcode = PHI) phis
End

Theorem phi_extends_refl:
  !bbs. phi_extends bbs bbs
Proof
  rw[phi_extends_def]
QED

Theorem phi_extends_trans[local]:
  !bbs1 bbs2 bbs3.
    phi_extends bbs1 bbs2 /\ phi_extends bbs2 bbs3 ==>
    phi_extends bbs1 bbs3
Proof
  rw[phi_extends_def] >>
  `j < LENGTH bbs2` by DECIDE_TAC >>
  res_tac >> qexists_tac `phis ++ phis'` >> gvs[EVERY_APPEND]
QED

Theorem insert_phi_map_labels[local]:
  !bbs f phi.
    MAP (\bb. bb.bb_label)
      (MAP (\bb. if bb.bb_label = f
                 then insert_phi_at_block phi bb else bb) bbs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> rw[] >>
  `MAP (\bb. bb.bb_label)
    (MAP (\bb. if bb.bb_label = f then insert_phi_at_block phi bb else bb)
       bbs) = MAP (\bb. bb.bb_label) bbs` by metis_tac[] >>
  rw[insert_phi_at_block_def]
QED

Theorem insert_phi_el_extend[local]:
  !bbs f phi j.
    phi.inst_opcode = PHI /\ j < LENGTH bbs ==>
    ?phis.
      (EL j (MAP (\bb. if bb.bb_label = f
                       then insert_phi_at_block phi bb else bb) bbs)).bb_instructions =
      phis ++ (EL j bbs).bb_instructions /\
      EVERY (\i. i.inst_opcode = PHI) phis
Proof
  Induct >> rw[] >> Cases_on `j` >> rw[EL]
  >- (Cases_on `h.bb_label = f` >> rw[insert_phi_at_block_def] >>
      qexists_tac `[phi]` >> rw[])
  >> gvs[]
QED

Theorem map_insert_phi_extends[local]:
  !bbs f phi.
    phi.inst_opcode = PHI ==>
    phi_extends bbs
      (MAP (\bb. if bb.bb_label = f
                 then insert_phi_at_block phi bb else bb) bbs)
Proof
  rw[phi_extends_def] >-
  rw[insert_phi_map_labels] >>
  metis_tac[insert_phi_el_extend]
QED

Theorem process_frontiers_phi_extends:
  !fs var pred_map live_in bbs rest has_phi bbs' rest' has_phi' bbs0.
    process_frontiers var pred_map live_in bbs rest has_phi fs =
      (bbs', rest', has_phi') /\
    phi_extends bbs0 bbs ==>
    phi_extends bbs0 bbs'
Proof
  Induct >> rw[process_frontiers_def] >>
  TRY (first_x_assum match_mp_tac) >>
  TRY (metis_tac[] >> NO_TAC) >>
  (* Live case: existential witness is the MAP'd bbs *)
  qexistsl_tac [`var`, `pred_map`, `live_in`,
    `MAP (\bb. if bb.bb_label = h
               then insert_phi_at_block
                 (build_phi_inst var
                   (case ALOOKUP pred_map h of SOME ps => ps | NONE => []))
                 bb
               else bb) bbs`,
    `h::rest`, `h::has_phi`, `rest'`, `has_phi'`] >>
  simp[] >>
  irule phi_extends_trans >>
  qexists_tac `bbs` >> rw[] >>
  irule map_insert_phi_extends >>
  rw[build_phi_inst_def]
QED

Theorem insert_phis_for_var_phi_extends:
  !var dom_frontiers pred_map live_in bbs wl hp bbs0.
    phi_extends bbs0 bbs ==>
    phi_extends bbs0
      (insert_phis_for_var var dom_frontiers pred_map live_in bbs wl hp)
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum irule >>
  irule process_frontiers_phi_extends >>
  metis_tac[]
QED

Theorem add_phi_nodes_phi_extends:
  !dom_frontiers pred_map live_in bbs defs.
    phi_extends bbs
      (add_phi_nodes dom_frontiers pred_map live_in bbs defs)
Proof
  rw[add_phi_nodes_def] >>
  qspec_tac (`bbs`, `bbs`) >>
  Induct_on `defs` >> rw[FOLDL, phi_extends_refl] >>
  PairCases_on `h` >> simp[] >>
  irule phi_extends_trans >>
  qexists_tac `insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 []` >>
  conj_tac >-
  (irule insert_phis_for_var_phi_extends >> rw[phi_extends_refl]) >>
  first_x_assum irule
QED

(* Added PHIs have inst_outputs = [var] where var is the variable being PHI'd.
   We trace this through the same process_frontiers → insert_phis_for_var →
   add_phi_nodes chain as phi_extends. *)

(* process_frontiers only adds build_phi_inst var, which has outputs = [var] *)
Theorem process_frontiers_phi_outputs:
  !fs var pred_map live_in bbs rest has_phi bbs' rest' has_phi'.
    process_frontiers var pred_map live_in bbs rest has_phi fs =
      (bbs', rest', has_phi') ==>
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs').bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        inst.inst_outputs = [var] /\ inst.inst_opcode = PHI
Proof
  Induct >> rw[process_frontiers_def]
  (* Case 1: MEM h has_phi — skip, bbs unchanged *)
  >- metis_tac[]
  >- metis_tac[]
  (* Case 2: not live — skip, bbs unchanged *)
  >- metis_tac[]
  >- metis_tac[]
  (* Case 3: live — insert_phi_at_block + recurse *)
  >> (
    qabbrev_tac `bbs_map = MAP (\bb. if bb.bb_label = h
       then insert_phi_at_block
         (build_phi_inst var
           (case ALOOKUP pred_map h of SOME ps => ps | NONE => []))
         bb else bb) bbs` >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    (* Case split: is inst in bbs_map or not? *)
    Cases_on `MEM inst (EL j bbs_map).bb_instructions`
    >- (
      (* inst is in bbs_map but not in bbs — added by MAP *)
      `EL j bbs_map = (
         if (EL j bbs).bb_label = h
         then insert_phi_at_block
           (build_phi_inst var
             (case ALOOKUP pred_map h of SOME ps => ps | NONE => []))
           (EL j bbs)
         else EL j bbs)` by
        simp[Abbr `bbs_map`, EL_MAP] >>
      Cases_on `(EL j bbs).bb_label = h` >> gvs[insert_phi_at_block_def] >>
      gvs[build_phi_inst_def])
    >- (
      (* inst not in bbs_map — IH gives result *)
      first_x_assum drule >> disch_then drule >>
      disch_then drule >> simp[]))
QED

(* insert_phis_for_var only adds build_phi_inst var *)
Theorem insert_phis_for_var_phi_outputs:
  !var dom_frontiers pred_map live_in bbs wl hp.
    !j. j < LENGTH bbs ==>
      !inst. MEM inst
        (EL j (insert_phis_for_var var dom_frontiers pred_map
                 live_in bbs wl hp)).bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        inst.inst_outputs = [var] /\ inst.inst_opcode = PHI
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `process_frontiers _ _ _ bbs1 _ _ _ = (bbs2, _, _)` >>
  `j < LENGTH bbs2` by (
    drule process_frontiers_phi_extends >>
    disch_then (qspec_then `bbs1` mp_tac) >>
    (impl_tac >- (simp[phi_extends_refl])) >>
    simp[phi_extends_def]) >>
  Cases_on `MEM inst (EL j bbs2).bb_instructions` >> (
    TRY (
      (* inst in bbs2 but not in bbs1 — added by process_frontiers *)
      drule process_frontiers_phi_outputs >>
      disch_then (qspec_then `j` mp_tac) >> simp[] >>
      disch_then drule >> simp[] >> NO_TAC) >>
    (* inst not in bbs2 — IH gives result *)
    first_x_assum drule >> disch_then drule >>
    disch_then drule >> simp[])
QED

(* add_phi_nodes: every added PHI has inst_outputs = [var]
   where var is in MAP FST defs *)
Theorem add_phi_nodes_phi_outputs:
  !dom_frontiers pred_map live_in bbs defs.
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in bbs defs in
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs1).bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        ?var. inst.inst_outputs = [var] /\
              MEM var (MAP FST defs) /\
              inst.inst_opcode = PHI
Proof
  simp_tac std_ss [LET_THM, add_phi_nodes_def] >>
  ntac 3 gen_tac >>
  Induct_on `defs` >> rw[FOLDL] >>
  PairCases_on `h` >> FULL_SIMP_TAC std_ss [] >> BETA_TAC >>
  qabbrev_tac `bbs_mid = insert_phis_for_var h0 dom_frontiers pred_map
    live_in bbs h1 []` >>
  `LENGTH bbs_mid = LENGTH bbs` by (
    `phi_extends bbs bbs_mid` by (
      simp[Abbr `bbs_mid`] >>
      irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
    gvs[phi_extends_def]) >>
  Cases_on `MEM inst (EL j bbs_mid).bb_instructions`
  >- (
    (* inst in bbs_mid but not in bbs — added by insert_phis_for_var *)
    `inst.inst_outputs = [h0] /\ inst.inst_opcode = PHI` by (
      mp_tac (Q.SPECL [`h0`, `dom_frontiers`, `pred_map`, `live_in`,
        `bbs`, `h1`, `[]:(string list)`]
        insert_phis_for_var_phi_outputs) >>
      disch_then (qspec_then `j` mp_tac) >> simp[Abbr `bbs_mid`] >>
      disch_then drule >> simp[]) >>
    qexists_tac `h0` >> simp[])
  >- (
    (* inst not in bbs_mid — IH gives result *)
    first_x_assum (qspecl_then [`bbs_mid`, `j`] mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then drule >> simp[] >>
    strip_tac >> qexists_tac `var` >> simp[])
QED

(* compute_defs produces colon_free variable names *)
Triviality block_assignments_colon_free:
  !bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions ==>
       EVERY colon_free (block_assignments bb)
Proof
  rw[block_assignments_def, EVERY_MEM, MEM_nub, MEM_FLAT, MEM_MAP,
     PULL_EXISTS] >>
  metis_tac[EVERY_MEM]
QED

Triviality alist_update_or_prepend_preserves_fst:
  !k f d acc.
    P k /\ EVERY (\p. P (FST p)) acc ==>
    EVERY (\p. P (FST p)) (alist_update_or_prepend k f d acc)
Proof
  Induct_on `acc` >> simp[alist_update_or_prepend_def] >>
  rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[alist_update_or_prepend_def] >>
  Cases_on `h0 = k` >> gvs[]
QED

Triviality foldr_aup_preserves_fst:
  !vars f d acc.
    EVERY P vars /\ EVERY (\p. P (FST p)) acc ==>
    EVERY (\p. P (FST p))
      (FOLDR (\var acc. alist_update_or_prepend var f d acc) acc vars)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  irule alist_update_or_prepend_preserves_fst >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem compute_defs_colon_free:
  !bbs.
    EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs) bb.bb_instructions)
      bbs ==>
    EVERY (\p. colon_free (FST p)) (compute_defs bbs)
Proof
  Induct >> simp[compute_defs_def] >> rpt strip_tac >> simp[LET_THM] >>
  irule foldr_aup_preserves_fst >> simp[] >>
  irule block_assignments_colon_free >> simp[]
QED

(* ==========================================================================
   Part 2: blocks_rel — general block-relation framework

   blocks_rel R bbs bbs' says: every block in bbs' has a corresponding block
   in bbs (at the same label) satisfying R.

   Both opcodes_preserved and succs_preserved are instances.
   ========================================================================== *)

Definition blocks_rel_def:
  blocks_rel R bbs bbs' <=>
    !lbl bb'. lookup_block lbl bbs' = SOME bb' ==>
      ?bb. lookup_block lbl bbs = SOME bb /\ R bb bb'
End

Triviality blocks_rel_refl:
  (!bb. R bb bb) ==> blocks_rel R bbs bbs
Proof
  rw[blocks_rel_def] >> metis_tac[]
QED

Triviality blocks_rel_trans:
  (!a b c. R a b /\ R b c ==> R a c) ==>
  blocks_rel R bbs1 bbs2 /\ blocks_rel R bbs2 bbs3 ==>
  blocks_rel R bbs1 bbs3
Proof
  rw[blocks_rel_def] >> res_tac >> res_tac >> metis_tac[]
QED

(* ==========================================================================
   Part 3: Per-instruction lemmas for rename_block_insts
   ========================================================================== *)

(* rename_block_insts preserves length *)
Theorem rename_block_insts_length:
  !insts rs.
    LENGTH (SND (rename_block_insts rs insts)) = LENGTH insts
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

(* rename_inst preserves opcode *)
Triviality rename_inst_opcode_preserved:
  !rs inst. (SND (rename_inst rs inst)).inst_opcode = inst.inst_opcode
Proof
  rw[rename_inst_def, LET_THM] >> pairarg_tac >> gvs[]
QED

(* rename_block_insts preserves opcodes *)
Theorem rename_block_insts_opcodes:
  !insts rs j.
    j < LENGTH insts ==>
    (EL j (SND (rename_block_insts rs insts))).inst_opcode =
      (EL j insts).inst_opcode
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `j` >> gvs[]
  >- metis_tac[rename_inst_opcode_preserved, pairTheory.SND]
  >- metis_tac[pairTheory.SND]
QED

(* rename_block_insts element-wise *)
Theorem rename_block_insts_el:
  !insts rs j.
    j < LENGTH insts ==>
    EL j (SND (rename_block_insts rs insts)) =
      SND (rename_inst (FST (rename_block_insts rs (TAKE j insts)))
                       (EL j insts))
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `j` >> gvs[rename_block_insts_def, LET_THM]
  >> pairarg_tac >> gvs[] >>
  metis_tac[pairTheory.SND, pairTheory.FST]
QED

(* rename_block_insts step *)
Theorem rename_block_insts_step:
  !insts rs j. j < LENGTH insts ==>
    FST (rename_block_insts rs (TAKE (SUC j) insts)) =
    FST (rename_inst (FST (rename_block_insts rs (TAKE j insts))) (EL j insts))
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `j` >> gvs[rename_block_insts_def, LET_THM]
  >> pairarg_tac >> gvs[] >>
  metis_tac[pairTheory.FST]
QED

(* rename_operands preserves get_label for each operand *)
Triviality rename_operands_get_label:
  !rs ops. MAP get_label (rename_operands rs ops) = MAP get_label ops
Proof
  Induct_on `ops` >>
  rw[rename_operands_def] >>
  Cases_on `h` >> rw[rename_operands_def, get_label_def]
QED

(* rename_inst preserves get_successors *)
Theorem rename_inst_get_successors:
  !rs inst. get_successors (SND (rename_inst rs inst)) = get_successors inst
Proof
  rw[get_successors_def, rename_inst_opcode_preserved] >>
  rw[rename_inst_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  simp[rename_operands_get_label]
QED

(* rename_block_insts preserves LAST *)
Theorem rename_block_insts_last:
  !rs insts. insts <> [] ==>
    ?rs'. LAST (SND (rename_block_insts rs insts)) =
          SND (rename_inst rs' (LAST insts))
Proof
  Induct_on `insts` >> rw[] >>
  Cases_on `insts`
  >- (
    (* Base: [h] *)
    simp[rename_block_insts_def, LET_THM] >>
    pairarg_tac >> simp[] >>
    qexists_tac `rs` >> simp[]
  ) >> (
    (* Step: h :: h' :: t, so rename gives inst' :: rest' *)
    simp[Once rename_block_insts_def, LET_THM] >>
    pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
    `rest' <> []` by
      (qsuff_tac `LENGTH rest' = SUC (LENGTH t)`
       >- (Cases_on `rest'` >> simp[]) >>
       metis_tac[rename_block_insts_length, pairTheory.SND,
                 listTheory.LENGTH]) >>
    simp[LAST_DEF] >>
    first_x_assum (qspec_then `rs'` mp_tac) >> simp[] >>
    disch_then strip_assume_tac >>
    gvs[LAST_DEF] >> metis_tac[]
  )
QED

(* ==========================================================================
   Part 4: Lookup helpers
   ========================================================================== *)

Theorem lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >> gvs[] >>
  first_x_assum irule >> gvs[lookup_block_def]
QED

Theorem lookup_block_MEM[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >> gvs[] >>
  disj2_tac >> first_x_assum irule >> gvs[lookup_block_def] >>
  metis_tac[]
QED

Theorem lookup_block_EL[local]:
  !bbs n.
    n < LENGTH bbs /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block (EL n bbs).bb_label bbs = SOME (EL n bbs)
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
  Cases_on `n` >> gvs[FIND_thm, MEM_MAP]
  >- (`MEM (EL n' bbs) bbs` by metis_tac[MEM_EL] >> metis_tac[])
  >- (first_x_assum (qspec_then `n'` mp_tac) >>
      rw[lookup_block_def])
QED

Triviality lookup_block_MEM_SOME:
  !bbs bb.
    MEM bb bbs /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    lookup_block bb.bb_label bbs = SOME bb
Proof
  Induct >> rw[lookup_block_def, FIND_thm] >> gvs[MEM_MAP] >>
  `bb.bb_label <> h.bb_label` by metis_tac[] >>
  simp[FIND_thm, GSYM lookup_block_def]
QED

Theorem phi_extends_lookup:
  !bbs bbs' bb.
    phi_extends bbs bbs' /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    MEM bb bbs ==>
    ?bb_mid.
      lookup_block bb.bb_label bbs' = SOME bb_mid /\
      ?phis.
        bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
        EVERY (\i. i.inst_opcode = PHI) phis
Proof
  rw[phi_extends_def] >>
  `?n. n < LENGTH bbs /\ EL n bbs = bb` by metis_tac[MEM_EL] >>
  qexists_tac `EL n bbs'` >> gvs[] >>
  `n < LENGTH bbs'` by gvs[] >>
  `(EL n bbs').bb_label = (EL n bbs).bb_label` by
    metis_tac[EL_MAP] >>
  gvs[] >>
  `lookup_block (EL n bbs').bb_label bbs' = SOME (EL n bbs')` by (
    irule lookup_block_EL >> gvs[]) >>
  gvs[]
QED

(* When lookup_block finds something at lbl in replace_block lbl new_bb bbs,
   and new_bb.bb_label = lbl, it must be new_bb. *)
Triviality lookup_replace_eq_det:
  !lbl new_bb bbs bb0 bb.
    lookup_block lbl bbs = SOME bb0 /\
    new_bb.bb_label = lbl /\
    lookup_block lbl (replace_block lbl new_bb bbs) = SOME bb ==>
    bb = new_bb
Proof
  rpt strip_tac >>
  `lookup_block lbl (replace_block lbl new_bb bbs) = SOME new_bb` by
    metis_tac[SIMP_RULE (srw_ss()) [PULL_EXISTS] lookup_block_replace_eq] >>
  gvs[]
QED

(* ==========================================================================
   Part 5: General rename pipeline preserves blocks_rel R

   Three preconditions on R:
   (i)   R is reflexive (for base cases)
   (ii)  R is transitive (for composing stages)
   (iii) rename_block_insts preserves R per-block
   (iv)  the PHI operand MAP preserves R per-block
   ========================================================================== *)

(* replace_block preserves blocks_rel when the new block satisfies R *)
Triviality replace_block_preserves_rel:
  !R lbl bbs orig new_bb.
    (!bb. R bb bb) /\
    lookup_block lbl bbs = SOME orig /\
    new_bb.bb_label = orig.bb_label /\
    R orig new_bb ==>
    blocks_rel R bbs (replace_block lbl new_bb bbs)
Proof
  rw[blocks_rel_def] >>
  imp_res_tac lookup_block_label >>
  Cases_on `lbl' = lbl` >> gvs[]
  >- metis_tac[lookup_replace_eq_det]
  >> metis_tac[lookup_block_replace_neq]
QED

(* One step of update_succ_phis: the PHI MAP applied to one successor block *)
Triviality update_succ_one_step_preserves_rel:
  !R rs lbl bbs s.
    (!bb. R bb bb) /\
    (!bb rs' lbl'.
       R bb (bb with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else inst with inst_operands :=
                       update_phi_for_pred rs' lbl' inst.inst_operands)
         bb.bb_instructions)) ==>
    blocks_rel R bbs
      (case lookup_block s bbs of
         NONE => bbs
       | SOME sbb =>
           replace_block s
             (sbb with bb_instructions :=
               MAP (\inst. if inst.inst_opcode <> PHI then inst
                           else inst with inst_operands :=
                             update_phi_for_pred rs lbl inst.inst_operands)
               sbb.bb_instructions) bbs)
Proof
  rw[] >>
  Cases_on `lookup_block s bbs` >> simp[]
  >- (irule blocks_rel_refl >> gvs[])
  >> irule replace_block_preserves_rel >> gvs[]
QED

(* Cons unfolding for update_succ_phis *)
Triviality update_succ_phis_cons:
  update_succ_phis rs lbl bbs (h::t) =
  update_succ_phis rs lbl
    (case lookup_block h bbs of
       NONE => bbs
     | SOME sbb =>
         replace_block h
           (sbb with bb_instructions :=
             MAP (\inst. if inst.inst_opcode <> PHI then inst
                         else inst with inst_operands :=
                           update_phi_for_pred rs lbl inst.inst_operands)
             sbb.bb_instructions) bbs) t
Proof
  rw[update_succ_phis_def, FOLDL, LET_THM]
QED

(* update_succ_phis preserves blocks_rel R (FOLDL of one-step) *)
Triviality update_succ_phis_preserves_rel:
  !R rs lbl bbs succs.
    (!bb. R bb bb) /\
    (!a b c. R a b /\ R b c ==> R a c) /\
    (!bb rs' lbl'.
       R bb (bb with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else inst with inst_operands :=
                       update_phi_for_pred rs' lbl' inst.inst_operands)
         bb.bb_instructions)) ==>
    blocks_rel R bbs (update_succ_phis rs lbl bbs succs)
Proof
  ntac 3 gen_tac >> qid_spec_tac `bbs` >>
  Induct_on `succs`
  >- (rw[update_succ_phis_def, FOLDL] >> irule blocks_rel_refl >> gvs[])
  >> rpt strip_tac >>
     rw[update_succ_phis_cons] >>
     irule (REWRITE_RULE [AND_IMP_INTRO] blocks_rel_trans) >>
     conj_tac >- metis_tac[] >>
     qexists_tac `case lookup_block h bbs of
       NONE => bbs
     | SOME sbb => replace_block h
         (sbb with bb_instructions :=
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                       else inst with inst_operands :=
                         update_phi_for_pred rs lbl inst.inst_operands)
           sbb.bb_instructions) bbs` >>
     conj_tac
     >- (irule update_succ_one_step_preserves_rel >> metis_tac[])
     >- (first_x_assum irule >> metis_tac[])
QED

(* rename_blocks preserves blocks_rel R — structural induction on dom_tree *)
Triviality phi_map_empty_insts:
  (!bb rs' lbl'.
     R bb (bb with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else inst with inst_operands :=
                     update_phi_for_pred rs' lbl' inst.inst_operands)
       bb.bb_instructions)) ==>
  !bb. bb.bb_instructions = [] ==> R bb (bb with bb_instructions := [])
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`bb`, `ARB`, `ARB`] mp_tac) >>
  asm_rewrite_tac[MAP]
QED

Triviality rename_step_preserves_rel:
  !R.
    (!bb. R bb bb) /\
    (!rs bb insts' rs1.
       bb.bb_instructions <> [] /\
       rename_block_insts rs bb.bb_instructions = (rs1, insts') ==>
       R bb (bb with bb_instructions := insts')) /\
    (!bb rs' lbl'.
       R bb (bb with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else inst with inst_operands :=
                       update_phi_for_pred rs' lbl' inst.inst_operands)
         bb.bb_instructions)) ==>
    !rs s bbs x insts' rs1.
      lookup_block s bbs = SOME x /\
      rename_block_insts rs x.bb_instructions = (rs1, insts') ==>
      blocks_rel R bbs (replace_block s (x with bb_instructions := insts') bbs)
Proof
  rpt strip_tac >>
  irule replace_block_preserves_rel >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `x` >> rpt conj_tac
  >- (Cases_on `x.bb_instructions`
    >- (
      `insts' = []` by gvs[rename_block_insts_def] >> gvs[] >>
      irule phi_map_empty_insts >> gvs[]
    )
    >- (first_x_assum irule >> simp[] >> metis_tac[])
  )
  >- simp[]
  >- (imp_res_tac lookup_block_label >> simp[])
QED

Triviality rename_blocks_preserves_rel:
  !R.
    (!bb. R bb bb) /\
    (!a b c. R a b /\ R b c ==> R a c) /\
    (* rename_block_insts preserves R per-block *)
    (!rs bb insts' rs1.
       bb.bb_instructions <> [] /\
       rename_block_insts rs bb.bb_instructions = (rs1, insts') ==>
       R bb (bb with bb_instructions := insts')) /\
    (* PHI operand MAP preserves R per-block *)
    (!bb rs' lbl'.
       R bb (bb with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else inst with inst_operands :=
                       update_phi_for_pred rs' lbl' inst.inst_operands)
         bb.bb_instructions)) ==>
    (!dtree bbs rs succ_map.
      blocks_rel R bbs (SND (rename_blocks rs bbs succ_map dtree))) /\
    (!children bbs ctrs stacks succ_map.
      blocks_rel R bbs (SND (rename_children ctrs stacks bbs succ_map children)))
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac
  >- (
    rw[] >> rw[Once rename_blocks_def] >>
    Cases_on `lookup_block s bbs`
    >- (simp[] >> irule blocks_rel_refl >> first_assum ACCEPT_TAC)
    >> simp[] >> pairarg_tac >> rw[LET_THM]
    >> qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss`
    >> qabbrev_tac `bbs1 = replace_block s (x with bb_instructions := insts') bbs`
    >> qabbrev_tac `bbs2 = update_succ_phis rs1 s bbs1 succs`
    >> `blocks_rel R bbs bbs1` by (
      simp[Abbr`bbs1`]
      >> irule rename_step_preserves_rel
      >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >> qexistsl_tac [`rs`, `rs1`] >> first_assum ACCEPT_TAC
    )
    >> `blocks_rel R bbs1 bbs2` by (
      simp[Abbr`bbs2`]
      >> irule update_succ_phis_preserves_rel
      >> rpt conj_tac >> first_assum ACCEPT_TAC
    )
    >> irule (REWRITE_RULE [AND_IMP_INTRO] blocks_rel_trans)
    >> (conj_tac >- first_assum ACCEPT_TAC)
    >> qexists_tac `bbs2` >> conj_tac
    >- (irule (REWRITE_RULE [AND_IMP_INTRO] blocks_rel_trans)
      >> (conj_tac >- first_assum ACCEPT_TAC)
      >> metis_tac[])
    >> first_x_assum irule
  )
  >- (rw[Once rename_blocks_def] >> irule blocks_rel_refl >> first_assum ACCEPT_TAC)
  >> rw[Once rename_blocks_def, LET_THM]
  >> pairarg_tac >> rw[]
  >> irule (REWRITE_RULE [AND_IMP_INTRO] blocks_rel_trans)
  >> (conj_tac >- first_assum ACCEPT_TAC)
  >> qexists_tac `bbs'` >> conj_tac
  >- (
    (`bbs' = SND (rename_blocks (ctrs,stacks) bbs succ_map dtree)` by
      (Cases_on `rename_blocks (ctrs,stacks) bbs succ_map dtree` >> gvs[]))
    >> gvs[])
  >> first_x_assum irule
QED

(* ==========================================================================
   Part 6: opcodes_preserved — instance of blocks_rel
   ========================================================================== *)

Definition opcodes_preserved_def:
  opcodes_preserved bbs bbs' <=>
    !lbl bb. lookup_block lbl bbs' = SOME bb ==>
      ?bb0. lookup_block lbl bbs = SOME bb0 /\
            LENGTH bb.bb_instructions = LENGTH bb0.bb_instructions /\
            !j. j < LENGTH bb0.bb_instructions ==>
              (EL j bb.bb_instructions).inst_opcode =
              (EL j bb0.bb_instructions).inst_opcode
End

(* The per-block opcode relation *)
Definition opcode_rel_def:
  opcode_rel bb bb' <=>
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    !j. j < LENGTH bb.bb_instructions ==>
      (EL j bb'.bb_instructions).inst_opcode =
      (EL j bb.bb_instructions).inst_opcode
End

Triviality opcodes_preserved_is_blocks_rel:
  opcodes_preserved bbs bbs' <=> blocks_rel opcode_rel bbs bbs'
Proof
  rw[opcodes_preserved_def, blocks_rel_def, opcode_rel_def] >> metis_tac[]
QED

Triviality opcode_rel_refl:
  !bb. opcode_rel bb bb
Proof
  rw[opcode_rel_def]
QED

Triviality opcode_rel_trans:
  !a b c. opcode_rel a b /\ opcode_rel b c ==> opcode_rel a c
Proof
  rw[opcode_rel_def] >> gvs[]
QED

(* rename_block_insts preserves opcode_rel per-block *)
Triviality rename_block_insts_opcode_rel:
  !rs bb insts' rs1.
    rename_block_insts rs bb.bb_instructions = (rs1, insts') ==>
    opcode_rel bb (bb with bb_instructions := insts')
Proof
  rw[opcode_rel_def] >> gvs[]
  >- (`LENGTH (SND (rename_block_insts rs bb.bb_instructions)) =
       LENGTH bb.bb_instructions` by simp[rename_block_insts_length] >>
      Cases_on `rename_block_insts rs bb.bb_instructions` >> gvs[])
  >- (`(EL j (SND (rename_block_insts rs bb.bb_instructions))).inst_opcode =
       (EL j bb.bb_instructions).inst_opcode` by simp[rename_block_insts_opcodes] >>
      Cases_on `rename_block_insts rs bb.bb_instructions` >> gvs[])
QED

(* PHI MAP preserves opcode_rel per-block *)
Triviality phi_map_opcode_rel:
  !bb rs lbl.
    opcode_rel bb (bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else inst with inst_operands :=
                    update_phi_for_pred rs lbl inst.inst_operands)
      bb.bb_instructions)
Proof
  rw[opcode_rel_def, LENGTH_MAP] >>
  Cases_on `(EL j bb.bb_instructions).inst_opcode = PHI` >>
  simp[EL_MAP]
QED

(* Main result: rename_blocks preserves opcodes *)
Theorem rename_blocks_opcodes_preserved:
  (!dtree bbs rs succ_map.
    opcodes_preserved bbs (SND (rename_blocks rs bbs succ_map dtree))) /\
  (!children bbs ctrs stacks succ_map.
    opcodes_preserved bbs (SND (rename_children ctrs stacks bbs succ_map children)))
Proof
  rw[opcodes_preserved_is_blocks_rel] >>
  mp_tac (Q.SPEC `opcode_rel` rename_blocks_preserves_rel) >>
  (impl_tac >- metis_tac[opcode_rel_refl, opcode_rel_trans,
      rename_block_insts_opcode_rel, phi_map_opcode_rel]) >>
  metis_tac[]
QED

(* Lookup corollary for opcodes_preserved *)
Theorem opcodes_preserved_lookup:
  !bbs bbs' lbl bb bb'.
    opcodes_preserved bbs bbs' /\
    lookup_block lbl bbs = SOME bb /\
    lookup_block lbl bbs' = SOME bb' ==>
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    !j. j < LENGTH bb.bb_instructions ==>
      (EL j bb'.bb_instructions).inst_opcode =
      (EL j bb.bb_instructions).inst_opcode
Proof
  rw[opcodes_preserved_def] >>
  first_x_assum drule >> strip_tac >>
  `bb0 = bb` by metis_tac[optionTheory.SOME_11] >>
  gvs[]
QED

(* ==========================================================================
   Part 7: succs_preserved — instance of blocks_rel
   ========================================================================== *)

Definition succs_preserved_def:
  succs_preserved bbs bbs' <=>
    !lbl bb. lookup_block lbl bbs' = SOME bb ==>
      ?bb0. lookup_block lbl bbs = SOME bb0 /\
            bb_succs bb = bb_succs bb0
End

(* The per-block succs relation *)
Definition succs_rel_def:
  succs_rel bb bb' <=> bb_succs bb' = bb_succs bb
End

Triviality succs_preserved_is_blocks_rel:
  succs_preserved bbs bbs' <=> blocks_rel succs_rel bbs bbs'
Proof
  rw[succs_preserved_def, blocks_rel_def, succs_rel_def] >> metis_tac[]
QED

Triviality succs_rel_refl:
  !bb. succs_rel bb bb
Proof
  rw[succs_rel_def]
QED

Triviality succs_rel_trans:
  !a b c. succs_rel a b /\ succs_rel b c ==> succs_rel a c
Proof
  rw[succs_rel_def]
QED

(* rename_block_insts preserves succs_rel per-block *)
Triviality rename_block_insts_succs_rel:
  !rs bb insts' rs1.
    rename_block_insts rs bb.bb_instructions = (rs1, insts') ==>
    succs_rel bb (bb with bb_instructions := insts')
Proof
  rw[succs_rel_def, bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[rename_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `SND (rename_block_insts rs (h::t)) = inst'::rest'` by
    (simp[rename_block_insts_def] >> pairarg_tac >> gvs[] >>
     pairarg_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`rs`, `h::t`] rename_block_insts_last) >> simp[] >>
  strip_tac >> simp[rename_inst_get_successors]
QED

(* PHI MAP preserves succs_rel per-block:
   The MAP only changes PHI operands. If LAST is PHI, get_successors = []
   (since is_terminator PHI = F). If LAST is not PHI, MAP leaves it unchanged. *)
Triviality phi_map_succs_rel:
  !bb rs lbl.
    succs_rel bb (bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else inst with inst_operands :=
                    update_phi_for_pred rs lbl inst.inst_operands)
      bb.bb_instructions)
Proof
  rw[succs_rel_def, bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[LAST_CONS_cond, MAP_EQ_NIL] >>
  Cases_on `t = []` >> gvs[]
  >- (Cases_on `h.inst_opcode = PHI` >> gvs[get_successors_def, is_terminator_def])
  >> simp[LAST_MAP] >>
  Cases_on `(LAST t).inst_opcode = PHI` >> gvs[get_successors_def, is_terminator_def]
QED

(* Main result: rename_blocks preserves succs *)
Theorem rename_blocks_succs_preserved[local]:
  (!dtree bbs rs succ_map.
    succs_preserved bbs (SND (rename_blocks rs bbs succ_map dtree))) /\
  (!children bbs ctrs stacks succ_map.
    succs_preserved bbs (SND (rename_children ctrs stacks bbs succ_map children)))
Proof
  rw[succs_preserved_is_blocks_rel] >>
  mp_tac (Q.SPEC `succs_rel` rename_blocks_preserves_rel) >>
  (impl_tac >- metis_tac[succs_rel_refl, succs_rel_trans,
      rename_block_insts_succs_rel, phi_map_succs_rel]) >>
  metis_tac[]
QED

(* ==========================================================================
   Part 8: Main structural theorem — compose phi_extends + opcodes_preserved
   ========================================================================== *)

(* Promote rename_blocks_succs_preserved for use by makeSsaProofScript *)
Theorem rename_blocks_succs_preserved_export:
  (!dtree bbs rs succ_map.
    succs_preserved bbs (SND (rename_blocks rs bbs succ_map dtree))) /\
  (!children bbs ctrs stacks succ_map.
    succs_preserved bbs (SND (rename_children ctrs stacks bbs succ_map children)))
Proof
  metis_tac[rename_blocks_succs_preserved]
QED

Triviality bb_succs_nonempty:
  !lbl h t. bb_succs <|bb_label := lbl; bb_instructions := h::t|> =
    nub (REVERSE (get_successors (LAST (h::t))))
Proof
  simp[bb_succs_def]
QED

Triviality bb_succs_empty:
  !lbl. bb_succs <|bb_label := lbl; bb_instructions := []|> = []
Proof
  simp[bb_succs_def]
QED

(* Prepending PHIs preserves bb_succs. Works with any two blocks —
   just needs the instruction relationship. bb_succs only depends on
   LAST of instructions; PHIs are not terminators so don't affect it. *)
Triviality LAST_APPEND_CONS[local]:
  !l h t. LAST (l ++ h::t) = LAST (h::t)
Proof
  Induct >> simp[LAST_CONS_cond] >> rw[] >> Cases_on `l` >> gvs[]
QED

Triviality phi_prefix_preserves_succs:
  !bb1 bb2 phis.
    bb1.bb_instructions = phis ++ bb2.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) phis ==>
    bb_succs bb1 = bb_succs bb2
Proof
  rpt strip_tac >> Cases_on `bb2.bb_instructions`
  >- (Cases_on `phis` >> gvs[bb_succs_def] >>
      sg `MEM (LAST (h::t)) (h::t)` >- metis_tac[LAST_MEM, MEM] >>
      gvs[EVERY_MEM] >> gvs[get_successors_def, is_terminator_def])
  >> Cases_on `phis` >- gvs[bb_succs_def]
  >> sg `bb_succs bb1 =
         nub (REVERSE (get_successors (LAST (h'::(t' ++ h::t)))))` >-
       (simp[bb_succs_def] >> gvs[]) >>
  sg `bb_succs bb2 =
      nub (REVERSE (get_successors (LAST (h::t))))` >- simp[bb_succs_def] >>
  ASM_REWRITE_TAC[] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [CONS_APPEND] THENC
                        ONCE_REWRITE_CONV [APPEND_ASSOC])) >>
  REWRITE_TAC[LAST_APPEND_CONS]
QED

(* phi_extends implies succs_preserved (needs ALL_DISTINCT labels) *)
Theorem phi_extends_succs_preserved:
  !bbs bbs'. phi_extends bbs bbs' /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    succs_preserved bbs bbs'
Proof
  rw[phi_extends_def, succs_preserved_def] >>
  imp_res_tac lookup_block_MEM >> gvs[MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >> gvs[] >> strip_tac >>
  qexists_tac `EL n bbs` >>
  imp_res_tac lookup_block_label >>
  sg `(EL n bbs).bb_label = lbl` >-
    (qpat_x_assum `MAP _ bbs' = MAP _ bbs` (mp_tac o
       Q.AP_TERM `\ls. EL n ls`) >>
     simp[EL_MAP]) >>
  conj_tac
  >- (irule MEM_lookup_block >> gvs[MEM_EL] >> metis_tac[])
  >> metis_tac[phi_prefix_preserves_succs]
QED

(* succs_preserved is transitive *)
Theorem succs_preserved_trans:
  !a b c. succs_preserved a b /\ succs_preserved b c ==> succs_preserved a c
Proof
  rw[succs_preserved_def] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `bb0'` >> gvs[]
QED

(* Full pipeline preserves succs *)
Theorem make_ssa_fn_succs_preserved:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
    succs_preserved func.fn_blocks
      (make_ssa_fn dom_frontiers dtree dom_post_order pred_map succ_map
         live_in func).fn_blocks
Proof
  rw[make_ssa_fn_def, LET_THM] >>
  CASE_TAC >- simp[succs_preserved_def] >>
  pairarg_tac >> gvs[] >>
  irule (REWRITE_RULE [AND_IMP_INTRO] succs_preserved_trans) >>
  qexists_tac `add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order))))` >>
  conj_tac
  >- (irule phi_extends_succs_preserved >>
      metis_tac[add_phi_nodes_phi_extends])
  >> metis_tac[rename_blocks_succs_preserved_export, SND]
QED

Theorem pipeline_block_structure:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func bb bb'.
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    MEM bb func.fn_blocks /\
    lookup_block bb.bb_label func'.fn_blocks = SOME bb' ==>
    ?n_phi.
      LENGTH bb'.bb_instructions = n_phi + LENGTH bb.bb_instructions /\
      (!j. j < n_phi ==>
        (EL j bb'.bb_instructions).inst_opcode = PHI) /\
      (!j. j < LENGTH bb.bb_instructions ==>
        (EL (n_phi + j) bb'.bb_instructions).inst_opcode =
        (EL j bb.bb_instructions).inst_opcode)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  sg `func.fn_blocks <> []` >- gvs[wf_function_def, fn_has_entry_def] >>
  sg `?entry. fn_entry_label func = SOME entry` >- (
    gvs[fn_entry_label_def, entry_block_def] >>
    Cases_on `func.fn_blocks` >> gvs[]) >>
  gvs[make_ssa_fn_def, LET_THM] >>
  qabbrev_tac `ordered_bbs = MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order))` >>
  qabbrev_tac `defs = compute_defs ordered_bbs` >>
  qabbrev_tac `bbs1 = add_phi_nodes dom_frontiers pred_map live_in
    func.fn_blocks defs` >>
  Cases_on `rename_blocks (init_rename_state defs) bbs1 succ_map dtree` >>
  rename1 `rename_blocks _ bbs1 _ _ = (rs_final, bbs2)` >> gvs[] >>
  sg `phi_extends func.fn_blocks bbs1` >-
    (unabbrev_all_tac >> metis_tac[add_phi_nodes_phi_extends]) >>
  sg `opcodes_preserved bbs1 bbs2` >-
    metis_tac[rename_blocks_opcodes_preserved, SND] >>
  sg `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` >-
    gvs[wf_function_def, fn_labels_def] >>
  sg `lookup_block bb.bb_label func.fn_blocks = SOME bb` >-
    (irule lookup_block_MEM_SOME >> gvs[]) >>
  drule_all phi_extends_lookup >> strip_tac >>
  rename1 `bb_mid.bb_instructions = phis ++ bb.bb_instructions` >>
  drule opcodes_preserved_lookup >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qexists_tac `LENGTH phis` >> gvs[] >> rw[]
  >- gvs[EL_APPEND1, EVERY_EL]
  >> gvs[EL_APPEND2]
QED
