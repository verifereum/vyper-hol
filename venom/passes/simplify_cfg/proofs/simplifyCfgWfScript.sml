(*
 * Simplify CFG — wf_function preservation through collapse_dfs
 *
 * Proves wf_function is preserved through each step of the DFS collapse,
 * and through the full simplify_cfg_round pipeline.
 *)

Theory simplifyCfgWf
Ancestors
  simplifyCfgHelpers
  venomInst venomState cfgTransform simplifyCfgDefs venomExecSemantics
  venomWf stateEquiv stateEquivProps cfgTransformProps venomExecProps
  cfgTransformProofs venomExecProofs

(* ================================================================
   Section: bb_well_formed through update_succ_phi_labels
   Key fact: subst_label_inst only changes operands, not opcodes.
   So bb_well_formed (which only checks opcodes) is preserved.
   ================================================================ *)

(* subst_label_inst preserves opcode *)
Theorem subst_label_inst_opcode[local]:
  !old new inst. (subst_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  rw[cfgTransformTheory.subst_label_inst_def]
QED

(* subst_label_inst preserves inst_id *)
Theorem subst_label_inst_id[local]:
  !old new inst. (subst_label_inst old new inst).inst_id = inst.inst_id
Proof
  rw[cfgTransformTheory.subst_label_inst_def]
QED

(* MAP over instructions preserving opcodes preserves bb_well_formed *)
Theorem bb_well_formed_MAP_opcode_preserving[local]:
  !f bb. bb_well_formed bb /\
    (!inst. (f inst).inst_opcode = inst.inst_opcode) ==>
    bb_well_formed (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  rpt strip_tac >>
  (* Rewrite MAP f opcode to original opcode everywhere *)
  `!n. n < LENGTH bb.bb_instructions ==>
    (EL n (MAP f bb.bb_instructions)).inst_opcode =
    (EL n bb.bb_instructions).inst_opcode` by
    simp[listTheory.EL_MAP] >>
  qpat_x_assum `bb_well_formed bb` mp_tac >>
  simp[bb_well_formed_def, listTheory.LAST_MAP] >> strip_tac >>
  rpt strip_tac >> fs[listTheory.LENGTH_MAP] >>
  res_tac >> fs[]
QED

(* The per-block body of update_succ_phi_labels preserves bb_well_formed *)
Theorem bb_well_formed_subst_phi_labels:
  !old new bb. bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst)
      bb.bb_instructions)
Proof
  rpt strip_tac >>
  irule bb_well_formed_MAP_opcode_preserving >> simp[] >>
  rpt strip_tac >> rw[] >> simp[subst_label_inst_opcode]
QED

(* FOLDL body of update_succ_phi_labels preserves bb_well_formed.
   Key: Induct on succs, use qpat_x_assum to avoid matching wrong assumption *)
Theorem FOLDL_update_phi_preserves_wf[local]:
  !succs old new bbs.
    (!b. MEM b bbs ==> bb_well_formed b) ==>
    !bb. MEM bb (FOLDL (\bs s.
         case lookup_block s bs of
           NONE => bs
         | SOME sbb =>
             replace_block s
               (sbb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                              else subst_label_inst old new inst)
                      sbb.bb_instructions) bs) bbs succs) ==>
    bb_well_formed bb
Proof
  Induct >> rw[] >>
  qpat_x_assum `!old new bbs. _` mp_tac >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  TRY (disch_then (qspecl_then [`old`, `new`, `bbs`] mp_tac) >> simp[] >> NO_TAC) >>
  disch_then (qspecl_then [`old`, `new`,
       `replace_block h
         (x with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old new inst)
            x.bb_instructions) bbs`] mp_tac) >>
  SUBGOAL_THEN ``!b. MEM b
       (replace_block h
         (x with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old new inst)
            x.bb_instructions) bbs) ==> bb_well_formed b`` ASSUME_TAC
  >| [rpt strip_tac >>
      imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
      fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
      BasicProvers.every_case_tac >> fs[] >> rw[] >>
      TRY (irule bb_well_formed_subst_phi_labels) >> res_tac,
      metis_tac[]]
QED

(* bb_well_formed through update_succ_phi_labels *)
Theorem bb_well_formed_update_succ_phi_labels[local]:
  !old new bbs succs bb.
    MEM bb (update_succ_phi_labels old new bbs succs) ==>
    (!b. MEM b bbs ==> bb_well_formed b) ==>
    bb_well_formed bb
Proof
  rw[update_succ_phi_labels_def, LET_THM] >>
  mp_tac (Q.SPECL [`succs`, `old`, `new`, `bbs`] FOLDL_update_phi_preserves_wf) >>
  simp[]
QED

(* ================================================================
   Section: bb_succs through update_succ_phi_labels
   update_succ_phi_labels only modifies PHI instructions,
   and bb_succs looks at terminators, so succs are unchanged.
   ================================================================ *)

(* bb_succs through PHI-only MAP *)
Theorem bb_succs_MAP_phi_only:
  !f bb. bb_well_formed bb /\
    (!inst. inst.inst_opcode <> PHI ==> f inst = inst) ==>
    bb_succs (bb with bb_instructions := MAP f bb.bb_instructions) =
    bb_succs bb
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  `LAST (MAP f (h::t)) = f (LAST (h::t))` by
    simp[listTheory.LAST_MAP] >>
  `is_terminator (LAST (h::t)).inst_opcode` by
    (Cases_on `t` >> fs[listTheory.LAST_DEF]) >>
  `(LAST (h::t)).inst_opcode <> PHI` by
    (strip_tac >> fs[is_terminator_def]) >>
  `f (LAST (h::t)) = LAST (h::t)` by res_tac >>
  ONCE_REWRITE_TAC [GSYM listTheory.MAP] >> fs[]
QED

(* Helper: ALL_DISTINCT MAP + same image => same element *)
Theorem ALL_DISTINCT_MAP_eq[local]:
  !f x y l. ALL_DISTINCT (MAP f l) /\
    MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  rpt strip_tac >>
  fs[listTheory.MEM_EL] >> rw[] >>
  `n < LENGTH (MAP f l)` by simp[] >>
  `n' < LENGTH (MAP f l)` by simp[] >>
  `EL n (MAP f l) = EL n' (MAP f l)` by
    (simp[listTheory.EL_MAP]) >>
  metis_tac[listTheory.ALL_DISTINCT_EL_IMP]
QED

(* Uniqueness of lookup_block under ALL_DISTINCT labels *)
Theorem lookup_block_unique[local]:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==>
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    !bb'. MEM bb' bbs /\ bb'.bb_label = lbl ==> bb' = bb
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  mp_tac (ISPECL [``\(b:basic_block). b.bb_label``, ``bb':basic_block``,
                  ``bb:basic_block``, ``bbs:basic_block list``]
          ALL_DISTINCT_MAP_eq) >>
  simp[]
QED

(* replace_block with PHI-only changes preserves MAP bb_succs *)
Theorem MAP_bb_succs_replace_block_phi[local]:
  !h old new x bbs.
    lookup_block h bbs = SOME x ==>
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    (!b. MEM b bbs ==> bb_well_formed b) ==>
    MAP bb_succs (replace_block h
      (x with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else subst_label_inst old new inst)
         x.bb_instructions) bbs) = MAP bb_succs bbs
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb_well_formed x` by res_tac >>
  `bb_succs (x with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst) x.bb_instructions)
    = bb_succs x` by (
    irule bb_succs_MAP_phi_only >> simp[] >>
    rpt strip_tac >> rw[] >> simp[subst_label_inst_opcode]) >>
  simp[cfgTransformTheory.replace_block_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >> rw[] >>
  imp_res_tac (Q.SPECL [`h`, `bbs`] lookup_block_unique) >>
  res_tac >> fs[]
QED

(* FOLDL of update_succ_phi_labels preserves MAP bb_succs (given wf + ALL_DISTINCT) *)
Theorem FOLDL_update_phi_preserves_succs[local]:
  !succs old new bbs.
    (!b. MEM b bbs ==> bb_well_formed b) ==>
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    MAP bb_succs
      (FOLDL (\bs s.
         case lookup_block s bs of
           NONE => bs
         | SOME sbb =>
             replace_block s
               (sbb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                              else subst_label_inst old new inst)
                      sbb.bb_instructions) bs) bbs succs) =
    MAP bb_succs bbs
Proof
  Induct >> rw[] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  (* Only SOME case remains; NONE auto-discharged by fs/IH *)
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  qabbrev_tac `bbs' = replace_block h
    (x with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst)
       x.bb_instructions) bbs` >>
  (* Step 1: wf of replace_block result *)
  SUBGOAL_THEN ``!b. MEM b bbs' ==> bb_well_formed b`` ASSUME_TAC
  >| [
    simp[Abbr `bbs'`] >> rpt strip_tac >>
    imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
    fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
    BasicProvers.every_case_tac >> fs[] >> rw[] >>
    irule bb_well_formed_subst_phi_labels >> res_tac,
    ALL_TAC] >>
  (* Step 1b: ALL_DISTINCT preserved through replace_block *)
  SUBGOAL_THEN ``ALL_DISTINCT (MAP (\b. b.bb_label) bbs')`` ASSUME_TAC
  >| [
    simp[Abbr `bbs'`] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> simp[],
    ALL_TAC] >>
  (* Step 2: IH gives MAP bb_succs (FOLDL ... bbs' succs) = MAP bb_succs bbs' *)
  first_x_assum (qspecl_then [`old`, `new`, `bbs'`] mp_tac) >> simp[] >>
  disch_tac >>
  (* Step 3: MAP bb_succs bbs' = MAP bb_succs bbs *)
  SUBGOAL_THEN ``MAP bb_succs bbs' = MAP bb_succs bbs`` ASSUME_TAC
  >| [
    simp[Abbr `bbs'`] >>
    irule MAP_bb_succs_replace_block_phi >> simp[],
    fs[]]
QED

(* update_succ_phi_labels preserves MAP bb_succs (given wf + ALL_DISTINCT) *)
Theorem MAP_bb_succs_update_succ_phi_labels:
  !old new bbs succs.
    (!b. MEM b bbs ==> bb_well_formed b) ==>
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    MAP bb_succs (update_succ_phi_labels old new bbs succs) =
    MAP bb_succs bbs
Proof
  rw[update_succ_phi_labels_def, LET_THM] >>
  irule FOLDL_update_phi_preserves_succs >> simp[]
QED

(* ================================================================
   Section: LAST through update_succ_phi_labels
   Key insight: LAST instruction is a terminator (not PHI),
   so the conditional MAP leaves it unchanged.
   ================================================================ *)

(* LAST of PHI-conditional MAP is LAST of original when bb_well_formed *)
Theorem LAST_MAP_phi_only[local]:
  !old new bb. bb_well_formed bb /\ bb.bb_instructions <> [] ==>
    LAST (MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst old new inst)
              bb.bb_instructions) =
    LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  simp[listTheory.LAST_MAP] >>
  fs[bb_well_formed_def] >>
  `is_terminator (LAST (h::t)).inst_opcode` by
    (Cases_on `t` >> fs[listTheory.LAST_DEF]) >>
  `(LAST (h::t)).inst_opcode <> PHI` by
    (strip_tac >> fs[is_terminator_def]) >>
  simp[]
QED

(* Helper: wf through replace_block with phi subst *)
Triviality wf_replace_block_phi_subst[local]:
  !h old new sbb bbs.
    (!b. MEM b bbs ==> bb_well_formed b) /\
    lookup_block h bbs = SOME sbb ==>
    !b. MEM b (replace_block h
         (sbb with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old new inst)
            sbb.bb_instructions) bbs) ==> bb_well_formed b
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM b (replace_block _ _ _)` mp_tac >>
  simp[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  strip_tac >> rename1 `MEM y bbs` >>
  Cases_on `y.bb_label = h` >> gvs[]
  >- (irule bb_well_formed_subst_phi_labels >>
      first_x_assum match_mp_tac >>
      metis_tac[venomExecProofsTheory.lookup_block_MEM])
  >> first_x_assum match_mp_tac >> simp[]
QED

(* Helper: bb0 in replace_block phi subst maps back to bbs with LAST preserved *)
Triviality replace_block_phi_subst_LAST_back[local]:
  !h old new sbb bbs bb0.
    (!b. MEM b bbs ==> bb_well_formed b) /\
    lookup_block h bbs = SOME sbb /\
    MEM bb0 (replace_block h
         (sbb with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old new inst)
            sbb.bb_instructions) bbs) /\
    bb0.bb_instructions <> [] ==>
    ?bb00. MEM bb00 bbs /\ bb00.bb_label = bb0.bb_label /\
           bb00.bb_instructions <> [] /\
           LAST bb0.bb_instructions = LAST bb00.bb_instructions
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM bb0 (replace_block _ _ _)` mp_tac >>
  simp[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  strip_tac >> rename1 `MEM y bbs` >>
  Cases_on `y.bb_label = h` >> gvs[]
  >- (qexists `sbb` >> simp[] >>
      mp_tac (Q.SPECL [`old`, `new`, `sbb`] LAST_MAP_phi_only) >>
      simp[] >> metis_tac[venomExecProofsTheory.lookup_block_MEM])
  >> (* original block case — bb0 unchanged *)
  qexists `bb0` >> simp[]
QED

(* Local copy of MEM_replace_block_cases — needed here because
   simplifyCfgCollapseBaseTheory depends on us (circular). *)
Triviality MEM_replace_block_cases[local]:
  !x lbl bb' bbs.
    MEM x (replace_block lbl bb' bbs) <=>
    (x = bb' /\ (?y. MEM y bbs /\ y.bb_label = lbl)) \/
    (MEM x bbs /\ x.bb_label <> lbl)
Proof
  rw[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  eq_tac >> strip_tac
  >- (Cases_on `bb.bb_label = lbl` >> fs[] >> metis_tac[])
  >- metis_tac[]
  >> fs[] >> qexists_tac `x` >> simp[]
QED

(* Local: unfold one step of update_succ_phi_labels *)
Triviality update_succ_phi_labels_cons[local]:
  !old new bbs h succs.
    update_succ_phi_labels old new bbs (h::succs) =
    update_succ_phi_labels old new
      (case lookup_block h bbs of
         NONE => bbs
       | SOME sbb =>
           replace_block h
             (sbb with bb_instructions :=
                MAP (\inst. if inst.inst_opcode <> PHI then inst
                            else subst_label_inst old new inst)
                    sbb.bb_instructions) bbs)
      succs
Proof
  simp[update_succ_phi_labels_def, LET_THM]
QED

(* bb_succs and num_succs depend ONLY on LAST instruction when non-empty *)
Theorem bb_succs_LAST_eq:
  !bb1 bb2. bb1.bb_instructions <> [] /\ bb2.bb_instructions <> [] /\
    LAST bb1.bb_instructions = LAST bb2.bb_instructions ==>
    bb_succs bb1 = bb_succs bb2
Proof
  rpt strip_tac >>
  Cases_on `bb1.bb_instructions` >> Cases_on `bb2.bb_instructions` >> gvs[] >>
  simp[bb_succs_def]
QED

Theorem num_succs_LAST_eq:
  !bb1 bb2. bb1.bb_instructions <> [] /\ bb2.bb_instructions <> [] /\
    LAST bb1.bb_instructions = LAST bb2.bb_instructions ==>
    num_succs bb1 = num_succs bb2
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.num_succs_def] >>
  drule_all bb_succs_LAST_eq >> simp[]
QED

(* LAST through update_succ_phi_labels — direct induction proof.
   Each FOLDL step is a replace_block with PHI-only MAP.
   replace_block_phi_subst_LAST_back handles a single step.
   wf_replace_block_phi_subst + ALL_DISTINCT_replace_block carry the invariants. *)
Theorem LAST_update_succ_phi_labels:
  !old new bbs succs bb'.
    (!b. MEM b bbs ==> bb_well_formed b) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    MEM bb' (update_succ_phi_labels old new bbs succs) /\
    bb'.bb_instructions <> [] ==>
    ?bb0. MEM bb0 bbs /\ bb0.bb_label = bb'.bb_label /\
          bb0.bb_instructions <> [] /\
          LAST bb'.bb_instructions = LAST bb0.bb_instructions
Proof
  ntac 2 gen_tac >> Induct_on `succs`
  >- (rw[update_succ_phi_labels_def] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >>
  (* Rewrite MEM: uspl...h::succs -> uspl...(case lookup)...succs *)
  qpat_x_assum `MEM bb' _` mp_tac >>
  PURE_REWRITE_TAC[update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs`
  >- ((* NONE: bbs unchanged *)
      ASM_REWRITE_TAC[optionTheory.option_case_def] >>
      strip_tac >>
      first_x_assum match_mp_tac >> rpt conj_tac >>
      first_assum ACCEPT_TAC)
  >> (* SOME sbb: one replace_block step *)
  ASM_REWRITE_TAC[optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  qabbrev_tac `bbs' = replace_block h
    (sbb with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst)
       sbb.bb_instructions) bbs` >>
  strip_tac >>
  (* IH gives bb0 in bbs'; chain back to bbs via helper *)
  first_x_assum (qspecl_then [`bbs'`, `bb'`] mp_tac) >>
  (* Derive bbs' properties from Abbrev without expanding replace_block *)
  `!b. MEM b bbs' ==> bb_well_formed b` by
    (qpat_x_assum `Abbrev (bbs' = _)` (SUBST1_TAC o
       REWRITE_RULE[markerTheory.Abbrev_def]) >>
     metis_tac[wf_replace_block_phi_subst]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs')` by
    (qpat_x_assum `Abbrev (bbs' = _)` (SUBST1_TAC o
       REWRITE_RULE[markerTheory.Abbrev_def]) >>
     irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
     simp[] >> metis_tac[venomExecProofsTheory.lookup_block_label]) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  (* bb0 in bbs' -> chain back to bbs via helper *)
  mp_tac replace_block_phi_subst_LAST_back >>
  disch_then (qspecl_then [`h`, `old`, `new`, `sbb`, `bbs`, `bb0`] mp_tac) >>
  (impl_tac
   >- (conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qpat_x_assum `Abbrev (bbs' = _)` (SUBST_ALL_TAC o
         REWRITE_RULE[markerTheory.Abbrev_def]) >>
       simp[])) >>
  strip_tac >>
  qexists `bb00` >> simp[] >> metis_tac[]
QED

(* ================================================================
   Section: fn_labels through merge step
   ================================================================ *)

(* merge_blocks preserves bb_label *)
Theorem merge_blocks_label[local]:
  !a b. (merge_blocks a b).bb_label = a.bb_label
Proof
  rw[merge_blocks_def]
QED

(* fn_labels through the full merge step *)
Theorem fn_labels_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    ALL_DISTINCT (fn_labels func) ==>
    fn_labels (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) =
    fn_labels (func with fn_blocks :=
      replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks))
Proof
  rpt strip_tac >>
  simp[fn_labels_def,
       simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels]
QED

(* ================================================================
   Section: fn_succs_closed through merge step (KEY LEMMA)

   Core argument: num_preds func next_lbl = 1 means only bb
   references next_lbl. After merge, bb is replaced by merged
   (with bb_succs next_bb), and next_lbl is removed. Since no
   other block references next_lbl, removing it is safe.
   ================================================================ *)

(* If num_preds = 1 and bb is a predecessor, then bb is the ONLY predecessor *)
Theorem num_preds_1_unique[local]:
  !func lbl bb.
    num_preds func lbl = 1 /\
    MEM bb func.fn_blocks /\
    MEM lbl (bb_succs bb) ==>
    !b. MEM b func.fn_blocks /\ MEM lbl (bb_succs b) ==> b = bb
Proof
  rw[num_preds_def, block_preds_def] >>
  `MEM bb (FILTER (\bb. MEM lbl (bb_succs bb)) func.fn_blocks)` by
    simp[listTheory.MEM_FILTER] >>
  `MEM b (FILTER (\bb. MEM lbl (bb_succs bb)) func.fn_blocks)` by
    simp[listTheory.MEM_FILTER] >>
  Cases_on `FILTER (\bb. MEM lbl (bb_succs bb)) func.fn_blocks` >> fs[] >>
  Cases_on `t` >> fs[listTheory.MEM]
QED

(* fn_succs_closed: removing a label that only one block references *)
(* After merge step, we need fn_succs_closed for the new function.
   Strategy: show each block's successors are still in fn_labels. *)

(* Helper: bb_succs of merge_blocks *)
Theorem bb_succs_merge_blocks[local]:
  !a b. bb_well_formed b ==>
    bb_succs (merge_blocks a b) = bb_succs b
Proof
  rw[merge_blocks_def, bb_succs_def] >>
  fs[bb_well_formed_def] >>
  Cases_on `b.bb_instructions` >> fs[] >>
  `LAST (FRONT a.bb_instructions ++ h::t) = LAST (h::t)` by
    simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
  `FRONT a.bb_instructions ++ h::t <> []` by simp[] >>
  Cases_on `FRONT a.bb_instructions ++ h::t` >> fs[]
QED

(* ================================================================
   Section: fn_inst_ids_distinct through merge step
   FRONT(a) ++ b has inst_ids that are a subset of a ++ b.
   ================================================================ *)

(* FRONT preserves MAP relationship *)
Theorem MAP_FRONT[local]:
  !f l. l <> [] ==> MAP f (FRONT l) = FRONT (MAP f l)
Proof
  gen_tac >> Induct >> simp[] >>
  Cases_on `l = []` >> simp[listTheory.FRONT_DEF]
QED

(* PERM: MAP inst_id (FRONT a ++ b) is related to MAP inst_id (a ++ b) *)
Theorem inst_ids_merge_perm[local]:
  !a b. a <> [] ==>
    MAP (\i. i.inst_id) (FRONT a ++ b) =
    FRONT (MAP (\i. i.inst_id) a) ++ MAP (\i. i.inst_id) b
Proof
  rpt strip_tac >>
  simp[listTheory.MAP_APPEND] >>
  simp[MAP_FRONT]
QED

(* ALL_DISTINCT of FRONT l when ALL_DISTINCT l *)
Theorem ALL_DISTINCT_FRONT[local]:
  !l. ALL_DISTINCT l /\ l <> [] ==> ALL_DISTINCT (FRONT l)
Proof
  Induct >> simp[] >>
  Cases_on `l = []` >> simp[listTheory.FRONT_DEF] >>
  rpt strip_tac >> fs[] >>
  metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]
QED

(* ALL_DISTINCT of FRONT a ++ b when ALL_DISTINCT (a ++ b) *)
Theorem ALL_DISTINCT_FRONT_APPEND[local]:
  !a b. ALL_DISTINCT (a ++ b) /\ a <> [] ==>
    ALL_DISTINCT (FRONT a ++ b)
Proof
  rpt strip_tac >>
  fs[listTheory.ALL_DISTINCT_APPEND] >>
  simp[listTheory.ALL_DISTINCT_APPEND] >> rpt conj_tac
  >| [
    irule ALL_DISTINCT_FRONT >> simp[],
    rpt strip_tac >>
    `MEM e a` by metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
    metis_tac[]
  ]
QED

(* Helper: per-block inst_ids preserved by subst_label_inst phi-conditional *)
Theorem subst_phi_inst_ids[local]:
  !old new insts.
    MAP (\i. i.inst_id)
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst) insts) =
    MAP (\i. i.inst_id) insts
Proof
  ntac 2 gen_tac >> Induct >> simp[] >>
  rpt strip_tac >> rw[] >> simp[subst_label_inst_id]
QED

(* FOLDL of update_succ_phi_labels preserves inst_ids *)
Theorem FOLDL_update_phi_preserves_inst_ids[local]:
  !succs old new bbs.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (FOLDL (\bs s.
         case lookup_block s bs of
           NONE => bs
         | SOME sbb =>
             replace_block s
               (sbb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                              else subst_label_inst old new inst)
                      sbb.bb_instructions) bs) bbs succs) =
    MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs
Proof
  Induct >> rw[] >>
  Cases_on `lookup_block h bbs` >> fs[] >>
  (* SOME case *)
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  qabbrev_tac `bbs' = replace_block h
    (x with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst)
      x.bb_instructions) bbs` >>
  (* ALL_DISTINCT preserved *)
  SUBGOAL_THEN ``ALL_DISTINCT (MAP (\b. b.bb_label) bbs')`` ASSUME_TAC
  >| [
    simp[Abbr `bbs'`] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> simp[],
    ALL_TAC] >>
  first_x_assum (qspecl_then [`old`, `new`, `bbs'`] mp_tac) >>
  simp[] >> disch_tac >>
  (* show replace_block preserves MAP inst_ids *)
  SUBGOAL_THEN ``MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs' =
                 MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs``
    (fn th => fs[th]) >>
  simp[Abbr `bbs'`, cfgTransformTheory.replace_block_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF,
       listTheory.MAP_EQ_f] >>
  rpt strip_tac >> rw[] >>
  (* bb.bb_label = x.bb_label, so bb = x by uniqueness *)
  `bb = x` by metis_tac[ALL_DISTINCT_MAP_eq] >>
  rw[] >> simp[subst_phi_inst_ids]
QED

(* subst_label_inst preserves inst_ids through update_succ_phi_labels *)
Theorem update_succ_phi_labels_inst_ids[local]:
  !old new bbs succs.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (update_succ_phi_labels old new bbs succs) =
    MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs
Proof
  rw[update_succ_phi_labels_def, LET_THM] >>
  irule FOLDL_update_phi_preserves_inst_ids >> simp[]
QED

(* ================================================================
   Section: General replace_block/remove_block helpers
   ================================================================ *)

(* Characterize MEM in replace_block *)
(* MEM_replace_block, MEM_replace_remove, MEM_replace_block_new,
   MEM_replace_block_other, MEM_remove_block_intro are in
   simplifyCfgHelpersTheory (opened via Libs). *)

(* ================================================================
   Section: wf_function through merge step (all 5 properties)
   Sub-lemmas for each wf_function conjunct, then combined.
   ================================================================ *)

(* 1. ALL_DISTINCT fn_labels *)
Theorem ALL_DISTINCT_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb ==>
    ALL_DISTINCT (fn_labels (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))))
Proof
  rpt strip_tac >>
  simp[fn_labels_def,
       simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
  simp[merge_blocks_label] >>
  irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
  fs[wf_function_def, fn_labels_def]
QED

(* Helper: update_succ_phi_labels preserves length *)
Theorem LENGTH_update_succ_phi_labels[local]:
  !old new bbs succs.
    LENGTH (update_succ_phi_labels old new bbs succs) = LENGTH bbs
Proof
  rpt gen_tac >>
  `MAP (\bb. bb.bb_label) (update_succ_phi_labels old new bbs succs) =
   MAP (\bb. bb.bb_label) bbs` by
    simp[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
  metis_tac[listTheory.LENGTH_MAP]
QED

(* 2. fn_has_entry: fn_blocks <> [] because entry block survives *)
Theorem fn_has_entry_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_has_entry (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt strip_tac >>
  simp[fn_has_entry_def] >>
  SUBGOAL_THEN ``LENGTH (update_succ_phi_labels next_lbl lbl
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks))
     (bb_succs (merge_blocks bb next_bb))) > 0`` mp_tac
  >- (
    simp[LENGTH_update_succ_phi_labels,
         cfgTransformTheory.replace_block_def, listTheory.LENGTH_MAP] >>
    fs[wf_function_def, fn_has_entry_def, can_merge_blocks_def] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >>
    gvs[] >>
    Cases_on `func.fn_blocks` >> fs[] >>
    simp[cfgTransformTheory.remove_block_def] >>
    (SUBGOAL_THEN ``h.bb_label <> next_bb.bb_label`` ASSUME_TAC
      >- fs[fn_entry_label_def, entry_block_def]) >>
    simp[]
  ) >>
  Cases_on `update_succ_phi_labels next_lbl lbl
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks))
     (bb_succs (merge_blocks bb next_bb))` >> simp[]
QED

(* 3. bb_well_formed for all blocks *)
Theorem bb_well_formed_merge_step[local]:
  !func lbl next_lbl bb next_bb b.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    MEM b (update_succ_phi_labels next_lbl lbl
      (replace_block lbl (merge_blocks bb next_bb)
         (remove_block next_lbl func.fn_blocks))
      (bb_succs (merge_blocks bb next_bb))) ==>
    bb_well_formed b
Proof
  rpt strip_tac >>
  irule bb_well_formed_update_succ_phi_labels >>
  qexistsl_tac [
    `replace_block lbl (merge_blocks bb next_bb)
       (remove_block next_lbl func.fn_blocks)`,
    `lbl`, `next_lbl`,
    `bb_succs (merge_blocks bb next_bb)`] >> simp[] >>
  rpt strip_tac >>
  imp_res_tac MEM_replace_remove >> gvs[] >| [
    (* merged block *)
    irule simplifyCfgHelpersTheory.bb_well_formed_merge_blocks >>
    imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
    fs[wf_function_def, can_merge_blocks_def] >> res_tac,
    (* original block *)
    fs[wf_function_def] >> res_tac
  ]
QED

(* 4. fn_succs_closed *)
(* Strategy:
   - update_succ_phi_labels preserves MAP bb_succs and MAP bb_label
   - So fn_succs_closed of result = fn_succs_closed of mid
   - mid = replace_block lbl merged (remove_block next_lbl blocks)
   - Every block in mid has label <> next_lbl
   - For merged block (label = lbl <> next_lbl when it exists):
     bb_succs = bb_succs(next_bb), and next_lbl not in them (self-loop exclusion:
     bb <> next_bb because merged block only exists when lbl <> next_lbl)
   - For other blocks: next_lbl not in succs (num_preds_1_unique: bb is unique pred)
*)

(* Helper: every block in replace_block(remove_block) has next_lbl not in succs *)
Theorem no_next_lbl_in_succs_mid[local]:
  !func bb next_bb b succ.
    wf_function func /\
    can_merge_blocks func bb next_bb /\
    MEM bb func.fn_blocks /\ MEM next_bb func.fn_blocks /\
    MEM b (replace_block bb.bb_label (merge_blocks bb next_bb)
             (remove_block next_bb.bb_label func.fn_blocks)) /\
    MEM succ (bb_succs b) ==>
    succ <> next_bb.bb_label
Proof
  rpt strip_tac >> rw[] >>
  imp_res_tac MEM_replace_remove >> gvs[] >>
  fs[can_merge_blocks_def] >>
  `bb_well_formed next_bb` by (fs[wf_function_def] >> res_tac) >>
  `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by
    metis_tac[bb_succs_merge_blocks] >>
  fs[] >>
  `!x. MEM x func.fn_blocks /\ MEM next_bb.bb_label (bb_succs x) ==>
       x = bb` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`func`, `next_bb.bb_label`, `bb`] num_preds_1_unique) >>
     simp[]) >>
  metis_tac[]
QED

(* fn_succs_closed for mid = replace_block + remove_block *)
Theorem fn_succs_closed_mid[local]:
  !func bb next_bb b succ.
    wf_function func /\
    can_merge_blocks func bb next_bb /\
    MEM bb func.fn_blocks /\ MEM next_bb func.fn_blocks /\
    MEM b (replace_block bb.bb_label (merge_blocks bb next_bb)
             (remove_block next_bb.bb_label func.fn_blocks)) /\
    MEM succ (bb_succs b) ==>
    MEM succ (fn_labels (func with fn_blocks :=
      replace_block bb.bb_label (merge_blocks bb next_bb)
        (remove_block next_bb.bb_label func.fn_blocks)))
Proof
  rpt strip_tac >>
  (SUBGOAL_THEN ``succ <> next_bb.bb_label`` ASSUME_TAC
   >- (metis_tac[no_next_lbl_in_succs_mid])) >>
  (* Get MEM succ (fn_labels func) via fn_succs_closed *)
  (SUBGOAL_THEN ``MEM succ (fn_labels func)`` ASSUME_TAC >- (
    imp_res_tac MEM_replace_remove >> gvs[]
    >- (
      (* b = merged block: bb_succs(merge) = bb_succs(next_bb) *)
      (SUBGOAL_THEN ``bb_well_formed next_bb`` ASSUME_TAC
       >- (fs[wf_function_def] >> res_tac)) >>
      imp_res_tac bb_succs_merge_blocks >>
      fs[wf_function_def, fn_succs_closed_def] >> metis_tac[]
    ) >>
    (* b = original block *)
    fs[wf_function_def, fn_succs_closed_def] >> metis_tac[]
  )) >>
  (* Now rewrite fn_labels through replace_block/remove_block *)
  fs[fn_labels_def, cfgTransformProofsTheory.fn_labels_replace_block,
     merge_blocks_label, cfgTransformProofsTheory.fn_labels_remove_block,
     listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

(*
  Helper: fn_succs_closed depends only on MAP bb_label and MAP bb_succs
  of fn_blocks. If both are preserved, fn_succs_closed is preserved.
*)
Theorem fn_succs_closed_same_labels_succs[local]:
  !bbs1 bbs2 func.
    MAP (\b. b.bb_label) bbs1 = MAP (\b. b.bb_label) bbs2 /\
    MAP bb_succs bbs1 = MAP bb_succs bbs2 /\
    fn_succs_closed (func with fn_blocks := bbs2) ==>
    fn_succs_closed (func with fn_blocks := bbs1)
Proof
  rpt strip_tac >>
  qpat_x_assum `fn_succs_closed _` mp_tac >>
  simp[fn_succs_closed_def, fn_labels_def] >>
  qpat_x_assum `MAP (\b. b.bb_label) _ = _` (SUBST1_TAC o SYM) >>
  rpt strip_tac >>
  (* Have: MEM bb bbs1, MEM succ (bb_succs bb) *)
  (* Have: !bb succ. MEM bb bbs2 /\ MEM succ (bb_succs bb) ==> result *)
  (* Need: find bb2 in bbs2 with MEM succ (bb_succs bb2) *)
  (* succ in bb_succs bb, bb in bbs1, MAP bb_succs bbs1 = bbs2 *)
  (* => succ in FLAT(MAP bb_succs bbs2) => exists bb2 in bbs2 *)
  (SUBGOAL_THEN ``MEM succ (FLAT (MAP bb_succs bbs2))`` ASSUME_TAC >- (
    qpat_x_assum `MAP bb_succs _ = _` (SUBST1_TAC o SYM) >>
    simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    qexists_tac `bb_succs bb` >> simp[] >>
    qexists_tac `bb` >> simp[])) >>
  fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  first_x_assum (qspecl_then [`y`, `succ`] mp_tac) >>
  simp[] >> strip_tac >> metis_tac[]
QED

(*
  Helper: fn_succs_closed is preserved by update_succ_phi_labels when
  the underlying blocks (mid) already satisfy fn_succs_closed,
  all blocks in mid are well-formed, and labels are ALL_DISTINCT.
*)
Theorem fn_succs_closed_update_succ_phi_labels[local]:
  !func old new mid succs.
    fn_succs_closed (func with fn_blocks := mid) /\
    (!b. MEM b mid ==> bb_well_formed b) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) mid) ==>
    fn_succs_closed (func with fn_blocks :=
      update_succ_phi_labels old new mid succs)
Proof
  rpt strip_tac >>
  irule fn_succs_closed_same_labels_succs >>
  qexists_tac `mid` >>
  simp[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
  irule MAP_bb_succs_update_succ_phi_labels >> simp[]
QED

Theorem fn_succs_closed_mid_fn[local]:
  !func bb next_bb.
    wf_function func /\
    can_merge_blocks func bb next_bb /\
    MEM bb func.fn_blocks /\ MEM next_bb func.fn_blocks ==>
    fn_succs_closed (func with fn_blocks :=
      replace_block bb.bb_label (merge_blocks bb next_bb)
        (remove_block next_bb.bb_label func.fn_blocks))
Proof
  rw[fn_succs_closed_def] >> rpt strip_tac >>
  irule fn_succs_closed_mid >> simp[] >>
  qexists_tac `bb'` >> simp[]
QED

Theorem bb_well_formed_mid[local]:
  !func bb next_bb b.
    wf_function func /\
    can_merge_blocks func bb next_bb /\
    MEM bb func.fn_blocks /\ MEM next_bb func.fn_blocks /\
    MEM b (replace_block bb.bb_label (merge_blocks bb next_bb)
             (remove_block next_bb.bb_label func.fn_blocks)) ==>
    bb_well_formed b
Proof
  rpt strip_tac >> imp_res_tac MEM_replace_remove >> gvs[]
  >- (
    irule simplifyCfgHelpersTheory.bb_well_formed_merge_blocks >>
    fs[wf_function_def, can_merge_blocks_def] >> res_tac
  )
  >> fs[wf_function_def] >> res_tac
QED

Theorem ALL_DISTINCT_mid[local]:
  !func bb next_bb.
    wf_function func /\
    MEM bb func.fn_blocks /\ MEM next_bb func.fn_blocks ==>
    ALL_DISTINCT (MAP (\b. b.bb_label)
      (replace_block bb.bb_label (merge_blocks bb next_bb)
        (remove_block next_bb.bb_label func.fn_blocks)))
Proof
  rpt strip_tac >>
  irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
  simp[merge_blocks_label] >>
  irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
  fs[wf_function_def, fn_labels_def]
QED

Theorem fn_succs_closed_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_succs_closed (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >> gvs[] >>
  irule fn_succs_closed_update_succ_phi_labels >> rpt conj_tac
  >- (rpt strip_tac >> irule bb_well_formed_mid >> metis_tac[])
  >- (irule ALL_DISTINCT_mid >> simp[])
  >> irule fn_succs_closed_mid_fn >> simp[]
QED

(* Helper: every element in merged inst_ids came from bb or next_bb *)
Theorem MEM_merge_blocks_inst_ids[local]:
  !bb next_bb x. bb.bb_instructions <> [] /\
    MEM x (MAP (\i. i.inst_id) (merge_blocks bb next_bb).bb_instructions) ==>
    MEM x (MAP (\i. i.inst_id) bb.bb_instructions) \/
    MEM x (MAP (\i. i.inst_id) next_bb.bb_instructions)
Proof
  rw[simplifyCfgDefsTheory.merge_blocks_def,
     listTheory.MAP_APPEND, listTheory.MEM_APPEND,
     listTheory.MEM_MAP] >>
  imp_res_tac rich_listTheory.MEM_FRONT_NOT_NIL >> metis_tac[]
QED

(* Helper: merged inst_ids are ALL_DISTINCT *)
Theorem ALL_DISTINCT_merge_blocks_inst_ids[local]:
  !bb next_bb.
    bb.bb_instructions <> [] /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions ++
                  MAP (\i. i.inst_id) next_bb.bb_instructions) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (merge_blocks bb next_bb).bb_instructions)
Proof
  rw[simplifyCfgDefsTheory.merge_blocks_def, listTheory.MAP_APPEND,
     listTheory.MAP_FRONT] >>
  match_mp_tac ALL_DISTINCT_FRONT_APPEND >>
  simp[listTheory.MAP_EQ_NIL]
QED

(* Helper: every element of FLAT(MAP f (replace+remove result)) was in
   FLAT(MAP f bbs) originally *)
Theorem MEM_FLAT_MAP_replace_remove[local]:
  !f lbl new_b nlbl bbs x.
    MEM x (FLAT (MAP f (replace_block lbl new_b (remove_block nlbl bbs)))) /\
    (!y. MEM y (f new_b) ==>
      (?b. MEM b bbs /\ MEM y (f b))) ==>
    MEM x (FLAT (MAP f bbs))
Proof
  ntac 4 gen_tac >>
  Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def,
     cfgTransformTheory.remove_block_def,
     listTheory.FILTER, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  TRY (Cases_on `bb.bb_label = lbl` >> gvs[]) >>
  TRY (res_tac >> qexists_tac `f b` >> simp[] >> metis_tac[]) >>
  TRY (qexists_tac `f bb` >> simp[] >>
       imp_res_tac listTheory.MEM_FILTER >> metis_tac[])
QED

(* Helper: MEM in FLAT(MAP f (replace_block)) implies MEM in original or f(new_b) *)
Theorem MEM_FLAT_MAP_replace[local]:
  !f lbl new_b bbs x.
    MEM x (FLAT (MAP f (replace_block lbl new_b bbs))) ==>
    MEM x (f new_b) \/ MEM x (FLAT (MAP f bbs))
Proof
  ntac 3 gen_tac >>
  Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  Cases_on `h.bb_label = lbl` >> gvs[] >>
  res_tac >> metis_tac[]
QED

(* ALL_DISTINCT FLAT through remove_block *)
Theorem ALL_DISTINCT_FLAT_remove[local]:
  !f lbl bbs.
    ALL_DISTINCT (FLAT (MAP f bbs)) ==>
    ALL_DISTINCT (FLAT (MAP f (remove_block lbl bbs)))
Proof
  ntac 2 gen_tac >> Induct_on `bbs` >>
  rw[cfgTransformTheory.remove_block_def, listTheory.FILTER] >>
  fs[listTheory.ALL_DISTINCT_APPEND] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.remove_block_def] >>
  simp[listTheory.ALL_DISTINCT_APPEND] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  fs[listTheory.MEM_FLAT, listTheory.MEM_MAP,
     cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

(* When no block has label lbl, replace_block is identity *)
Theorem replace_block_id[local]:
  !lbl new_b bbs.
    ~MEM lbl (MAP (\b. b.bb_label) bbs) ==>
    replace_block lbl new_b bbs = bbs
Proof
  Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.replace_block_def] >>
  res_tac >> gvs[]
QED

(* replace_block after remove_block with same label is identity *)
Theorem replace_block_remove_same[local]:
  !lbl x bbs. replace_block lbl x (remove_block lbl bbs) = remove_block lbl bbs
Proof
  Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def,
     cfgTransformTheory.remove_block_def] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.replace_block_def,
                   GSYM cfgTransformTheory.remove_block_def] >>
  gvs[]
QED

(* When f(new_b) = f(old_b), replace_block preserves MAP f exactly. *)
Theorem MAP_replace_block_same[local]:
  !f lbl new_b bbs.
    (!b. MEM b bbs /\ b.bb_label = lbl ==> f new_b = f b) ==>
    MAP f (replace_block lbl new_b bbs) = MAP f bbs
Proof
  ntac 3 gen_tac >> Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.replace_block_def] >>
  res_tac >> gvs[]
QED

(* Corollary: FLAT version *)
Theorem FLAT_MAP_replace_block_same[local]:
  !f lbl new_b bbs.
    (!b. MEM b bbs /\ b.bb_label = lbl ==> f new_b = f b) ==>
    FLAT (MAP f (replace_block lbl new_b bbs)) = FLAT (MAP f bbs)
Proof
  metis_tac[MAP_replace_block_same]
QED

(* ALL_DISTINCT FLAT through replace_block.
   Requires ALL_DISTINCT labels (at most one block replaced)
   and that f(new_b) elements come from the replaced block. *)
Theorem ALL_DISTINCT_FLAT_replace[local]:
  !f lbl new_b bbs.
    ALL_DISTINCT (FLAT (MAP f bbs)) /\
    ALL_DISTINCT (MAP (\blk. blk.bb_label) bbs) /\
    ALL_DISTINCT (f new_b) /\
    (!x. MEM x (f new_b) ==>
      (?blk. MEM blk bbs /\ blk.bb_label = lbl /\ MEM x (f blk))) ==>
    ALL_DISTINCT (FLAT (MAP f (replace_block lbl new_b bbs)))
Proof
  ntac 3 gen_tac >>
  Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def] >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.replace_block_def] >>
  rpt strip_tac
  >- (imp_res_tac replace_block_id >> gvs[])
  >- (imp_res_tac replace_block_id >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      fs[listTheory.MEM_MAP] >> metis_tac[])
  (* Goal 3: h.bb_label<>lbl, ALL_DISTINCT via IH *)
  >- (first_x_assum match_mp_tac >>
      rpt strip_tac >> res_tac >> gvs[] >>
      fs[listTheory.MEM_MAP] >> metis_tac[])
  (* Goal 4: h.bb_label<>lbl, disjointness contradiction *)
  >> (imp_res_tac MEM_FLAT_MAP_replace >> gvs[]
      >- (res_tac >> gvs[] >>
          fs[listTheory.MEM_MAP, listTheory.MEM_FLAT] >> metis_tac[])
      >> res_tac)
QED

(* Weaker variant: only need containment for elements also in FLAT(MAP f bbs).
   "Fresh" elements (only in new_b) are fine. *)
Theorem ALL_DISTINCT_FLAT_replace_weak[local]:
  !f lbl new_b bbs.
    ALL_DISTINCT (FLAT (MAP f bbs)) /\
    ALL_DISTINCT (MAP (\blk. blk.bb_label) bbs) /\
    ALL_DISTINCT (f new_b) /\
    (!x. MEM x (f new_b) /\ MEM x (FLAT (MAP f bbs)) ==>
      (?blk. MEM blk bbs /\ blk.bb_label = lbl /\ MEM x (f blk))) ==>
    ALL_DISTINCT (FLAT (MAP f (replace_block lbl new_b bbs)))
Proof
  ntac 3 gen_tac >>
  Induct_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def] >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.replace_block_def] >>
  rpt strip_tac
  (* h.bb_label = lbl case: replace_block on tail is identity *)
  >- (imp_res_tac replace_block_id >> gvs[])
  >- (imp_res_tac replace_block_id >> gvs[] >> res_tac >>
      gvs[] >> fs[listTheory.MEM_MAP] >> metis_tac[])
  (* h.bb_label <> lbl case *)
  >- (first_x_assum match_mp_tac >>
      rpt strip_tac >> gvs[] >> res_tac >>
      gvs[] >> fs[listTheory.MEM_MAP] >> metis_tac[])
  >> (imp_res_tac MEM_FLAT_MAP_replace >> gvs[]
      >- (res_tac >> gvs[] >>
          fs[listTheory.MEM_MAP, listTheory.MEM_FLAT] >> metis_tac[])
      >> res_tac)
QED

(* ALL_DISTINCT of FLAT implies ALL_DISTINCT of each member's image *)
Theorem ALL_DISTINCT_FLAT_member[local]:
  !f b bbs. ALL_DISTINCT (FLAT (MAP f bbs)) /\ MEM b bbs ==>
    ALL_DISTINCT (f b)
Proof
  ntac 2 gen_tac >> Induct_on `bbs` >>
  rw[] >> gvs[listTheory.ALL_DISTINCT_APPEND]
QED

(* Elements from different blocks in ALL_DISTINCT FLAT don't overlap *)
Theorem ALL_DISTINCT_FLAT_disjoint[local]:
  !f b1 b2 bbs x.
    ALL_DISTINCT (FLAT (MAP f bbs)) /\
    MEM b1 bbs /\ MEM b2 bbs /\ b1 <> b2 /\
    MEM x (f b1) ==>
    ~MEM x (f b2)
Proof
  ntac 3 gen_tac >>
  Induct_on `bbs` >>
  rw[] >> gvs[listTheory.ALL_DISTINCT_APPEND]
  >- (fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
  >- (fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
  >> metis_tac[]
QED

(* ALL_DISTINCT of combined images from two distinct members *)
Theorem ALL_DISTINCT_FLAT_two_members[local]:
  !f b1 b2 bbs. ALL_DISTINCT (FLAT (MAP f bbs)) /\
    MEM b1 bbs /\ MEM b2 bbs /\ b1 <> b2 ==>
    ALL_DISTINCT (f b1 ++ f b2)
Proof
  rpt strip_tac >>
  simp[listTheory.ALL_DISTINCT_APPEND] >>
  rpt conj_tac
  >- (irule ALL_DISTINCT_FLAT_member >> metis_tac[])
  >- (irule ALL_DISTINCT_FLAT_member >> metis_tac[])
  >> metis_tac[ALL_DISTINCT_FLAT_disjoint]
QED

(* When label is not in the block list, remove_block is identity *)
Theorem remove_block_id[local]:
  !lbl bbs.
    ~MEM lbl (MAP (\b. b.bb_label) bbs) ==>
    remove_block lbl bbs = bbs
Proof
  Induct_on `bbs` >>
  rw[cfgTransformTheory.remove_block_def] >>
  PURE_REWRITE_TAC[GSYM cfgTransformTheory.remove_block_def] >>
  res_tac >> gvs[]
QED

(* MEM_remove_block_orig: use cfgTransformProofsTheory.MEM_remove_block *)
(* ALL_DISTINCT_MAP_label_remove: use cfgTransformProofsTheory.ALL_DISTINCT_remove_block *)

(* If x is in f(b) where b has label nlbl and is in bbs,
   then x is NOT in FLAT(MAP f (remove_block nlbl bbs)),
   because ALL_DISTINCT means x is only in f(b) and b is removed.
   Curried form for easy use with imp_res_tac. *)
Theorem removed_element_not_in_rest[local]:
  !f nlbl b bbs x.
    ALL_DISTINCT (FLAT (MAP f bbs)) ==>
    MEM b bbs ==> b.bb_label = nlbl ==> MEM x (f b) ==>
    ~MEM x (FLAT (MAP f (remove_block nlbl bbs)))
Proof
  rpt strip_tac >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  imp_res_tac cfgTransformProofsTheory.MEM_remove_block >>
  Cases_on `y = b`
  >- (gvs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER])
  >> (imp_res_tac ALL_DISTINCT_FLAT_disjoint >> gvs[])
QED

(* ALL_DISTINCT FLAT through replace+remove.
   Compositional: remove preserves ALL_DISTINCT, then apply replace_weak.
   Elements of new_b come from blocks with label lbl or nlbl. *)
Theorem ALL_DISTINCT_FLAT_replace_remove[local]:
  !f lbl new_b nlbl bbs.
    ALL_DISTINCT (FLAT (MAP f bbs)) /\
    ALL_DISTINCT (MAP (\blk. blk.bb_label) bbs) /\
    ALL_DISTINCT (f new_b) /\
    (!x. MEM x (f new_b) ==>
      (?blk. MEM blk bbs /\ (blk.bb_label = lbl \/ blk.bb_label = nlbl) /\
             MEM x (f blk))) ==>
    ALL_DISTINCT (FLAT (MAP f (replace_block lbl new_b
                                 (remove_block nlbl bbs))))
Proof
  rpt strip_tac >>
  (SUBGOAL_THEN ``ALL_DISTINCT (FLAT (MAP f (remove_block nlbl bbs)))``
   ASSUME_TAC >- (irule ALL_DISTINCT_FLAT_remove >> simp[])) >>
  (SUBGOAL_THEN ``ALL_DISTINCT (MAP (\blk. blk.bb_label)
     (remove_block nlbl bbs))`` ASSUME_TAC
   >- (irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >> simp[])) >>
  irule ALL_DISTINCT_FLAT_replace_weak >> simp[] >>
  rpt strip_tac >> res_tac
  >- (Cases_on `lbl = nlbl`
      >- (gvs[] >> imp_res_tac removed_element_not_in_rest >> gvs[])
      >> (qexists_tac `blk` >> gvs[] >>
          fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER]))
  >> (imp_res_tac removed_element_not_in_rest >> gvs[])
QED

(* Helper: two distinct blocks in a function with distinct inst_ids
   have ALL_DISTINCT combined inst_ids *)
(*  Workaround: irule/drule unify f wrongly on (f b) vs (MAP g (b.field)).
    This specialized lemma avoids ambiguity for inst_ids. *)
Theorem inst_ids_two_blocks_distinct[local]:
  !bb next_bb bbs.
    ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) /\
    MEM bb bbs /\ MEM next_bb bbs /\ bb <> next_bb ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions ++
                  MAP (\i. i.inst_id) next_bb.bb_instructions)
Proof
  rpt strip_tac >>
  mp_tac (ISPECL
    [``\(b:basic_block). MAP (\i. i.inst_id) b.bb_instructions``,
     ``bb:basic_block``, ``next_bb:basic_block``, ``bbs:basic_block list``]
    ALL_DISTINCT_FLAT_two_members) >>
  simp[]
QED

(* 5. fn_inst_ids_distinct through merge_step *)
Theorem fn_inst_ids_distinct_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_inst_ids_distinct (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >> gvs[] >>
  fs[wf_function_def] >>
  simp[fn_inst_ids_distinct_def] >>
  (* Reduce via update_succ_phi_labels_inst_ids *)
  (SUBGOAL_THEN ``ALL_DISTINCT (MAP (\b. b.bb_label)
    (replace_block bb.bb_label (merge_blocks bb next_bb)
       (remove_block next_bb.bb_label func.fn_blocks)))``
    ASSUME_TAC
  >- (fs[venomInstTheory.fn_labels_def] >>
      irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
      rw[merge_blocks_label] >>
      irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >> simp[])) >>
  imp_res_tac update_succ_phi_labels_inst_ids >> gvs[] >>
  (* Case split: self-loop (bb = next_bb) vs distinct blocks *)
  Cases_on `bb.bb_label = next_bb.bb_label`
  >- ((* Self-loop: replace is vacuous after remove of same label *)
      gvs[replace_block_remove_same] >>
      irule ALL_DISTINCT_FLAT_remove >>
      fs[fn_inst_ids_distinct_def])
  >> (* Distinct blocks: use ALL_DISTINCT_FLAT_replace_remove *)
  (SUBGOAL_THEN ``bb <> next_bb:basic_block`` ASSUME_TAC
   >- (strip_tac >> gvs[])) >>
  (SUBGOAL_THEN ``bb.bb_instructions <> []`` ASSUME_TAC
   >- (res_tac >> gvs[venomWfTheory.bb_well_formed_def])) >>
  irule ALL_DISTINCT_FLAT_replace_remove >>
  fs[fn_inst_ids_distinct_def, venomInstTheory.fn_labels_def] >>
  conj_tac
  >- ((* Containment: inst_ids of merge come from bb or next_bb *)
      rpt strip_tac >>
      drule_all MEM_merge_blocks_inst_ids >> strip_tac >> gvs[]
      >- (qexists_tac `bb` >> simp[])
      >> (qexists_tac `next_bb` >> simp[]))
  >> ((* ALL_DISTINCT (inst_ids (merge_blocks bb next_bb)) *)
      irule ALL_DISTINCT_merge_blocks_inst_ids >> simp[] >>
      irule inst_ids_two_blocks_distinct >> simp[] >>
      qexists_tac `func.fn_blocks` >> simp[])
QED

(* Intro lemma: avoids destructive wf_function_def rewriting *)
Theorem wf_function_intro[local]:
  !func. ALL_DISTINCT (fn_labels func) /\ fn_has_entry func /\
    (!bb. MEM bb func.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed func /\ fn_inst_ids_distinct func ==>
    wf_function func
Proof
  rw[wf_function_def]
QED

(* Combine all 5 properties *)
Theorem wf_function_merge_step:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    wf_function (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt strip_tac >>
  match_mp_tac wf_function_intro >> rpt conj_tac
  >- (match_mp_tac ALL_DISTINCT_merge_step >> simp[])
  >- (match_mp_tac fn_has_entry_merge_step >> simp[])
  >- (rpt strip_tac >> fs[] >> imp_res_tac bb_well_formed_merge_step)
  >- (match_mp_tac fn_succs_closed_merge_step >> simp[])
  >> match_mp_tac fn_inst_ids_distinct_merge_step >> simp[]
QED

(* ================================================================
   General: MAP f preserves bb_well_formed when f preserves inst_opcode.
   Used by all bb_well_formed-through-MAP proofs below.
   NOTE: irule works for non-lambda f; lambda f needs direct proof.
   ================================================================ *)

Theorem bb_well_formed_MAP_inst[local]:
  !f bb. (!i. (f i).inst_opcode = i.inst_opcode) ==>
    bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  rw[venomWfTheory.bb_well_formed_def] >>
  fs[listTheory.LAST_MAP] >>
  rpt strip_tac >>
  gvs[listTheory.EL_MAP] >>
  res_tac
QED

(* ================================================================
   Section: wf_function through bypass step (do_merge_jump)
   ================================================================ *)

(* Helper: update_phi_bypass preserves inst_opcode and inst_id *)
Theorem update_phi_bypass_opcode:
  !a_lbl b_lbl inst.
    (update_phi_bypass a_lbl b_lbl inst).inst_opcode = inst.inst_opcode
Proof
  rw[simplifyCfgDefsTheory.update_phi_bypass_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem update_phi_bypass_inst_id[local]:
  !a_lbl b_lbl inst.
    (update_phi_bypass a_lbl b_lbl inst).inst_id = inst.inst_id
Proof
  rw[simplifyCfgDefsTheory.update_phi_bypass_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* KEY: update_phi_bypass is identity on non-PHI instructions *)
Theorem update_phi_bypass_non_phi:
  !a_lbl b_lbl inst.
    inst.inst_opcode <> PHI ==>
    update_phi_bypass a_lbl b_lbl inst = inst
Proof
  rw[simplifyCfgDefsTheory.update_phi_bypass_def]
QED

(* KEY: The combined a-block transform (update_phi_bypass o cond_subst) preserves opcode *)
Theorem bypass_a_transform_opcode:
  !a_lbl b_lbl tgt_lbl inst.
    (update_phi_bypass a_lbl b_lbl
      (if ~is_terminator inst.inst_opcode then inst
       else subst_label_inst b_lbl tgt_lbl inst)).inst_opcode = inst.inst_opcode
Proof
  rpt strip_tac >> IF_CASES_TAC >>
  simp[update_phi_bypass_opcode, subst_label_inst_opcode]
QED

(* KEY: LAST through double MAP — outer MAP is identity on LAST (non-PHI) *)
Theorem LAST_a_block_bypass:
  !a_lbl b_lbl tgt_lbl bb.
    bb_well_formed bb ==>
    LAST (MAP (update_phi_bypass a_lbl b_lbl)
      (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                   else subst_label_inst b_lbl tgt_lbl inst)
        bb.bb_instructions)) =
    LAST (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                      else subst_label_inst b_lbl tgt_lbl inst)
          bb.bb_instructions)
Proof
  rpt strip_tac >>
  fs[venomWfTheory.bb_well_formed_def] >>
  simp[listTheory.LAST_MAP] >>
  irule update_phi_bypass_non_phi >>
  simp[cfgTransformProofsTheory.subst_label_inst_fields] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
  fs[venomInstTheory.is_terminator_def]
QED

(* KEY: bb_succs of the double-MAP a-block = bb_succs of single-MAP version.
   Since LAST is unchanged by the outer MAP (LAST_a_block_bypass),
   and bb_succs depends only on LAST (bb_succs_LAST_eq). *)
Theorem bb_succs_a_block_bypass:
  !a_lbl b_lbl tgt_lbl bb.
    bb_well_formed bb ==>
    bb_succs (bb with bb_instructions :=
      MAP (update_phi_bypass a_lbl b_lbl)
        (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                     else subst_label_inst b_lbl tgt_lbl inst)
          bb.bb_instructions)) =
    bb_succs (bb with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                   else subst_label_inst b_lbl tgt_lbl inst)
        bb.bb_instructions)
Proof
  rpt strip_tac >>
  irule bb_succs_LAST_eq >>
  `bb.bb_instructions <> []` by fs[venomWfTheory.bb_well_formed_def] >>
  simp[listTheory.MAP_EQ_NIL, LAST_a_block_bypass]
QED

(* Helper: conditional subst_label_inst preserves opcode and id *)
Theorem cond_subst_label_opcode:
  !old new inst.
    (if ~is_terminator inst.inst_opcode then inst
     else subst_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  rw[] >> simp[cfgTransformProofsTheory.subst_label_inst_fields]
QED

Theorem cond_subst_label_inst_id[local]:
  !old new inst.
    (if ~is_terminator inst.inst_opcode then inst
     else subst_label_inst old new inst).inst_id = inst.inst_id
Proof
  rw[] >> simp[cfgTransformProofsTheory.subst_label_inst_fields]
QED

(* bb_well_formed through do_merge_jump block transforms.
   Lambda case uses direct proof; non-lambda uses irule bb_well_formed_MAP_inst *)
Theorem bb_well_formed_cond_subst_label:
  !old new bb. bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst old new inst)
      bb.bb_instructions)
Proof
  rw[venomWfTheory.bb_well_formed_def] >>
  fs[listTheory.LAST_MAP,
     cfgTransformProofsTheory.subst_label_inst_fields] >>
  rpt strip_tac >>
  gvs[listTheory.EL_MAP] >>
  BasicProvers.every_case_tac >>
  gvs[cfgTransformProofsTheory.subst_label_inst_fields] >>
  res_tac >> fs[]
QED

Theorem bb_well_formed_update_phi_bypass:
  !a_lbl b_lbl bb. bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions :=
      MAP (update_phi_bypass a_lbl b_lbl) bb.bb_instructions)
Proof
  rpt strip_tac >> irule bb_well_formed_MAP_inst >>
  simp[update_phi_bypass_opcode]
QED

(* Helper: bb_succs unchanged through update_phi_bypass *)
Theorem bb_succs_update_phi_bypass:
  !a_lbl b_lbl bb. bb_well_formed bb ==>
    bb_succs (bb with bb_instructions :=
      MAP (update_phi_bypass a_lbl b_lbl) bb.bb_instructions) =
    bb_succs bb
Proof
  rpt strip_tac >> irule bb_succs_MAP_phi_only >>
  simp[update_phi_bypass_opcode] >>
  rw[simplifyCfgDefsTheory.update_phi_bypass_def]
QED

(* General: characterize MEM in MAP THE (FILTER IS_SOME (MAP f l)) *)
Theorem MEM_MAP_THE_FILTER_IS_SOME:
  !x f l. MEM x (MAP THE (FILTER IS_SOME (MAP f l))) <=>
          ?y. MEM y l /\ f y = SOME x
Proof
  gen_tac >> gen_tac >> Induct >> rw[] >>
  Cases_on `f h` >> simp[EQ_IMP_THM] >> rpt strip_tac >> gvs[] >>
  TRY (qexists_tac `h` >> simp[] >> NO_TAC) >>
  TRY (qexists_tac `y` >> simp[] >> NO_TAC) >>
  disj2_tac >> qexists_tac `y` >> simp[]
QED

(* bb_succs in terms of get_successors of last instruction *)
Theorem MEM_bb_succs_iff:
  !x bb. bb.bb_instructions <> [] ==>
    (MEM x (bb_succs bb) <=> MEM x (get_successors (LAST bb.bb_instructions)))
Proof
  rpt strip_tac >> Cases_on `bb.bb_instructions` >>
  fs[venomInstTheory.bb_succs_def, listTheory.MEM_nub,
     listTheory.MEM_REVERSE]
QED

(* subst_label_op never produces SOME old when old <> new *)
Theorem not_label_after_subst_op:
  !old new op. old <> new ==>
    get_label (subst_label_op old new op) <> SOME old
Proof
  Cases_on `op` >>
  rw[cfgTransformTheory.subst_label_op_def, venomStateTheory.get_label_def]
QED

(* After subst_label_inst, old label is removed from get_successors *)
Theorem not_MEM_get_successors_subst:
  !old new inst. old <> new ==>
    ~MEM old (get_successors (subst_label_inst old new inst))
Proof
  rw[get_successors_def,
     cfgTransformTheory.subst_label_inst_def, LET_THM,
     cfgTransformProofsTheory.subst_label_inst_fields,
     MEM_MAP_THE_FILTER_IS_SOME] >>
  rpt strip_tac >>
  fs[listTheory.MEM_MAP] >>
  imp_res_tac not_label_after_subst_op >> gvs[]
QED

(* Forward: subst_label_inst maps successors old→new, preserves others *)
Theorem MEM_get_successors_subst_forward:
  !old new x inst. MEM x (get_successors inst) ==>
    MEM (if x = old then new else x)
      (get_successors (subst_label_inst old new inst))
Proof
  rw[get_successors_def, cfgTransformTheory.subst_label_inst_def, LET_THM,
     cfgTransformProofsTheory.subst_label_inst_fields,
     MEM_MAP_THE_FILTER_IS_SOME] >>
  fs[listTheory.MEM_MAP] >>
  Cases_on `y` >> fs[venomStateTheory.get_label_def] >> gvs[]
  >- ((* x = old: witness subst_label_op old new (Label old) = Label new *)
    qexists_tac `Label new` >>
    rw[venomStateTheory.get_label_def] >>
    qexists_tac `Label old` >>
    simp[cfgTransformTheory.subst_label_op_def])
  >> ((* x = s ≠ old: witness subst_label_op old new (Label s) = Label s *)
    qexists_tac `Label s` >>
    rw[venomStateTheory.get_label_def] >>
    qexists_tac `Label s` >>
    simp[cfgTransformTheory.subst_label_op_def])
QED

(* Forward: conditional subst maps successors in bb_succs *)
Theorem MEM_bb_succs_cond_subst_forward:
  !old new x bb. bb_well_formed bb /\ MEM x (bb_succs bb) ==>
    MEM (if x = old then new else x)
      (bb_succs (bb with bb_instructions :=
        MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                    else subst_label_inst old new inst)
        bb.bb_instructions))
Proof
  rpt strip_tac >>
  fs[venomWfTheory.bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  fs[MEM_bb_succs_iff] >>
  `is_terminator (LAST (h::t)).inst_opcode` by fs[] >>
  (* Fold goal's (f h :: MAP f t) back to MAP f (h::t) for LAST_MAP *)
  `(if ~is_terminator h.inst_opcode then h
    else subst_label_inst old new h)::
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) t =
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) (h::t)` by
    simp[] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  PURE_REWRITE_TAC[listTheory.LAST_MAP] >>
  fs[] >>
  irule MEM_get_successors_subst_forward >> simp[]
QED

(* After conditional subst_label_inst, old label not in bb_succs *)
Theorem not_MEM_bb_succs_cond_subst:
  !old new bb. bb_well_formed bb /\ old <> new ==>
    ~MEM old (bb_succs (bb with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst old new inst)
      bb.bb_instructions))
Proof
  rw[bb_succs_def, venomWfTheory.bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  (* Rewrite cons back to MAP for LAST_MAP *)
  `(if ~is_terminator h.inst_opcode then h
    else subst_label_inst old new h)::
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) t =
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) (h::t)` by
    simp[] >>
  pop_assum SUBST1_TAC >>
  simp[listTheory.LAST_MAP, not_MEM_get_successors_subst]
QED

(* Helper: bypass target cannot be b itself (self-loop impossible with num_preds=1)
   If b has 1 predecessor and a has 2 successors (a <> b since num_succs differs),
   yet both a and b reach b, then num_preds >= 2, contradiction. *)
Theorem target_neq_b_bypass:
  !func a b target_lbl target.
    wf_function func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    lookup_block target_lbl func.fn_blocks = SOME target ==>
    target_lbl <> b.bb_label
Proof
  rw[can_bypass_jump_def] >>
  strip_tac >> gvs[] >>
  fs[num_preds_def, block_preds_def] >>
  (* a <> b since num_succs a = 2 but num_succs b = 1 *)
  `a <> b` by (strip_tac >> gvs[] >> fs[num_succs_def]) >>
  (* Both a and b are in the FILTER, but LENGTH = 1 *)
  `MEM a (FILTER (\bb'. MEM b.bb_label (bb_succs bb')) func.fn_blocks)` by
    fs[listTheory.MEM_FILTER] >>
  `MEM b (FILTER (\bb'. MEM b.bb_label (bb_succs bb')) func.fn_blocks)` by
    fs[listTheory.MEM_FILTER] >>
  (* LENGTH 1 list has exactly one element; both a and b are in it => a = b *)
  Cases_on `FILTER (\bb'. MEM b.bb_label (bb_succs bb')) func.fn_blocks` >> fs[] >>
  Cases_on `t` >> fs[listTheory.MEM]
QED

(* Helper: get_label after subst_label_op *)
Theorem get_label_subst_label_op:
  !old new op s. get_label (subst_label_op old new op) = SOME s ==>
    s = new \/ (get_label op = SOME s /\ s <> old)
Proof
  Cases_on `op` >>
  rw[cfgTransformTheory.subst_label_op_def, venomStateTheory.get_label_def]
QED

(* Helper: successors after subst_label_inst *)
Theorem MEM_get_successors_subst_label_inst:
  !old new inst s.
    MEM s (get_successors (subst_label_inst old new inst)) ==>
    s = new \/ (MEM s (get_successors inst) /\ s <> old)
Proof
  rw[get_successors_def,
     cfgTransformTheory.subst_label_inst_def, LET_THM,
     cfgTransformProofsTheory.subst_label_inst_fields,
     MEM_MAP_THE_FILTER_IS_SOME] >>
  fs[listTheory.MEM_MAP] >> gvs[] >>
  drule get_label_subst_label_op >> strip_tac >> gvs[]
  >> disj2_tac >> simp[] >>
  qexists_tac `y'` >> simp[]
QED

(* Helper: bb_succs after conditional subst_label_inst *)
Theorem MEM_bb_succs_cond_subst_label:
  !old new bb succ. bb_well_formed bb /\
    MEM succ (bb_succs (bb with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst old new inst)
      bb.bb_instructions)) ==>
    succ = new \/ (MEM succ (bb_succs bb) /\ succ <> old)
Proof
  rw[bb_succs_def, venomWfTheory.bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  `(if ~is_terminator h.inst_opcode then h
    else subst_label_inst old new h)::
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) t =
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) (h::t)` by
    simp[] >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  fs[listTheory.LAST_MAP] >>
  `is_terminator (LAST (h::t)).inst_opcode` by fs[] >>
  rfs[] >>
  imp_res_tac MEM_get_successors_subst_label_inst >> fs[]
QED

(* Pointwise: get_label commutes with subst_label_op via OPTION_MAP *)
Triviality get_label_subst_label_op_option[local]:
  !old new op.
    get_label (subst_label_op old new op) =
    OPTION_MAP (\s. if s = old then new else s) (get_label op)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[cfgTransformTheory.subst_label_op_def, venomStateTheory.get_label_def] >>
  IF_CASES_TAC >> simp[venomStateTheory.get_label_def]
QED

(* List-level: FILTER/MAP THE commutes with subst_label_op via OPTION_MAP *)
Triviality filter_get_label_subst[local]:
  !old new ops.
    MAP THE (FILTER IS_SOME (MAP get_label (MAP (subst_label_op old new) ops))) =
    MAP (\s. if s = old then new else s)
        (MAP THE (FILTER IS_SOME (MAP get_label ops)))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >>
  rpt strip_tac >> simp[get_label_subst_label_op_option] >>
  Cases_on `get_label h` >> simp[]
QED

(* get_successors after subst_label_inst: maps old→new in successors *)
Theorem get_successors_subst_label_inst:
  !old new inst.
    get_successors (subst_label_inst old new inst) =
    MAP (\s. if s = old then new else s) (get_successors inst)
Proof
  rw[venomInstTheory.get_successors_def,
     cfgTransformTheory.subst_label_inst_def,
     cfgTransformProofsTheory.subst_label_inst_fields,
     filter_get_label_subst]
QED

(* nub (MAP f xs) = MAP f (nub xs) when f is injective on elements of xs *)
Triviality nub_MAP_INJ[local]:
  !f xs. (!x y. MEM x xs /\ MEM y xs /\ f x = f y ==> x = y) ==>
    nub (MAP f xs) = MAP f (nub xs)
Proof
  gen_tac >> Induct >> simp[listTheory.nub_def] >>
  rpt strip_tac >>
  `!x y. MEM x xs /\ MEM y xs /\ f x = f y ==> x = y` by metis_tac[] >>
  simp[listTheory.nub_def] >>
  (* Key: MEM (f h) (MAP f (nub xs)) iff MEM h (nub xs),
     using injectivity on h::xs (not just xs) *)
  `MEM (f h) (MAP f (nub xs)) <=> MEM h (nub xs)` by (
    simp[listTheory.MEM_MAP] >> eq_tac >> rpt strip_tac >> gvs[]
    >- (* fwd: ∃y ∈ nub xs. f y = f h. By MEM_nub, y ∈ xs ⊆ h::xs.
           h ∈ h::xs. Injectivity on h::xs gives y = h. *)
       (last_x_assum (qspecl_then [`y`, `h`] mp_tac) >>
        simp[] >> metis_tac[listTheory.MEM_nub])
    >> (qexists `h` >> simp[])) >>
  simp[] >> IF_CASES_TAC >> simp[]
  >- (* MEM (f h) (MAP f xs) → MEM h xs by injectivity on h::xs *)
     (`MEM h xs` by (
        gvs[listTheory.MEM_MAP] >>
        last_x_assum (qspecl_then [`y`, `h`] mp_tac) >>
        simp[] >> metis_tac[]) >>
      simp[])
  >> (* ¬MEM (f h) (MAP f xs) → ¬MEM h xs (contrapositive) *)
     (`~MEM h xs` by (
        strip_tac >> gvs[listTheory.MEM_MAP] >>
        qexists `h` >> simp[]) >>
      simp[])
QED

(* num_succs is preserved by cond_subst when new ∉ bb_succs bb.
   The substitution maps old→new in successors. Since new was not
   already a successor, the map is injective, so nub preserves length. *)
Theorem num_succs_cond_subst:
  !old new bb. bb_well_formed bb /\ ~MEM new (bb_succs bb) ==>
    num_succs (bb with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst old new inst)
      bb.bb_instructions) = num_succs bb
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.num_succs_def] >>
  fs[bb_succs_def, venomWfTheory.bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  `(if ~is_terminator h.inst_opcode then h
    else subst_label_inst old new h)::
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) t =
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst old new inst) (h::t)` by
    simp[] >>
  pop_assum SUBST1_TAC >>
  simp[listTheory.LAST_MAP] >>
  `is_terminator (LAST (h::t)).inst_opcode` by fs[] >>
  simp[get_successors_subst_label_inst] >>
  simp[listTheory.REVERSE_APPEND, rich_listTheory.MAP_REVERSE] >>
  `LENGTH (nub (REVERSE (MAP (\s. if s = old then new else s)
     (get_successors (LAST (h::t)))))) =
   LENGTH (MAP (\s. if s = old then new else s)
     (nub (REVERSE (get_successors (LAST (h::t))))))` by (
    AP_TERM_TAC >>
    `nub (REVERSE (MAP (\s. if s = old then new else s)
       (get_successors (LAST (h::t))))) =
     nub (MAP (\s. if s = old then new else s)
       (REVERSE (get_successors (LAST (h::t)))))` by
      simp[rich_listTheory.MAP_REVERSE] >>
    pop_assum SUBST1_TAC >>
    irule nub_MAP_INJ >>
    rpt strip_tac >> gvs[] >>
    (* Injectivity: f x = f y with f = \s. if s=old then new else s *)
    rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt strip_tac >> gvs[] >>
    (* Case: x=old, y≠old, f x = new = y. Then y=new ∈ REVERSE(get_succs) *)
    fs[listTheory.MEM_REVERSE, listTheory.nub_def]) >>
  simp[listTheory.LENGTH_MAP]
QED

(*
 * do_merge_jump: standalone component lemmas.
 * Each does its own case analysis to avoid multi-goal batch issues.
 *
 * Shared setup: rw[do_merge_jump_def] >> every_case_tac >> fs[] >> rw[]
 * yields one goal with func' = func with fn_blocks :=
 *   replace_block a.bb_label a'
 *     (replace_block target_lbl target'
 *       (remove_block b.bb_label func.fn_blocks))
 * where a' = a with bb_instructions := MAP (cond_subst) a.bb_instructions
 *       target' = target with bb_instructions := MAP (update_phi_bypass) target.bb_instructions
 *)

(* Common setup tactic for do_merge_jump component lemmas *)
(* Shared fact: a <> b and a.bb_label <> b.bb_label from can_bypass_jump *)
Theorem a_neq_b_bypass[local]:
  !func a b. can_bypass_jump func a b /\ wf_function func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks ==>
    a <> b /\ a.bb_label <> b.bb_label
Proof
  rw[can_bypass_jump_def] >> strip_tac >> gvs[] >> fs[num_succs_def] >>
  (* a.bb_label = b.bb_label case: derive a = b from unique lookup *)
  `lookup_block b.bb_label func.fn_blocks = SOME a` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `lookup_block b.bb_label func.fn_blocks = SOME b` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  gvs[]
QED

val do_merge_jump_setup =
  fs[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> fs[] >> rw[] >>
  rename [`lookup_block target_lbl func.fn_blocks = SOME target`] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  drule_all target_neq_b_bypass >> strip_tac >>
  drule_all a_neq_b_bypass >> strip_tac >>
  fs[can_bypass_jump_def];

(* 1. ALL_DISTINCT fn_labels *)
Theorem ALL_DISTINCT_do_merge_jump[local]:
  !func a b label_map func' lm'.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    ALL_DISTINCT (fn_labels func')
Proof
  rpt strip_tac >> do_merge_jump_setup >>
  simp[fn_labels_def,
       cfgTransformProofsTheory.fn_labels_replace_block,
       cfgTransformProofsTheory.fn_labels_remove_block] >>
  irule listTheory.FILTER_ALL_DISTINCT >>
  fs[wf_function_def, fn_labels_def]
QED

(* 2. fn_has_entry *)
Theorem fn_has_entry_do_merge_jump[local]:
  !func a b label_map func' lm'.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    fn_has_entry func'
Proof
  rpt strip_tac >> do_merge_jump_setup >>
  simp[venomWfTheory.fn_has_entry_def,
       cfgTransformTheory.replace_block_def,
       cfgTransformTheory.remove_block_def,
       listTheory.FILTER_NEQ_NIL, listTheory.MEM_MAP] >>
  qexists_tac `a` >> simp[listTheory.MEM_FILTER]
QED

(* General: bb_well_formed through two composed MAPs *)
Triviality bb_well_formed_MAP_MAP[local]:
  !f g bb. (!i. (f i).inst_opcode = i.inst_opcode) /\
           (!i. (g i).inst_opcode = i.inst_opcode) /\
           bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions := MAP f (MAP g bb.bb_instructions))
Proof
  rpt strip_tac >>
  once_rewrite_tac[listTheory.MAP_MAP_o] >>
  irule bb_well_formed_MAP_inst >>
  simp[combinTheory.o_DEF]
QED

(* bb_well_formed for the a-block in do_merge_jump (double MAP) *)
Theorem bb_well_formed_a_block_bypass:
  !a_lbl b_lbl tgt_lbl bb.
    bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions :=
      MAP (update_phi_bypass a_lbl b_lbl)
        (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                     else subst_label_inst b_lbl tgt_lbl inst)
          bb.bb_instructions))
Proof
  rpt strip_tac >> irule bb_well_formed_MAP_MAP >>
  simp[update_phi_bypass_opcode, cond_subst_label_opcode]
QED

(* 3. bb_well_formed *)
Theorem bb_well_formed_do_merge_jump[local]:
  !func a b label_map func' lm'.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    !bb. MEM bb func'.fn_blocks ==> bb_well_formed bb
Proof
  rpt gen_tac >> strip_tac >> do_merge_jump_setup >>
  rpt strip_tac >>
  drule MEM_replace_block >> strip_tac >> gvs[] >> (
    (* Case 1: bb = a' (MAP upb (MAP cs a.instrs)) *)
    (irule bb_well_formed_a_block_bypass >> fs[wf_function_def] >> res_tac)
    ORELSE
    (* Cases 2+3: in inner replace_block(remove_block) *)
    (drule MEM_replace_remove >> strip_tac >> gvs[] >> (
      (* Case 2: bb = target' *)
      (match_mp_tac bb_well_formed_update_phi_bypass >> fs[wf_function_def] >> res_tac)
      ORELSE
      (* Case 3: original block *)
      (fs[wf_function_def] >> res_tac))))
QED

(* Helper: succ in fn_labels after filter (shared across all 3 cases) *)
Theorem succ_in_fn_labels_filter[local]:
  !succ b_lbl func.
    succ <> b_lbl /\ MEM succ (fn_labels func) ==>
    MEM succ (FILTER (\l. l <> b_lbl) (MAP (\bb. bb.bb_label) func.fn_blocks))
Proof
  simp[fn_labels_def, listTheory.MEM_FILTER]
QED

(* 4. fn_succs_closed - helper: succ in fn_labels for each case *)

(* 4. fn_succs_closed *)

(* Core fact: every successor of any block in do_merge_jump result
   is either <> b.bb_label and in fn_labels func.
   Shared proof strategy: unique predecessor + fn_succs_closed of original *)

Theorem fn_succs_closed_do_merge_jump[local]:
  !func a b label_map func' lm'.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    fn_succs_closed func'
Proof
  rpt gen_tac >> strip_tac >> do_merge_jump_setup >>
  rw[venomWfTheory.fn_succs_closed_def] >> rpt strip_tac >>
  simp[fn_labels_def,
       cfgTransformProofsTheory.fn_labels_replace_block,
       cfgTransformProofsTheory.fn_labels_remove_block,
       listTheory.MEM_FILTER] >>
  (* Establish shared facts before case dispatch *)
  `bb_well_formed a` by (fs[wf_function_def] >> res_tac) >>
  `bb_well_formed target` by (fs[wf_function_def] >> res_tac) >>
  `!bb'. MEM bb' func.fn_blocks /\ MEM b.bb_label (bb_succs bb') ==> bb' = a` by
    (rpt strip_tac >>
     mp_tac (ISPECL [``func:ir_function``, ``(b:basic_block).bb_label``,
                     ``a:basic_block``] num_preds_1_unique) >>
     simp[]) >>
  (* Reduce to: succ <> b.bb_label /\ MEM succ (fn_labels func) *)
  `succ <> b.bb_label /\ MEM succ (fn_labels func)` suffices_by
    simp[fn_labels_def, listTheory.MEM_FILTER] >>
  conj_tac
  >- (
    (* PART 1: succ <> b.bb_label *)
    (* All cases: if succ = b.bb_label, the containing block is a
       predecessor of b, hence = a by unique predecessor, contradiction
       with label inequality *)
    strip_tac >> gvs[] >>
    drule MEM_replace_block >> strip_tac >> gvs[] >> (
      (* bb = a': MEM b.bb_label (bb_succs (a with ...)) *)
      (fs[bb_succs_a_block_bypass] >>
       drule_all MEM_bb_succs_cond_subst_label >> strip_tac >> gvs[] >>
       first_x_assum (qspec_then `a` mp_tac) >> simp[])
      ORELSE
      (* bb in inner: dispatch on target'/original *)
      (drule MEM_replace_remove >> strip_tac >> gvs[] >> (
        (* bb = target': succs same as target; target = a by uniq pred; contradiction *)
        (imp_res_tac bb_succs_update_phi_bypass >> gvs[] >>
         first_x_assum (qspec_then `target` mp_tac) >> simp[])
        ORELSE
        (* original block: bb = a by uniq pred; but bb.bb_label <> a.bb_label *)
        (first_x_assum (qspec_then `bb` mp_tac) >> simp[])))))
  (* PART 2: MEM succ (fn_labels func) *)
  >> `fn_succs_closed func` by fs[wf_function_def] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [venomWfTheory.fn_succs_closed_def]) >>
  drule MEM_replace_block >> strip_tac >> gvs[]
  >- (
    (* Goal 1: bb = a' (cond_subst block) *)
    fs[bb_succs_a_block_bypass] >>
    drule_all MEM_bb_succs_cond_subst_label >> strip_tac >> gvs[]
    >- (
      (* succ = target.bb_label: is succ of b *)
      first_x_assum (qspecl_then [`b`, `target.bb_label`] mp_tac) >>
      simp[listTheory.MEM])
    (* succ in bb_succs a, succ <> b.bb_label *)
    >> first_x_assum (qspecl_then [`a`, `succ`] mp_tac) >> simp[])
  (* Goal 2: bb in inner replace_block(remove_block) *)
  >> drule MEM_replace_remove >> strip_tac >> gvs[]
  >- (
    (* bb = target': succs = target's succs *)
    imp_res_tac bb_succs_update_phi_bypass >> gvs[] >>
    first_x_assum (qspecl_then [`target`, `succ`] mp_tac) >> simp[])
  (* original block *)
  >> first_x_assum (qspecl_then [`bb`, `succ`] mp_tac) >> simp[]
QED

(* 5. fn_inst_ids_distinct *)
val inst_ids_f = ``\bb:basic_block. MAP (\i:instruction. i.inst_id) bb.bb_instructions``;

val ALL_DISTINCT_inst_ids_replace =
  ISPECL [inst_ids_f] ALL_DISTINCT_FLAT_replace |> BETA_RULE;

val ALL_DISTINCT_inst_ids_replace_remove =
  ISPECL [inst_ids_f] ALL_DISTINCT_FLAT_replace_remove |> BETA_RULE;

val ALL_DISTINCT_inst_ids_member =
  ISPECL [inst_ids_f] ALL_DISTINCT_FLAT_member |> BETA_RULE;

(* Helper: inst_ids containment through replace_block(remove_block) *)
Theorem inst_ids_containment_do_merge_jump[local]:
  !func a b target_lbl target x.
    wf_function func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    a.bb_label <> b.bb_label /\ a <> b /\
    target_lbl <> b.bb_label /\
    target.bb_label = target_lbl /\
    MEM target func.fn_blocks /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    MEM x (MAP (\i. i.inst_id) a.bb_instructions) ==>
    ?blk. MEM blk (replace_block target_lbl
            (target with bb_instructions :=
              MAP (update_phi_bypass a.bb_label b.bb_label)
                  target.bb_instructions)
            (remove_block b.bb_label func.fn_blocks)) /\
          blk.bb_label = a.bb_label /\
          MEM x (MAP (\i. i.inst_id) blk.bb_instructions)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  Cases_on `a.bb_label = target_lbl`
  >- (
    `lookup_block target_lbl func.fn_blocks = SOME a` by
      (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
    `a = target` by fs[] >>
    qexists_tac `target with bb_instructions :=
      MAP (update_phi_bypass a.bb_label b.bb_label)
          target.bb_instructions` >>
    rpt conj_tac
    >- (match_mp_tac MEM_replace_block_new >>
        qexists_tac `target` >>
        conj_tac >- (match_mp_tac MEM_remove_block_intro >> fs[])
        >> fs[])
    >- fs[]
    >> fs[update_phi_bypass_inst_id, listTheory.MAP_MAP_o,
          combinTheory.o_DEF])
  >> (
    qexists_tac `a` >> rpt conj_tac
    >- (match_mp_tac MEM_replace_block_other >> simp[] >>
        match_mp_tac MEM_remove_block_intro >> simp[])
    >- simp[]
    >> simp[])
QED

(* Characterization of do_merge_jump SOME case *)
Theorem do_merge_jump_SOME_cases:
  !func a b lm func' lm'.
    do_merge_jump func a b lm = SOME (func', lm') ==>
    ?target_lbl target.
      bb_succs b = [target_lbl] /\
      lookup_block target_lbl func.fn_blocks = SOME target /\
      func'.fn_blocks = replace_block a.bb_label
        (a with bb_instructions :=
           MAP (update_phi_bypass a.bb_label b.bb_label)
             (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                          else subst_label_inst b.bb_label target_lbl inst)
               a.bb_instructions))
        (replace_block target_lbl
          (target with bb_instructions :=
             MAP (update_phi_bypass a.bb_label b.bb_label)
               target.bb_instructions)
          (remove_block b.bb_label func.fn_blocks)) /\
      lm' = (b.bb_label, target_lbl) :: lm
Proof
  rpt strip_tac >>
  qpat_x_assum `do_merge_jump _ _ _ _ = SOME _` mp_tac >>
  simp[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  simp[LET_THM] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* do_merge_jump SOME: only gives lm' structure, NOT func'.fn_blocks *)
Theorem do_merge_jump_lm_structure[local]:
  !func a b lm func' lm'.
    do_merge_jump func a b lm = SOME (func', lm') ==>
    ?target_lbl. lm' = (b.bb_label, target_lbl) :: lm
Proof
  rpt strip_tac >> qpat_x_assum `_ = SOME _` mp_tac >>
  simp[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> simp[LET_THM] >>
  strip_tac >> gvs[]
QED

(*  Helper: inst_ids of MAP update_phi_bypass = original inst_ids *)
Theorem inst_ids_MAP_upb[local]:
  !a_lbl b_lbl insts.
    MAP (\i. i.inst_id) (MAP (update_phi_bypass a_lbl b_lbl) insts) =
    MAP (\i. i.inst_id) insts
Proof
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, update_phi_bypass_inst_id]
QED

(* Helper: inst_ids of double-MAP (update_phi_bypass ∘ cond_subst) = original *)
Theorem inst_ids_MAP_upb_cs[local]:
  !a_lbl b_lbl tgt_lbl insts.
    MAP (\i. i.inst_id)
      (MAP (update_phi_bypass a_lbl b_lbl)
        (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                     else subst_label_inst b_lbl tgt_lbl inst) insts)) =
    MAP (\i. i.inst_id) insts
Proof
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
       update_phi_bypass_inst_id, cond_subst_label_inst_id]
QED

Theorem fn_inst_ids_distinct_do_merge_jump[local]:
  !func a b label_map func' lm'.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    fn_inst_ids_distinct func'
Proof
  rpt strip_tac >>
  drule_all do_merge_jump_SOME_cases >> strip_tac >> gvs[] >>
  simp[fn_inst_ids_distinct_def] >>
  (* Step 1: remove_block preserves ALL_DISTINCT *)
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (remove_block b.bb_label func.fn_blocks)))` by
    (irule ALL_DISTINCT_FLAT_remove >>
     fs[wf_function_def, fn_inst_ids_distinct_def]) >>
  (* Step 2: replace target — inst_ids unchanged *)
  `FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (replace_block target_lbl
       (target with bb_instructions :=
         MAP (update_phi_bypass a.bb_label b.bb_label)
             target.bb_instructions)
       (remove_block b.bb_label func.fn_blocks))) =
   FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (remove_block b.bb_label func.fn_blocks))` by
    (irule FLAT_MAP_replace_block_same >> rpt strip_tac >>
     fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
     `ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
       fs[wf_function_def, venomInstTheory.fn_labels_def] >>
     imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
     imp_res_tac venomExecProofsTheory.lookup_block_label >>
     `b' = target` by metis_tac[ALL_DISTINCT_MAP_eq] >>
     simp[inst_ids_MAP_upb]) >>
  (* Step 3: replace a — inst_ids unchanged *)
  `FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (replace_block a.bb_label
       (a with bb_instructions :=
         MAP (update_phi_bypass a.bb_label b.bb_label)
           (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                        else subst_label_inst b.bb_label target_lbl inst)
             a.bb_instructions))
       (replace_block target_lbl
         (target with bb_instructions :=
           MAP (update_phi_bypass a.bb_label b.bb_label)
               target.bb_instructions)
         (remove_block b.bb_label func.fn_blocks)))) =
   FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (replace_block target_lbl
       (target with bb_instructions :=
         MAP (update_phi_bypass a.bb_label b.bb_label)
             target.bb_instructions)
       (remove_block b.bb_label func.fn_blocks)))` by
    (irule FLAT_MAP_replace_block_same >> rpt strip_tac >>
     simp[inst_ids_MAP_upb_cs] >>
     (* b' is a block with label a.bb_label in replace(target, remove(b, blocks)) *)
     imp_res_tac MEM_replace_block >> gvs[]
     >- (* b' = target' — means a.bb_label = target_lbl, so a = target *)
       (`ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
          fs[wf_function_def, venomInstTheory.fn_labels_def] >>
        imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
        imp_res_tac venomExecProofsTheory.lookup_block_label >>
        `a = target` by metis_tac[ALL_DISTINCT_MAP_eq] >>
        gvs[inst_ids_MAP_upb, inst_ids_MAP_upb_cs])
     >> (* b' is original block from remove_block, b'.bb_label = a.bb_label *)
       (fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
        `ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
          fs[wf_function_def, venomInstTheory.fn_labels_def] >>
        `b' = a` by metis_tac[ALL_DISTINCT_MAP_eq] >>
        gvs[inst_ids_MAP_upb_cs])) >>
  gvs[]
QED

(* Combine all 5 properties *)
Theorem wf_function_do_merge_jump:
  !func a b label_map func' lm'.
    wf_function func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    wf_function func'
Proof
  rpt strip_tac >>
  match_mp_tac wf_function_intro >> rpt conj_tac
  >- (drule_all ALL_DISTINCT_do_merge_jump >> simp[])
  >- (drule_all fn_has_entry_do_merge_jump >> simp[])
  >- (rpt strip_tac >> drule_all bb_well_formed_do_merge_jump >> simp[])
  >- (drule_all fn_succs_closed_do_merge_jump >> simp[])
  >> drule_all fn_inst_ids_distinct_do_merge_jump >> simp[]
QED

(* wf_function through try_bypass *)
Theorem wf_function_try_bypass:
  !func label_map bb succs func' lm' flag.
    wf_function func /\
    MEM bb func.fn_blocks /\
    try_bypass func label_map bb succs = (func', lm', flag) ==>
    wf_function func'
Proof
  ntac 3 gen_tac >> Induct_on `succs` >>
  rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac wf_function_do_merge_jump >> fs[]
QED

(* ================================================================
   Section: wf_function through collapse_dfs
   Following fn_inst_wf_collapse_dfs pattern exactly.
   ================================================================ *)

Theorem wf_collapse_dfs:
  !func label_map visited wl func' lm' vis'.
    collapse_dfs func label_map visited wl = (func', lm', vis') ==>
    wf_function func ==> wf_function func'
Proof
  match_mp_tac (ISPEC ``wf_function``
    simplifyCfgHelpersTheory.collapse_dfs_preserves) >>
  rpt conj_tac
  >- (rpt strip_tac >> irule wf_function_merge_step >> metis_tac[])
  >> rpt strip_tac >> irule wf_function_try_bypass >>
     metis_tac[]
QED

(* ================================================================
   Section: wf_function through subst_block_labels_fn
   MAP-over-blocks transform. Labels unchanged, opcodes unchanged.
   ================================================================ *)

Theorem subst_block_labels_inst_opcode[local]:
  !lm inst. (subst_block_labels_inst lm inst).inst_opcode = inst.inst_opcode
Proof
  rw[cfgTransformTheory.subst_block_labels_inst_def,
     venomInstTheory.is_block_label_opcode_def,
     cfgTransformTheory.subst_label_map_inst_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
QED

Theorem subst_block_labels_inst_id[local]:
  !lm inst. (subst_block_labels_inst lm inst).inst_id = inst.inst_id
Proof
  rw[cfgTransformTheory.subst_block_labels_inst_def,
     venomInstTheory.is_block_label_opcode_def,
     cfgTransformTheory.subst_label_map_inst_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
QED

Theorem bb_well_formed_subst_block_labels[local]:
  !lm bb. bb_well_formed bb ==>
    bb_well_formed (subst_block_labels_block lm bb)
Proof
  rw[cfgTransformTheory.subst_block_labels_block_def] >>
  irule bb_well_formed_MAP_inst >>
  simp[subst_block_labels_inst_opcode]
QED

(* Successor characterization for subst_label_map_op *)
Theorem get_label_subst_label_map_op[local]:
  !lm op s.
    get_label (subst_label_map_op lm op) = SOME s ==>
    (?old. get_label op = SOME old /\ ALOOKUP lm old = SOME s) \/
    (get_label op = SOME s /\ ALOOKUP lm s = NONE)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[cfgTransformTheory.subst_label_map_op_def,
       venomStateTheory.get_label_def] >>
  BasicProvers.every_case_tac >>
  rw[venomStateTheory.get_label_def] >> fs[]
QED

(* get_successors through subst_label_map_inst *)
Theorem MEM_get_successors_subst_label_map_inst[local]:
  !lm inst s.
    is_terminator inst.inst_opcode /\
    MEM s (get_successors (subst_label_map_inst lm inst)) ==>
    (?old. MEM old (get_successors inst) /\ ALOOKUP lm old = SOME s) \/
    (MEM s (get_successors inst) /\ ALOOKUP lm s = NONE)
Proof
  rw[venomInstTheory.get_successors_def,
     cfgTransformTheory.subst_label_map_inst_def,
     MEM_MAP_THE_FILTER_IS_SOME] >>
  fs[listTheory.MEM_MAP] >> gvs[] >>
  drule get_label_subst_label_map_op >> strip_tac >> gvs[]
  >- (disj1_tac >> qexists_tac `old` >> simp[] >>
      qexists_tac `y'` >> simp[])
  >> (disj2_tac >> simp[] >>
      qexists_tac `y'` >> simp[])
QED

(* Successor characterization for subst_block_labels_inst *)
Theorem MEM_get_successors_subst_block_labels_inst[local]:
  !lm inst s.
    MEM s (get_successors (subst_block_labels_inst lm inst)) ==>
    (?old. MEM old (get_successors inst) /\ ALOOKUP lm old = SOME s) \/
    (MEM s (get_successors inst) /\ ALOOKUP lm s = NONE)
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (irule MEM_get_successors_subst_label_map_inst >> simp[] >>
      fs[cfgTransformTheory.subst_block_labels_inst_def,
         venomInstTheory.is_block_label_opcode_def])
  >> (fs[cfgTransformTheory.subst_block_labels_inst_def,
         venomInstTheory.is_block_label_opcode_def,
         venomInstTheory.get_successors_def] >>
      Cases_on `inst.inst_opcode = PHI` >>
      fs[cfgTransformTheory.subst_label_map_inst_def,
         venomInstTheory.get_successors_def])
QED

(* bb_succs characterization for subst_block_labels_block *)
Theorem MEM_bb_succs_subst_block_labels_block[local]:
  !lm bb s.
    bb_well_formed bb /\
    MEM s (bb_succs (subst_block_labels_block lm bb)) ==>
    (?old. MEM old (bb_succs bb) /\ ALOOKUP lm old = SOME s) \/
    (MEM s (bb_succs bb) /\ ALOOKUP lm s = NONE)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    fs[venomWfTheory.bb_well_formed_def] >>
  `(subst_block_labels_block lm bb).bb_instructions <> []` by
    fs[cfgTransformTheory.subst_block_labels_block_def] >>
  fs[MEM_bb_succs_iff] >>
  fs[cfgTransformTheory.subst_block_labels_block_def,
     listTheory.LAST_MAP] >>
  drule MEM_get_successors_subst_block_labels_inst >> simp[]
QED

Theorem fn_succs_closed_subst_block_labels_fn[local]:
  !label_map func.
    fn_succs_closed func /\
    (!bb. MEM bb func.fn_blocks ==> bb_well_formed bb) /\
    (!old new. ALOOKUP label_map old = SOME new /\
       MEM old (FLAT (MAP bb_succs func.fn_blocks)) ==>
       MEM new (fn_labels func)) ==>
    fn_succs_closed (subst_block_labels_fn label_map func)
Proof
  rpt strip_tac >>
  SIMP_TAC (srw_ss())
    [venomWfTheory.fn_succs_closed_def,
     cfgTransformProofsTheory.fn_labels_subst_block_labels_fn,
     cfgTransformTheory.subst_block_labels_fn_def] >>
  REWRITE_TAC [listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  `bb_well_formed y` by res_tac >>
  drule_all MEM_bb_succs_subst_block_labels_block >>
  strip_tac
  >- ((* case: ALOOKUP label_map old = SOME succ *)
      qpat_x_assum `!old new. ALOOKUP _ _ = SOME _ /\ _ ==> _` match_mp_tac >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[])
  >- ((* case: MEM succ (bb_succs y), original *)
      fs[venomWfTheory.fn_succs_closed_def] >>
      metis_tac[])
QED

Theorem wf_subst_block_labels_fn:
  !label_map func.
    wf_function func /\
    (!old new. ALOOKUP label_map old = SOME new /\
       MEM old (FLAT (MAP bb_succs func.fn_blocks)) ==>
       MEM new (fn_labels func)) ==>
    wf_function (subst_block_labels_fn label_map func)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels func)` by fs[wf_function_def] >>
  `fn_has_entry func` by fs[wf_function_def] >>
  `!bb. MEM bb func.fn_blocks ==> bb_well_formed bb` by fs[wf_function_def] >>
  `fn_succs_closed func` by fs[wf_function_def] >>
  `fn_inst_ids_distinct func` by fs[wf_function_def] >>
  match_mp_tac wf_function_intro >>
  rpt conj_tac
  >- simp[cfgTransformProofsTheory.fn_labels_subst_block_labels_fn]
  >- (fs[venomWfTheory.fn_has_entry_def,
         cfgTransformTheory.subst_block_labels_fn_def] >>
      Cases_on `func.fn_blocks` >> fs[])
  >- (rpt strip_tac >>
      fs[cfgTransformTheory.subst_block_labels_fn_def,
         listTheory.MEM_MAP] >> gvs[] >>
      match_mp_tac bb_well_formed_subst_block_labels >> res_tac)
  >- (match_mp_tac fn_succs_closed_subst_block_labels_fn >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- fs[venomWfTheory.fn_inst_ids_distinct_def,
        cfgTransformTheory.subst_block_labels_fn_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF,
        cfgTransformTheory.subst_block_labels_block_def,
        subst_block_labels_inst_id]
QED

(* ================================================================
   Section: label_map keys disjoint from block successors
   After collapse_dfs, every key in the label_map is a removed block
   label that no surviving block references as a successor.
   ================================================================ *)

(* label_map_disjoint: keys of lm are not in any block's successors *)
Definition label_map_disjoint_def:
  label_map_disjoint lm func <=>
    !old. MEM old (MAP FST lm) ==>
      ~MEM old (FLAT (MAP bb_succs func.fn_blocks))
End

Theorem label_map_disjoint_nil:
  !func. label_map_disjoint [] func
Proof
  simp[label_map_disjoint_def]
QED

(* The label_map precondition of wf_subst_block_labels_fn is vacuously
   satisfied when label_map_disjoint holds *)
Theorem label_map_disjoint_imp_precond:
  !lm func.
    label_map_disjoint lm func ==>
    (!old new. ALOOKUP lm old = SOME new /\
       MEM old (FLAT (MAP bb_succs func.fn_blocks)) ==>
       MEM new (fn_labels func))
Proof
  rw[label_map_disjoint_def] >> rpt strip_tac >>
  `MEM old (MAP FST lm)` by
    (simp[listTheory.MEM_MAP] >>
     imp_res_tac alistTheory.ALOOKUP_MEM >>
     metis_tac[pairTheory.FST]) >>
  res_tac
QED

(* ================================================================
   Helpers for label_map_disjoint_collapse_dfs:
   1. Successor set monotonicity through merge/bypass steps
   2. New label_map key not in successors after step
   ================================================================ *)

(* Helper: FLAT(MAP bb_succs) through replace_block + remove_block is subset
   of original, when replacement's bb_succs come from an existing block *)
Theorem flat_bb_succs_replace_remove_subset[local]:
  !lbl merged nlbl bbs x.
    MEM x (FLAT (MAP bb_succs
      (replace_block lbl merged (remove_block nlbl bbs)))) ==>
    MEM x (bb_succs merged) \/
    (?blk. MEM blk bbs /\ blk.bb_label <> nlbl /\
           blk.bb_label <> lbl /\ MEM x (bb_succs blk))
Proof
  rw[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  imp_res_tac MEM_replace_remove >> gvs[]
  >- metis_tac[]
  >> metis_tac[]
QED

(* Key helper: MAP bb_succs is preserved through the merge step's
   update_succ_phi_labels, reducing it to the simpler replace+remove *)
Theorem FLAT_bb_succs_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    FLAT (MAP bb_succs
      (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
          (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))) =
    FLAT (MAP bb_succs
      (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))
Proof
  rpt strip_tac >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  `bb_well_formed bb` by (fs[wf_function_def] >> res_tac) >>
  `bb_well_formed next_bb` by (fs[wf_function_def] >> res_tac) >>
  `no_phis next_bb` by gvs[can_merge_blocks_def] >>
  `ALL_DISTINCT (fn_labels func)` by fs[wf_function_def] >>
  `bb_well_formed (merge_blocks bb next_bb)` by
    (irule bb_well_formed_merge_blocks >> simp[]) >>
  `!b. MEM b (replace_block lbl (merge_blocks bb next_bb)
          (remove_block next_lbl func.fn_blocks)) ==> bb_well_formed b` by
    (rpt strip_tac >>
     qpat_x_assum `MEM _ (replace_block _ _ _)` mp_tac >>
     simp[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
     strip_tac >> gvs[] >>
     IF_CASES_TAC >> gvs[] >>
     fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER,
        wf_function_def] >>
     res_tac) >>
  imp_res_tac venomExecPropsTheory.lookup_block_label >>
  `ALL_DISTINCT (MAP (\b:basic_block. b.bb_label)
      (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by
    (irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
     simp[merge_blocks_def] >>
     irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
     fs[fn_labels_def]) >>
  simp[MAP_bb_succs_update_succ_phi_labels]
QED

(* Merge step: successors of new function are subset of old *)
Theorem merge_step_succs_subset[local]:
  !func lbl next_lbl bb next_bb x.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    MEM x (FLAT (MAP bb_succs
      (func with fn_blocks :=
        update_succ_phi_labels next_lbl lbl
          (replace_block lbl (merge_blocks bb next_bb)
            (remove_block next_lbl func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb))).fn_blocks)) ==>
    MEM x (FLAT (MAP bb_succs func.fn_blocks))
Proof
  rpt strip_tac >> fs[] >>
  imp_res_tac FLAT_bb_succs_merge_step >> fs[] >>
  drule flat_bb_succs_replace_remove_subset >> strip_tac
  >- (imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
      `bb_well_formed next_bb` by (fs[wf_function_def] >> res_tac) >>
      `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by
        simp[bb_succs_merge_blocks] >>
      fs[] >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
  >- (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
QED


(* do_merge_jump SOME: successors of new function are subset of old *)
Theorem do_merge_jump_succs_subset[local]:
  !func a b lm func' lm' x.
    wf_function func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b lm = SOME (func', lm') /\
    MEM x (FLAT (MAP bb_succs func'.fn_blocks)) ==>
    MEM x (FLAT (MAP bb_succs func.fn_blocks))
Proof
  rpt strip_tac >>
  drule_all do_merge_jump_SOME_cases >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  (* DO NOT use imp_res_tac lookup_block_label — keeps target_lbl unsubstituted *)
  `bb_well_formed a` by (fs[wf_function_def] >> res_tac) >>
  `bb_well_formed target` by (fs[wf_function_def] >> res_tac) >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  (* Assumptions: MEM x (bb_succs y), MEM y (replace_block a.bb_label ...) *)
  (* Goal: ∃l. (∃y. l = bb_succs y ∧ MEM y func.fn_blocks) ∧ MEM x l *)
  qpat_x_assum `MEM y (replace_block a.bb_label _ _)` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP MEM_replace_block) >> gvs[]
  >- (
    (* y = a-block: bb_succs of MAP upb (MAP cond_subst ...) *)
    qpat_x_assum `MEM x (bb_succs _)` mp_tac >>
    simp[bb_succs_a_block_bypass] >>
    strip_tac >>
    drule_all MEM_bb_succs_cond_subst_label >> strip_tac >> gvs[]
    >- (
      (* x = target_lbl: target_lbl ∈ bb_succs b = [target_lbl] *)
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[listTheory.MEM]
    )
    >- (
      (* x was already a succ of a (and x <> b.bb_label) *)
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
    )
  )
  >- (
    (* y from inner replace_block target_lbl ... *)
    qpat_x_assum `MEM y (replace_block target_lbl _ _)` mp_tac >>
    disch_then (strip_assume_tac o MATCH_MP MEM_replace_block) >> gvs[]
    >- (
      (* y = target with updated phi: bb_succs unchanged *)
      qpat_x_assum `MEM x (bb_succs _)` mp_tac >>
      simp[bb_succs_update_phi_bypass] >>
      strip_tac >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
    )
    >- (
      (* y from remove_block b.bb_label — an original block *)
      fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
    )
  )
QED

(* try_bypass T: successors of new function are subset of old *)
Theorem try_bypass_succs_subset[local]:
  !func lm bb succs func' lm' x.
    wf_function func /\
    MEM bb func.fn_blocks /\
    try_bypass func lm bb succs = (func', lm', T) /\
    MEM x (FLAT (MAP bb_succs func'.fn_blocks)) ==>
    MEM x (FLAT (MAP bb_succs func.fn_blocks))
Proof
  Induct_on `succs` >> rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  TRY (imp_res_tac do_merge_jump_succs_subset >> first_assum ACCEPT_TAC) >>
  res_tac
QED

(* Merge step: removed label (next_lbl) is not in any successor *)
(* General lemma: after replace_block + remove_block, a label that had
   a sole predecessor (which was replaced) doesnt appear in any successors *)
Theorem not_succ_after_replace_remove[local]:
  !bbs lbl new_bb next_lbl.
    ALL_DISTINCT (MAP (\b:basic_block. b.bb_label) bbs) /\
    ~MEM next_lbl (bb_succs new_bb) /\
    (!y. MEM y bbs /\ y.bb_label <> lbl /\ y.bb_label <> next_lbl ==>
         ~MEM next_lbl (bb_succs y)) ==>
    ~MEM next_lbl (FLAT (MAP bb_succs
      (replace_block lbl new_bb (remove_block next_lbl bbs))))
Proof
  rpt strip_tac >>
  fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  qpat_x_assum `MEM _ (replace_block _ _ _)` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP MEM_replace_block) >> gvs[] >>
  fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

Theorem merge_step_new_key_not_succ[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    bb_succs bb = [next_lbl] ==>
    ~MEM next_lbl (FLAT (MAP bb_succs
      (func with fn_blocks :=
        update_succ_phi_labels next_lbl lbl
          (replace_block lbl (merge_blocks bb next_bb)
            (remove_block next_lbl func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb))).fn_blocks))
Proof
  rpt gen_tac >> strip_tac >>
  simp[] >>
  `num_preds func next_lbl = 1` by fs[can_merge_blocks_def] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  imp_res_tac venomExecPropsTheory.lookup_block_label >>
  SUBGOAL_THEN ``bb_well_formed next_bb`` ASSUME_TAC >-
    (fs[wf_function_def] >> res_tac) >>
  drule_all FLAT_bb_succs_merge_step >> strip_tac >>
  ONCE_ASM_REWRITE_TAC[] >>
  CCONTR_TAC >>
  fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  qpat_x_assum `MEM _ (replace_block _ _ _)` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP MEM_replace_block) >> gvs[]
  >- (
    fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
    `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by
      simp[bb_succs_merge_blocks] >>
    fs[] >>
    mp_tac (Q.SPECL [`func`, `next_bb.bb_label`, `bb`] num_preds_1_unique) >>
    (impl_tac >- simp[listTheory.MEM]) >>
    disch_then (qspec_then `next_bb` mp_tac) >>
    simp[] >> strip_tac >>
    imp_res_tac venomExecPropsTheory.lookup_block_label >> gvs[]
  )
  >> (
    fs[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
    mp_tac (Q.SPECL [`func`, `next_bb.bb_label`, `bb`] num_preds_1_unique) >>
    (impl_tac >- simp[listTheory.MEM]) >>
    disch_then (qspec_then `y` mp_tac) >>
    simp[] >> strip_tac >>
    imp_res_tac venomExecPropsTheory.lookup_block_label >> gvs[]
  )
QED

(* do_merge_jump SOME: removed label (b.bb_label) is not in any successor *)
Theorem do_merge_jump_new_key_not_succ[local]:
  !func a b lm func' lm'.
    wf_function func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    ~MEM b.bb_label (FLAT (MAP bb_succs func'.fn_blocks))
Proof
  rpt strip_tac >>
  drule_all do_merge_jump_SOME_cases >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb_well_formed a` by (fs[wf_function_def] >> res_tac) >>
  `bb_well_formed target` by (fs[wf_function_def] >> res_tac) >>
  `target_lbl <> b.bb_label` by
    (irule target_neq_b_bypass >> metis_tac[]) >>
  `num_preds func b.bb_label = 1` by fs[can_bypass_jump_def] >>
  `MEM b.bb_label (bb_succs a)` by fs[can_bypass_jump_def] >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  (* MEM b.bb_label (bb_succs y), MEM y (replace_block a.bb_label ...) *)
  qpat_x_assum `MEM y (replace_block a.bb_label _ _)` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP MEM_replace_block) >> gvs[]
  >- suspend "case_a"
  >- suspend "case_inner"
QED

Resume do_merge_jump_new_key_not_succ[case_a]:
  fs[bb_succs_a_block_bypass] >>
  `b.bb_label <> target_lbl` by metis_tac[] >>
  metis_tac[not_MEM_bb_succs_cond_subst]
QED

Resume do_merge_jump_new_key_not_succ[case_inner]:
  (* a is the unique predecessor of b *)
  `!bb'. MEM bb' func.fn_blocks /\ MEM b.bb_label (bb_succs bb') ==> bb' = a` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`func`, `b.bb_label`, `a`] num_preds_1_unique) >>
     simp[]) >>
  (* Decompose: y = target' (original case killed by gvs) *)
  qpat_x_assum `MEM y (replace_block _ _ _)` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP MEM_replace_remove) >> gvs[] >>
  (* bb_succs target' = bb_succs target; target pred of b => target = a => contradiction *)
  imp_res_tac bb_succs_update_phi_bypass >> gvs[]
QED

Finalise do_merge_jump_new_key_not_succ

(* try_bypass T: new key not in successors *)
Theorem try_bypass_new_key_not_succ[local]:
  !func lm bb succs func' lm'.
    wf_function func /\
    MEM bb func.fn_blocks /\
    try_bypass func lm bb succs = (func', lm', T) ==>
    !old. MEM old (MAP FST lm') /\ ~MEM old (MAP FST lm) ==>
      ~MEM old (FLAT (MAP bb_succs func'.fn_blocks))
Proof
  Induct_on `succs` >> rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* Fallthrough cases: try_bypass on rest, use IH *)
  TRY (res_tac >> NO_TAC) >>
  (* Direct case: do_merge_jump returned SOME *)
  (* Use do_merge_jump_lm_structure (NOT do_merge_jump_SOME_cases)
     to get lm' = (x.bb_label, _) :: lm without expanding func'.fn_blocks *)
  imp_res_tac do_merge_jump_lm_structure >>
  gvs[listTheory.MAP, listTheory.MEM] >>
  (* Now old = x.bb_label and goal is ~MEM x.bb_label (FLAT (MAP bb_succs func'.fn_blocks)) *)
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  match_mp_tac do_merge_jump_new_key_not_succ >>
  metis_tac[]
QED

(* Main theorem: collapse_dfs preserves label_map_disjoint.
   This is the key lemma for wf_simplify_cfg_round. *)
(* Joint preservation: wf_function AND label_map_disjoint through collapse_dfs *)
Theorem wf_label_map_disjoint_collapse_dfs[local]:
  !func lm vis wl func' lm' vis'.
    collapse_dfs func lm vis wl = (func', lm', vis') ==>
    wf_function func /\ label_map_disjoint lm func ==>
    wf_function func' /\ label_map_disjoint lm' func'
Proof
  MATCH_MP_TAC (BETA_RULE (ISPECL [``\(lm:(string#string) list) (func:ir_function).
    wf_function func /\ label_map_disjoint lm func``]
    simplifyCfgHelpersTheory.collapse_dfs_preserves2)) >>
  rpt conj_tac
  (* merge_step preserves wf_function /\ label_map_disjoint *)
  >- (
    rpt strip_tac
    (* wf_function of merged func *)
    >- (match_mp_tac wf_function_merge_step >> metis_tac[])
    (* label_map_disjoint of extended label_map and merged func *)
    >> rw[label_map_disjoint_def]
    (* Case 1: old = next_bb.bb_label (the new key) *)
    >- (imp_res_tac venomExecPropsTheory.lookup_block_label >>
        gvs[simplifyCfgDefsTheory.can_merge_blocks_def] >>
        match_mp_tac (SIMP_RULE (srw_ss()) [] merge_step_new_key_not_succ) >>
        metis_tac[simplifyCfgDefsTheory.can_merge_blocks_def])
    (* Case 2: old in MAP FST lm (existing keys) *)
    >> CCONTR_TAC >> fs[] >>
    `MEM old (FLAT (MAP bb_succs func.fn_blocks))` suffices_by (
      strip_tac >> fs[label_map_disjoint_def] >> res_tac) >>
    irule (SIMP_RULE (srw_ss()) [] merge_step_succs_subset) >> metis_tac[]
  )
  (* try_bypass preserves wf_function /\ label_map_disjoint *)
  >> rpt strip_tac
  (* wf_function *)
  >- (irule wf_function_try_bypass >> metis_tac[])
  (* label_map_disjoint *)
  >> rw[label_map_disjoint_def] >>
  Cases_on `MEM old (MAP FST label_map)`
  >- (fs[label_map_disjoint_def] >> res_tac >>
      CCONTR_TAC >> fs[] >>
      `MEM old (FLAT (MAP bb_succs func.fn_blocks))` suffices_by metis_tac[] >>
      irule try_bypass_succs_subset >> metis_tac[])
  >> irule try_bypass_new_key_not_succ >> metis_tac[]
QED

(* Corollary: label_map_disjoint alone *)
Theorem label_map_disjoint_collapse_dfs:
  !func lm vis wl func' lm' vis'.
    collapse_dfs func lm vis wl = (func', lm', vis') ==>
    wf_function func /\ label_map_disjoint lm func ==>
    label_map_disjoint lm' func'
Proof
  metis_tac[wf_label_map_disjoint_collapse_dfs]
QED

(* ================================================================
   Section: wf_remove_unreachable
   ================================================================ *)

(* General list lemmas for FILTER preserving ALL_DISTINCT *)
Theorem ALL_DISTINCT_MAP_FILTER[local]:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct_on `l` >> rw[listTheory.FILTER, listTheory.MAP,
    listTheory.ALL_DISTINCT] >>
  fs[listTheory.MEM_MAP, listTheory.MEM_FILTER] >> res_tac
QED

Theorem ALL_DISTINCT_FLAT_MAP_FILTER[local]:
  !l P f. ALL_DISTINCT (FLAT (MAP f l)) ==>
    ALL_DISTINCT (FLAT (MAP f (FILTER P l)))
Proof
  Induct >> rw[listTheory.FILTER] >>
  fs[listTheory.ALL_DISTINCT_APPEND] >>
  rw[] >> fs[listTheory.MEM_FLAT, listTheory.MEM_MAP,
             listTheory.MEM_FILTER] >> metis_tac[]
QED

Theorem wf_remove_unreachable_labels[local]:
  !func.
    wf_function func ==>
    ALL_DISTINCT (fn_labels (remove_unreachable_blocks func))
Proof
  rw[remove_unreachable_blocks_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  fs[wf_function_def, fn_labels_def] >>
  irule ALL_DISTINCT_MAP_FILTER >> simp[]
QED

Theorem wf_remove_unreachable_entry[local]:
  !func.
    wf_function func ==>
    fn_has_entry (remove_unreachable_blocks func)
Proof
  rw[remove_unreachable_blocks_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  fs[wf_function_def, fn_has_entry_def] >>
  Cases_on `func.fn_blocks` >> fs[] >>
  (`fn_entry_label func = SOME h.bb_label` by
    fs[fn_entry_label_def, entry_block_def]) >>
  imp_res_tac cfgTransformPropsTheory.reachable_entry >>
  simp[listTheory.FILTER]
QED

Theorem wf_remove_unreachable_bbwf[local]:
  !func bb.
    wf_function func /\
    MEM bb (remove_unreachable_blocks func).fn_blocks ==>
    bb_well_formed bb
Proof
  rw[remove_unreachable_blocks_def] >>
  BasicProvers.every_case_tac >> fs[wf_function_def] >>
  fs[listTheory.MEM_FILTER]
QED

Theorem wf_remove_unreachable_succs[local]:
  !func.
    wf_function func ==>
    fn_succs_closed (remove_unreachable_blocks func)
Proof
  rw[remove_unreachable_blocks_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  fs[wf_function_def] >>
  rw[fn_succs_closed_def] >>
  fs[listTheory.MEM_FILTER] >>
  (`reachable func succ` by (
    irule cfgTransformPropsTheory.reachable_step >>
    qexists_tac `bb.bb_label` >> simp[fn_succ_def] >>
    qexists_tac `bb` >> simp[] >>
    irule venomExecPropsTheory.MEM_lookup_block >>
    fs[fn_labels_def])) >>
  (`MEM succ (fn_labels func)` by (fs[fn_succs_closed_def] >> res_tac)) >>
  simp[fn_labels_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  fs[fn_labels_def, listTheory.MEM_MAP] >>
  qexists_tac `bb'` >> fs[]
QED

Theorem wf_remove_unreachable_instids[local]:
  !func.
    wf_function func ==>
    fn_inst_ids_distinct (remove_unreachable_blocks func)
Proof
  rw[remove_unreachable_blocks_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  fs[wf_function_def, fn_inst_ids_distinct_def] >>
  irule ALL_DISTINCT_FLAT_MAP_FILTER >> simp[]
QED

Theorem wf_remove_unreachable:
  !func.
    wf_function func ==>
    wf_function (remove_unreachable_blocks func)
Proof
  rpt strip_tac >>
  simp[wf_function_def, wf_remove_unreachable_labels,
       wf_remove_unreachable_entry, wf_remove_unreachable_succs,
       wf_remove_unreachable_instids] >>
  rpt strip_tac >> irule wf_remove_unreachable_bbwf >>
  qexists_tac `func` >> fs[wf_function_def]
QED

(* ================================================================
   Section: wf_simplify_cfg_round (exported)
   Chain: remove_unreachable -> fix_all_phis -> collapse_dfs
         -> subst_block_labels -> remove_unreachable -> fix_all_phis
   ================================================================ *)

Theorem wf_simplify_cfg_round:
  !func.
    wf_function func /\
    (simplify_cfg_round func).fn_blocks <> [] ==>
    wf_function (simplify_cfg_round func)
Proof
  rw[simplifyCfgDefsTheory.simplify_cfg_round_def] >>
  BasicProvers.every_case_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  (* Step 1: remove_unreachable preserves wf *)
  `wf_function (remove_unreachable_blocks func)` by
    (irule wf_remove_unreachable >> simp[]) >>
  (* Step 2: fix_all_phis preserves wf *)
  `wf_function (fix_all_phis (remove_unreachable_blocks func))` by
    (irule simplifyCfgHelpersTheory.wf_fix_all_phis >> simp[]) >>
  (* Step 3: collapse_dfs preserves wf *)
  `wf_function func2` by
    (drule_all wf_collapse_dfs >> simp[]) >>
  (* Step 4: label_map_disjoint for subst_block_labels *)
  `label_map_disjoint label_map func2` by
    (drule label_map_disjoint_collapse_dfs >>
     disch_then irule >> simp[label_map_disjoint_nil]) >>
  (* Step 5: subst_block_labels preserves wf (if label_map nonempty) *)
  IF_CASES_TAC >> fs[]
  >- (
    (* label_map = []: func3 = func2, skip to remove_unreachable *)
    `wf_function (remove_unreachable_blocks func2)` by
      (irule wf_remove_unreachable >> simp[]) >>
    irule simplifyCfgHelpersTheory.wf_fix_all_phis >> simp[]
  ) >>
  (* label_map <> []: subst_block_labels_fn *)
  `wf_function (subst_block_labels_fn label_map func2)` by (
    match_mp_tac wf_subst_block_labels_fn >> conj_tac
    >- first_assum ACCEPT_TAC
    >> match_mp_tac label_map_disjoint_imp_precond >> first_assum ACCEPT_TAC) >>
  `wf_function (remove_unreachable_blocks (subst_block_labels_fn label_map func2))` by
    (irule wf_remove_unreachable >> simp[]) >>
  irule simplifyCfgHelpersTheory.wf_fix_all_phis >> simp[]
QED

val _ = export_theory();
