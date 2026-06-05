(* Phase 3 WF preservation: ao_transform_block
 *
 * TOP-LEVEL:
 *   ao_phase3_preserves_wf — wf_function preserved through phase 3
 *
 * Helper:
 *   ao_transform_block_bb_wf, ao_transform_block_bb_succs
 *   (ao_transform_inst structural properties now live in aoWf)
 *)

Theory aoPhase3Wf
Ancestors
  algebraicOptDefs aoPeepholeSim aoPhase1Wf aoPhase3Ids aoWf
  venomState venomWf venomInst passSimulationProps passSimulationDefs
  passSharedDefs
Libs
  pairLib BasicProvers

(* ao_resolve_iszero_inst / ao_transform_inst structural properties are
   shared from aoWf; this theory keeps only phase-3-specific lemmas. *)

Triviality resolve_op_label[local]:
  !targets opc lbl.
    ao_resolve_iszero_op targets opc (Label lbl) = Label lbl
Proof
  simp[ao_resolve_iszero_op_def]
QED

Triviality resolve_op_get_label[local]:
  !targets opc op.
    IS_SOME (get_label op) ==>
    IS_SOME (get_label (ao_resolve_iszero_op targets opc op))
Proof
  Cases_on `op` >>
  simp[venomStateTheory.get_label_def, ao_resolve_iszero_op_def]
QED

Triviality ao_resolve_iszero_inst_wf[local]:
  !targets inst.
    inst_wf inst /\ inst.inst_opcode <> PHI ==>
    inst_wf (ao_resolve_iszero_inst targets inst)
Proof
  rpt strip_tac >>
  fs[ao_resolve_iszero_inst_def, inst_wf_def] >>
  Cases_on `inst.inst_opcode` >> gvs[listTheory.LENGTH_MAP] >>
  simp[resolve_op_label, ao_resolve_iszero_op_def] >>
  fs[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> res_tac >>
  irule resolve_op_get_label >> simp[]
QED

Triviality ao_pre_flip_inst_wf[local]:
  !inst. inst_wf inst ==> inst_wf (ao_pre_flip_inst inst)
Proof
  rpt strip_tac >>
  simp[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  gvs[is_comparator_def, flip_comparison_opcode_def, inst_wf_def]
QED

(* ===== Iszero chain invariant: internal positions are Vars ===== *)

(* A single forward step keeps the "positions >= 1 are Var" invariant. *)
Triviality chain_step_pos_var[local]:
  !acc inst v ch.
    (!v' ch'. ALOOKUP acc v' = SOME ch' ==>
       !j. 0 < j /\ j < LENGTH ch' ==> ?y. EL j ch' = Var y) ==>
    ALOOKUP (ao_compute_iszero_step acc inst) v = SOME ch ==>
    !j. 0 < j /\ j < LENGTH ch ==> ?y. EL j ch = Var y
Proof
  rpt strip_tac >>
  qpat_x_assum `ALOOKUP _ _ = SOME _` mp_tac >>
  simp[ao_compute_iszero_step_def, LET_THM] >>
  every_case_tac >> simp[] >> every_case_tac >> simp[] >>
  strip_tac >> gvs[] >>
  TRY (metis_tac[]) >>
  gvs[listTheory.LENGTH_SNOC] >>
  TRY (`j = 1` by DECIDE_TAC >> gvs[listTheory.EL_LENGTH_SNOC] >> NO_TAC) >>
  qmatch_asmsub_rename_tac `ALOOKUP acc acc_var = SOME acc_chain` >>
  Cases_on `j = LENGTH acc_chain`
  >- gvs[listTheory.EL_LENGTH_SNOC]
  >- (`j < LENGTH acc_chain` by DECIDE_TAC >>
      gvs[listTheory.EL_SNOC] >> metis_tac[])
QED

Triviality chain_pos_var_foldl[local]:
  !insts acc v chain k.
    (!v' ch. ALOOKUP acc v' = SOME ch ==>
       !j. 0 < j /\ j < LENGTH ch ==> ?y. EL j ch = Var y) /\
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    ?y. EL k chain = Var y
Proof
  Induct
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  fs[listTheory.FOLDL] >>
  first_x_assum (qspecl_then [`ao_compute_iszero_step acc h`, `v`, `chain`, `k`] mp_tac) >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >> metis_tac[chain_step_pos_var]) >>
  simp[]
QED

Theorem chain_pos_var:
  !fn0 targets v chain k.
    targets = ao_compute_fn_iszero_targets fn0 /\
    ALOOKUP targets v = SOME chain /\ 0 < k /\ k < LENGTH chain ==>
    ?y. EL k chain = Var y
Proof
  rpt strip_tac >>
  gvs[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  qspecl_then [`fn_insts fn0`, `[]`, `v`, `chain`, `k`] mp_tac chain_pos_var_foldl >>
  simp[]
QED

(* ===== ao_resolve_iszero_inst preserves inst_wf for PHI ===== *)

(* Resolution maps non-Var operands to themselves and Vars to Vars,
   hence preserves phi_well_formed. *)
(* Helper: phi_well_formed is preserved through a 2-element prefix when f maps
   Var->Var and fixes non-Var operands. *)
Triviality phi_wf_cons2[local]:
  !f x y rest.
    (!v. ?w. f (Var v) = Var w) /\
    (!op. (!v. op <> Var v) ==> f op = op) /\
    phi_well_formed (x::y::rest) /\ phi_well_formed (MAP f rest) ==>
    phi_well_formed (f x :: f y :: MAP f rest)
Proof
  rpt strip_tac >>
  `!n. f (Lit n) = Lit n` by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `!l. f (Label l) = Label l` by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  Cases_on `x` >> Cases_on `y` >>
  gvs[phi_well_formed_def] >>
  rename1 `f (Var v)` >>
  `?w. f (Var v) = Var w` by metis_tac[] >>
  gvs[phi_well_formed_def]
QED

Triviality phi_wf_map[local]:
  !f ops.
    (!v. ?w. f (Var v) = Var w) /\
    (!op. (!v. op <> Var v) ==> f op = op) /\
    phi_well_formed ops ==>
    phi_well_formed (MAP f ops)
Proof
  gen_tac >> ho_match_mp_tac phi_well_formed_ind >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (fs[phi_well_formed_def] >> NO_TAC) >>
  REWRITE_TAC[listTheory.MAP] >> irule phi_wf_cons2 >> simp[] >>
  first_x_assum irule >> fs[phi_well_formed_def]
QED

Triviality ao_resolve_iszero_op_phi_var[local]:
  !fn0 targets v.
    targets = ao_compute_fn_iszero_targets fn0 ==>
    ?w. ao_resolve_iszero_op targets PHI (Var v) = Var w
Proof
  rpt strip_tac >>
  simp[ao_resolve_iszero_op_def, LET_THM] >>
  CASE_TAC >> simp[] >>
  rename1 `ALOOKUP _ _ = SOME chain` >>
  IF_CASES_TAC >> simp[] >>
  qmatch_goalsub_abbrev_tac `EL keep chain` >>
  `keep < LENGTH chain` by fs[Abbr `keep`] >>
  `0 < keep` by
    (`(LENGTH chain - 1) MOD 2 < 2` by simp[] >>
     simp[Abbr `keep`] >> DECIDE_TAC) >>
  metis_tac[chain_pos_var]
QED

Triviality ao_resolve_iszero_op_phi_nonvar[local]:
  !targets op. (!v. op <> Var v) ==>
    ao_resolve_iszero_op targets PHI op = op
Proof
  rpt strip_tac >> Cases_on `op` >> fs[ao_resolve_iszero_op_def]
QED

Triviality ao_resolve_iszero_inst_wf_phi[local]:
  !fn0 inst.
    inst_wf inst /\ inst.inst_opcode = PHI ==>
    inst_wf (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn0) inst)
Proof
  rpt strip_tac >>
  fs[ao_resolve_iszero_inst_def, inst_wf_def] >>
  simp[listTheory.LENGTH_MAP] >>
  irule phi_wf_map >> simp[] >>
  metis_tac[ao_resolve_iszero_op_phi_var, ao_resolve_iszero_op_phi_nonvar]
QED

(* The resolve post-pass rewrites PHIs through ao_resolve_iszero_inst (which
   preserves inst_wf for PHIs, above) and leaves non-PHIs untouched, hence
   preserves inst_wf across the whole block. *)
Triviality ao_resolve_phis_block_inst_wf[local]:
  !fn0 bb.
    EVERY inst_wf bb.bb_instructions ==>
    EVERY inst_wf
      (ao_resolve_phis_block (ao_compute_fn_iszero_targets fn0) bb).bb_instructions
Proof
  rpt strip_tac >>
  simp[ao_resolve_phis_block_def, listTheory.EVERY_MAP] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[] >>
  irule ao_resolve_iszero_inst_wf_phi >> simp[]
QED


(* ===== FLAT MAPi helpers ===== *)

Triviality flat_mapi_ne[local]:
  !g l. l <> [] /\ (!i. i < LENGTH l ==> g i (EL i l) <> []) ==>
    FLAT (MAPi g l) <> []
Proof
  rpt gen_tac >> Cases_on `l` >> simp[indexedListsTheory.MAPi_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Triviality last_flat_mapi[local]:
  !l g.
    l <> [] /\ (!i. i < LENGTH l ==> g i (EL i l) <> []) /\
    (?v. g (PRE (LENGTH l)) (LAST l) = [v]) ==>
    LAST (FLAT (MAPi g l)) = LAST (g (PRE (LENGTH l)) (LAST l))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[indexedListsTheory.MAPi_def] >> strip_tac >>
  Cases_on `l`
  >- (gvs[indexedListsTheory.MAPi_def] >>
      `g 0 h <> []` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      Cases_on `g 0 h` >> fs[])
  >- (rename1 `h :: h' :: t` >>
      first_assum (qspec_then `1` assume_tac) >>
      gvs[rich_listTheory.LAST_APPEND_NOT_NIL] >>
      first_x_assum (qspec_then `g o SUC` mp_tac) >>
      simp[combinTheory.o_DEF] >>
      strip_tac >>
      first_assum (qspec_then `1` assume_tac) >>
      fs[] >>
      ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC] >>
      simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
      first_x_assum irule >>
      rpt strip_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
QED

Triviality front_flat_mapi_singleton[local]:
  !l g.
    l <> [] /\ (!i. i < LENGTH l ==> g i (EL i l) <> []) /\
    (?v. g (PRE (LENGTH l)) (LAST l) = [v]) ==>
    FRONT (FLAT (MAPi g l)) = FLAT (MAPi g (FRONT l))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[indexedListsTheory.MAPi_def] >> strip_tac >>
  Cases_on `l`
  >- (gvs[indexedListsTheory.MAPi_def] >>
      `g 0 h <> []` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      Cases_on `g 0 h` >> fs[])
  >- (rename1 `h :: h' :: t` >>
      first_assum (qspec_then `1` assume_tac) >> fs[] >>
      first_x_assum (qspec_then `g o SUC` mp_tac) >>
      simp[combinTheory.o_DEF] >>
      strip_tac >>
      `!i. i < SUC (LENGTH t) ==> g (SUC i) (EL i (h'::t)) <> []` by
        (rpt strip_tac >>
         first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
      res_tac >>
      qpat_assum `FRONT _ = FLAT _` (SUBST1_TAC o SYM) >>
      ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC] >>
      irule rich_listTheory.FRONT_APPEND_NOT_NIL >>
      simp[])
QED

(* ===== PHI prefix for FLAT MAPi ===== *)

Triviality phi_singleton_at_head[local]:
  !g h t.
    (!i. i < LENGTH (h::t) /\ (EL i (h::t)).inst_opcode = PHI ==>
         ?v. g i (EL i (h::t)) = [v] /\ v.inst_opcode = PHI) ==>
    h.inst_opcode = PHI ==>
    ?v. g 0 h = [v] /\ v.inst_opcode = PHI
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Triviality flat_mapi_nonphi_contra[local]:
  !h t g i j.
    (!i j. i < j /\ j < LENGTH (h::t) /\ (EL j (h::t)).inst_opcode = PHI ==>
           (EL i (h::t)).inst_opcode = PHI) /\
    (!i r. i < LENGTH (h::t) /\ (EL i (h::t)).inst_opcode <> PHI /\
           MEM r (g i (EL i (h::t))) ==> r.inst_opcode <> PHI) /\
    h.inst_opcode <> PHI /\
    i < j /\ j < LENGTH (g 0 h ++ FLAT (MAPi (g o SUC) t)) /\
    (EL j (g 0 h ++ FLAT (MAPi (g o SUC) t))).inst_opcode = PHI ==>
    (EL i (g 0 h ++ FLAT (MAPi (g o SUC) t))).inst_opcode = PHI
Proof
  rpt strip_tac >>
  `!k. k < LENGTH (h::t) ==> (EL k (h::t)).inst_opcode <> PHI` by (
    rpt strip_tac >>
    spose_not_then strip_assume_tac >>
    (Cases_on `k` >- gvs[]) >>
    rename1 `SUC m < _` >>
    first_x_assum (qspecl_then [`0`, `SUC m`] mp_tac) >> simp[]) >>
  `EVERY (\r. r.inst_opcode <> PHI) (g 0 h ++ FLAT (MAPi (g o SUC) t))` by (
    simp[listTheory.EVERY_APPEND] >>
    (conj_tac >- (
      simp[listTheory.EVERY_MEM] >>
      rpt strip_tac >> rename1 `MEM r _` >>
      first_x_assum (qspecl_then [`0`, `r`] mp_tac) >> simp[])) >>
    simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
         indexedListsTheory.MEM_MAPi, combinTheory.o_DEF] >>
    rpt strip_tac >> gvs[] >>
    rename1 `MEM r _` >> rename1 `k < LENGTH t` >>
    first_x_assum (qspecl_then [`SUC k`, `r`] mp_tac) >> simp[]) >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  PURE_REWRITE_TAC [listTheory.EVERY_EL] >>
  disch_then (qspec_then `j` mp_tac) >> simp[]
QED

Triviality flat_mapi_phi_prefix[local]:
  !l g.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) /\
    (!i. i < LENGTH l /\ (EL i l).inst_opcode = PHI ==>
         ?v. g i (EL i l) = [v] /\ v.inst_opcode = PHI) /\
    (!i r. i < LENGTH l /\ (EL i l).inst_opcode <> PHI /\
           MEM r (g i (EL i l)) ==> r.inst_opcode <> PHI) /\
    (!i. i < LENGTH l ==> g i (EL i l) <> [])
    ==>
    (!i j. i < j /\ j < LENGTH (FLAT (MAPi g l)) /\
           (EL j (FLAT (MAPi g l))).inst_opcode = PHI ==>
           (EL i (FLAT (MAPi g l))).inst_opcode = PHI)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> rename1 `h :: t` >>
  simp[indexedListsTheory.MAPi_def] >>
  `g 0 h <> []` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    drule_all phi_singleton_at_head >> strip_tac >>
    gvs[] >> rpt strip_tac >>
    (Cases_on `i` >- simp[]) >>
    (Cases_on `j` >- gvs[]) >> gvs[] >>
    (`!i j. i < j /\ j < LENGTH (FLAT (MAPi (g o SUC) t)) /\
            (EL j (FLAT (MAPi (g o SUC) t))).inst_opcode = PHI ==>
            (EL i (FLAT (MAPi (g o SUC) t))).inst_opcode = PHI` by (
      first_x_assum MATCH_MP_TAC >>
      simp[combinTheory.o_DEF] >>
      (rpt conj_tac >> rpt gen_tac >> rpt strip_tac) >| [
        first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[],
        qpat_x_assum `!i. _ /\ _ = PHI ==> ?v. _`
          (qspec_then `SUC i` mp_tac) >> simp[],
        qpat_x_assum `!i r. _`
          (qspecl_then [`SUC i`, `r`] mp_tac) >> simp[],
        qpat_x_assum `!i. _ ==> _ <> _`
          (qspec_then `SUC i` mp_tac) >> simp[]
      ])) >>
    first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[])
  >- (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`h`, `t`, `g`, `i`, `j`] flat_mapi_nonphi_contra) >>
    impl_tac >- (
      rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> simp[]) >>
    simp[])
QED

Triviality ao_transform_inst_phi_prefix[local]:
  !insts targets mid dfg ra lbl.
    (!i j. i < j /\ j < LENGTH insts /\
       (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    EVERY inst_wf insts /\
    (!i. i < LENGTH insts ==>
      ao_transform_inst mid dfg ra lbl i targets (EL i insts) <> []) ==>
    !i j.
      i < j /\
      j < LENGTH (FLAT (MAPi
        (\idx inst. ao_transform_inst mid dfg ra lbl idx targets inst)
        insts)) /\
      (EL j (FLAT (MAPi
        (\idx inst. ao_transform_inst mid dfg ra lbl idx targets inst)
        insts))).inst_opcode = PHI ==>
      (EL i (FLAT (MAPi
        (\idx inst. ao_transform_inst mid dfg ra lbl idx targets inst)
        insts))).inst_opcode = PHI
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `g = \idx inst.
    ao_transform_inst mid dfg ra lbl idx targets inst` >>
  MATCH_MP_TAC flat_mapi_phi_prefix >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >>
      qexists_tac `EL i insts` >>
      simp[Abbr `g`, ao_transform_inst_phi])
  >- (rpt strip_tac >>
      `inst_wf (EL i insts)` by fs[listTheory.EVERY_EL] >>
      `EVERY (\r'. r'.inst_opcode <> PHI)
             (g i (EL i insts))` by
        (simp[Abbr `g`] >>
         irule ao_transform_inst_non_phi >> simp[]) >>
      fs[listTheory.EVERY_MEM] >> res_tac >> fs[])
  >- fs[Abbr `g`]
QED

(* ===== bb_well_formed for ao_transform_block ===== *)

(* ao_resolve_phis_block only rewrites PHI operands, preserving every
   instruction's opcode and the block length, so bb_well_formed (which depends
   only on opcodes + length) is invariant under it.  This lets the WF proof
   strip the resolve post-pass and reduce to the pre-resolution block. *)
Triviality ao_resolve_phis_block_bb_well_formed[local]:
  !targets bb.
    bb_well_formed bb ==>
    bb_well_formed (ao_resolve_phis_block targets bb)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `h = \inst. if inst.inst_opcode = PHI
                          then ao_resolve_iszero_inst targets inst else inst` >>
  `(ao_resolve_phis_block targets bb).bb_instructions = MAP h bb.bb_instructions`
    by simp[ao_resolve_phis_block_def, Abbr `h`] >>
  `!x. (h x).inst_opcode = x.inst_opcode` by
    rw[Abbr `h`, ao_resolve_iszero_inst_opcode] >>
  `!n. n < LENGTH bb.bb_instructions ==>
    (MAP h bb.bb_instructions)❲n❳.inst_opcode = bb.bb_instructions❲n❳.inst_opcode`
    by (rpt strip_tac >>
        `(MAP h bb.bb_instructions)❲n❳ = h (bb.bb_instructions❲n❳)`
          by simp[listTheory.EL_MAP] >>
        fs[]) >>
  fs[bb_well_formed_def, listTheory.LAST_MAP] >>
  rw[] >> res_tac >> fs[]
QED

Triviality ao_transform_block_bb_wf[local]:
  !mid dfg ra targets bb.
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions ==>
    bb_well_formed (ao_transform_block mid dfg ra targets bb)
Proof
  rpt strip_tac >>
  simp[ao_transform_block_def] >>
  irule ao_resolve_phis_block_bb_well_formed >>
  simp[bb_well_formed_def] >>
  fs[bb_well_formed_def] >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  qabbrev_tac `g = \idx inst.
    ao_transform_inst mid dfg ra bb.bb_label idx targets inst` >>
  `!i. i < LENGTH insts ==> g i (EL i insts) <> []` by
    simp[Abbr `g`, ao_transform_inst_ne] >>
  `EVERY inst_wf insts` by simp[Abbr `insts`] >>
  `inst_wf (LAST insts)` by
    (fs[listTheory.EVERY_MEM] >>
     first_x_assum irule >>
     irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  rpt conj_tac
  >- (irule flat_mapi_ne >> simp[])
  >- (`g (PRE (LENGTH insts)) (LAST insts) =
       [ao_resolve_iszero_inst targets (LAST insts)]` by (
        simp[Abbr `g`] >> irule ao_transform_inst_term >> simp[]) >>
      `LAST (FLAT (MAPi g insts)) =
       LAST (g (PRE (LENGTH insts)) (LAST insts))` by (
        irule last_flat_mapi >> simp[] >>
        qexists_tac `ao_resolve_iszero_inst targets (LAST insts)` >>
        simp[]) >>
      simp[ao_resolve_iszero_inst_opcode])
  >- (rpt strip_tac >>
      spose_not_then strip_assume_tac >>
      `FLAT (MAPi g insts) <> []` by (irule flat_mapi_ne >> simp[]) >>
      `i < PRE (LENGTH (FLAT (MAPi g insts)))` by simp[] >>
      `EVERY (\r. ~is_terminator r.inst_opcode) (FRONT insts)` by (
        simp[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT,
             rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
        rpt strip_tac >> CCONTR_TAC >> fs[] >>
        `n < LENGTH insts` by (Cases_on `insts` >> fs[]) >>
        res_tac >> fs[]) >>
      `FRONT (FLAT (MAPi g insts)) = FLAT (MAPi g (FRONT insts))` by (
        irule front_flat_mapi_singleton >> simp[] >>
        qexists_tac `ao_resolve_iszero_inst targets (LAST insts)` >>
        simp[Abbr `g`] >> irule ao_transform_inst_term >> simp[]) >>
      `EVERY (\r. ~is_terminator r.inst_opcode)
             (FLAT (MAPi g (FRONT insts)))` by (
        simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
             indexedListsTheory.MEM_MAPi] >>
        rpt gen_tac >> strip_tac >> gvs[] >>
        rename1 `MEM x (g n (EL n (FRONT insts)))` >>
        `n < LENGTH insts` by
          (Cases_on `insts` >> fs[rich_listTheory.LENGTH_FRONT]) >>
        `EL n (FRONT insts) = EL n insts` by
          (irule rich_listTheory.EL_FRONT >>
           fs[listTheory.NULL_EQ, rich_listTheory.LENGTH_FRONT]) >>
        `~is_terminator (EL n insts).inst_opcode` by (
          fs[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT] >>
          spose_not_then strip_assume_tac >> res_tac >>
          Cases_on `insts` >> fs[]) >>
        `inst_wf (EL n insts)` by fs[listTheory.EVERY_EL] >>
        `EVERY (\r'. ~is_terminator r'.inst_opcode)
               (g n (EL n insts))` by
          (simp[Abbr `g`] >> irule ao_transform_inst_non_term >> simp[]) >>
        gvs[] >> fs[listTheory.EVERY_MEM]) >>
      `EL i (FLAT (MAPi g insts)) =
       EL i (FRONT (FLAT (MAPi g insts)))` by (
        irule (GSYM rich_listTheory.EL_FRONT) >>
        fs[listTheory.NULL_EQ, rich_listTheory.LENGTH_FRONT]) >>
      `~is_terminator (EL i (FRONT (FLAT (MAPi g insts)))).inst_opcode`
        by (qpat_x_assum `EVERY _ (FLAT (MAPi g (FRONT _)))` mp_tac >>
            qpat_x_assum `FRONT _ = _` (fn th => REWRITE_TAC [GSYM th]) >>
            simp[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT,
                 listTheory.NULL_EQ]) >>
      gvs[])
  >- (simp[Abbr `g`] >>
      MATCH_MP_TAC ao_transform_inst_phi_prefix >>
      rpt conj_tac >> gvs[])
QED

(* ===== ao_transform_block preserves bb_succs ===== *)

Triviality ao_resolve_iszero_op_get_label[local]:
  !targets opc op.
    get_label (ao_resolve_iszero_op targets opc op) = get_label op
Proof
  rpt gen_tac >>
  Cases_on `op` >>
  PURE_REWRITE_TAC[ao_resolve_iszero_op_def] >> simp[] >>
  Cases_on `ALOOKUP targets s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[LET_THM] >>
  IF_CASES_TAC >> simp[get_label_def]
QED

Triviality ao_resolve_iszero_inst_get_successors[local]:
  !targets inst.
    get_successors (ao_resolve_iszero_inst targets inst) = get_successors inst
Proof
  rpt strip_tac >>
  simp[get_successors_def, ao_resolve_iszero_inst_def,
       ao_resolve_iszero_inst_opcode] >>
  IF_CASES_TAC >> simp[] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
       listTheory.MAP_EQ_f] >>
  rpt strip_tac >>
  simp[ao_resolve_iszero_op_get_label]
QED

Triviality get_succ_last_map[local]:
  !f l. l <> [] /\ (!x. get_successors (f x) = get_successors x) ==>
        get_successors (LAST (MAP f l)) = get_successors (LAST l)
Proof
  rpt strip_tac >> fs[listTheory.LAST_MAP]
QED

(* The resolve post-pass only touches PHI operands, and get_successors is
   invariant under iszero resolution, so bb_succs is preserved. *)
Triviality ao_resolve_phis_block_bb_succs[local]:
  !targets bb. bb_succs (ao_resolve_phis_block targets bb) = bb_succs bb
Proof
  rpt gen_tac >>
  simp[bb_succs_def, ao_resolve_phis_block_def] >>
  qmatch_goalsub_abbrev_tac `MAP h bb.bb_instructions` >>
  `!x. get_successors (h x) = get_successors x` by
    rw[Abbr `h`, ao_resolve_iszero_inst_get_successors] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  `get_successors (LAST (h h'::MAP h t)) = get_successors (LAST (h'::t))`
    suffices_by simp[] >>
  `h h'::MAP h t = MAP h (h'::t)` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule get_succ_last_map >> fs[]
QED

Triviality ao_transform_block_label[local]:
  !mid dfg ra targets bb.
    (ao_transform_block mid dfg ra targets bb).bb_label = bb.bb_label
Proof
  simp[ao_transform_block_def, ao_resolve_phis_block_def]
QED

Triviality ao_transform_block_bb_succs[local]:
  !mid dfg ra targets bb.
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions ==>
    bb_succs (ao_transform_block mid dfg ra targets bb) = bb_succs bb
Proof
  rpt strip_tac >>
  simp[ao_transform_block_def, ao_resolve_phis_block_bb_succs] >>
  simp[bb_succs_def] >>
  fs[bb_well_formed_def] >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  qabbrev_tac `g = \idx inst.
    ao_transform_inst mid dfg ra bb.bb_label idx targets inst` >>
  `!i. i < LENGTH insts ==> g i (EL i insts) <> []` by
    simp[Abbr `g`, ao_transform_inst_ne] >>
  `FLAT (MAPi g insts) <> []` by
    (irule flat_mapi_ne >> simp[]) >>
  `inst_wf (LAST insts)` by
    (fs[listTheory.EVERY_MEM] >>
     metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  `g (PRE (LENGTH insts)) (LAST insts) =
     [ao_resolve_iszero_inst targets (LAST insts)]` by
    (simp[Abbr `g`] >> irule ao_transform_inst_term >> simp[]) >>
  `LAST (FLAT (MAPi g insts)) =
   LAST (g (PRE (LENGTH insts)) (LAST insts))` by (
    irule last_flat_mapi >> simp[] >>
    qexists_tac `ao_resolve_iszero_inst targets (LAST insts)` >>
    simp[]) >>
  fs[] >>
  `!inst. get_successors (ao_resolve_iszero_inst targets inst) =
          get_successors inst` by
    simp[ao_resolve_iszero_inst_get_successors] >>
  Cases_on `FLAT (MAPi g insts)` >> fs[] >>
  Cases_on `insts` >> fs[]
QED

(* ===== Targets no-label property ===== *)


(* ===== Succs closed ===== *)

Triviality ao_phase3_succs_closed[local]:
  !mid dfg ra targets fn.
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks /\
    (!bb succ. MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
       MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)) ==>
    !bb succ.
      MEM bb (MAP (ao_transform_block mid dfg ra targets) fn.fn_blocks) /\
      MEM succ (bb_succs bb) ==>
      MEM succ (MAP (\bb. bb.bb_label)
        (MAP (ao_transform_block mid dfg ra targets) fn.fn_blocks))
Proof
  rpt strip_tac >>
  gvs[listTheory.MEM_MAP] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
       ao_transform_block_label] >>
  `bb_well_formed y /\ EVERY inst_wf y.bb_instructions` by
    (conj_tac >- res_tac >>
     fs[listTheory.EVERY_MEM] >> res_tac) >>
  `bb_succs (ao_transform_block mid dfg ra targets y) =
   bb_succs y` by (
    match_mp_tac ao_transform_block_bb_succs >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  fs[] >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists_tac `ao_transform_block mid dfg ra targets bb` >>
  simp[ao_transform_block_label] >>
  qexists_tac `bb` >> simp[]
QED

(* ===== Phase 3 preserves wf_function ===== *)

Theorem ao_phase3_preserves_wf:
  !mid dfg ra targets fn.
    wf_function fn /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid) ==>
    wf_function (function_map_transform
      (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = ao_transform_block mid dfg ra targets` >>
  simp[wf_function_def, function_map_transform_def,
       fn_labels_def, fn_has_entry_def] >>
  qpat_x_assum `wf_function fn` mp_tac >>
  simp_tac std_ss [wf_function_def, fn_labels_def, fn_has_entry_def,
       fn_succs_closed_def] >>
  simp[] >> strip_tac >>
  rpt conj_tac
  >- (simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
           Abbr `bt`, ao_transform_block_label])
  >- (rpt strip_tac >> gvs[listTheory.MEM_MAP, Abbr `bt`] >>
      irule ao_transform_block_bb_wf >>
      res_tac >> gvs[listTheory.EVERY_MEM] >> res_tac)
  >- (simp[Abbr `bt`] >>
      match_mp_tac ao_phase3_succs_closed >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  (* fn_inst_ids_distinct *)
  >- (simp[Abbr `bt`, GSYM function_map_transform_def] >>
      irule ao_phase3_inst_ids_distinct >> fs[])
QED

(* ===== Phase 3 preserves EVERY inst_wf ===== *)

(* Each ao_opt_* rewrite produces well-formed instructions, given the
   original output arity (= 1 for the arithmetic opcodes they fire on). *)
Triviality ao_opt_shift_inst_wf[local]:
  !inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_shift inst)
Proof
  rpt strip_tac >> simp[ao_opt_shift_def] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_signextend_inst_wf[local]:
  !ra lbl idx inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_signextend ra lbl idx inst)
Proof
  rpt strip_tac >> simp[ao_opt_signextend_def, LET_THM] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_exp_inst_wf[local]:
  !inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_exp inst)
Proof
  rpt strip_tac >> simp[ao_opt_exp_def] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_addsub_inst_wf[local]:
  !inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_addsub inst)
Proof
  rpt strip_tac >> simp[ao_opt_addsub_def, LET_THM] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_and_inst_wf[local]:
  !inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_and inst)
Proof
  rpt strip_tac >> simp[ao_opt_and_def] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_muldiv_inst_wf[local]:
  !inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_muldiv inst)
Proof
  rpt strip_tac >> simp[ao_opt_muldiv_def, LET_THM] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_or_inst_wf[local]:
  !dfg inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_or dfg inst)
Proof
  rpt strip_tac >> simp[ao_opt_or_def] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_eq_inst_wf[local]:
  !mid dfg inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_eq mid dfg inst)
Proof
  rpt strip_tac >> simp[ao_opt_eq_def, LET_THM] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_opt_comparator_inst_wf[local]:
  !mid dfg ra lbl idx inst. inst_wf inst /\ LENGTH inst.inst_outputs = 1 ==>
    EVERY inst_wf (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, ao_cmp_prefer_iz_zero_def,
       ao_cmp_prefer_iz_max_def, ao_cmp_prefer_iz_general_def,
       ao_signed_boundaries_def, ao_unsigned_boundaries_def, LET_THM] >>
  every_case_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >> fs[inst_wf_def]
QED

(* ao_opt_producer only fires on BALANCE/EXTCODESIZE/SIGNEXTEND, all of
   which have output arity 1 once inst_wf holds, so no extra hyp needed. *)
Triviality ao_opt_producer_inst_wf[local]:
  !dfg inst result.
    inst_wf inst /\ ao_opt_producer dfg inst = SOME result ==>
    EVERY inst_wf result
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_opt_producer _ _ = _` mp_tac >>
  simp[ao_opt_producer_def] >>
  every_case_tac >> simp[] >> strip_tac >> gvs[] >> fs[inst_wf_def]
QED

Triviality ao_post_flip_inst_wf[local]:
  !inst. inst_wf inst ==> inst_wf (ao_post_flip_inst inst)
Proof
  rpt strip_tac >> simp[ao_post_flip_inst_def] >>
  every_case_tac >> gvs[] >> fs[inst_wf_def]
QED

(* Fix B: post-flipping only the trailing instruction preserves inst_wf. *)
Triviality post_flip_last_inst_wf[local]:
  !l. EVERY inst_wf l ==> EVERY inst_wf (ao_post_flip_last l)
Proof
  ho_match_mp_tac ao_post_flip_last_ind >> rpt conj_tac
  >- simp[ao_post_flip_last_def]
  >- (rw[ao_post_flip_last_def] >> irule ao_post_flip_inst_wf >> fs[])
  >- (rw[ao_post_flip_last_def] >> fs[])
QED

Triviality ao_peephole_inst_inst_wf[local]:
  !mid dfg ra lbl idx inst.
    inst_wf inst ==>
    EVERY inst_wf (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (asm_simp_tac (srw_ss()) [] >> NO_TAC) >>
  FIRST [
    irule ao_opt_shift_inst_wf,
    irule ao_opt_signextend_inst_wf,
    irule ao_opt_exp_inst_wf,
    irule ao_opt_addsub_inst_wf,
    irule ao_opt_and_inst_wf,
    irule ao_opt_muldiv_inst_wf,
    irule ao_opt_or_inst_wf,
    irule ao_opt_eq_inst_wf,
    irule ao_opt_comparator_inst_wf
  ] >> gvs[inst_wf_def]
QED

Triviality ao_transform_inst_inst_wf[local]:
  !fn0 mid dfg ra lbl idx inst.
    inst_wf inst ==>
    EVERY inst_wf
      (ao_transform_inst mid dfg ra lbl idx
        (ao_compute_fn_iszero_targets fn0) inst)
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  IF_CASES_TAC >- simp[] >>
  qabbrev_tac
    `inst0 = ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn0) inst` >>
  `inst_wf inst0` by
    (simp[Abbr `inst0`] >> irule ao_resolve_iszero_inst_wf >> simp[]) >>
  `inst0.inst_opcode = inst.inst_opcode /\
   inst0.inst_outputs = inst.inst_outputs` by
    simp[Abbr `inst0`, ao_resolve_iszero_inst_def] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[] >>
  CASE_TAC
  >- (* NONE: pre-flip then peephole then post-flip *)
     (simp[LET_THM] >> irule post_flip_last_inst_wf >>
      irule ao_peephole_inst_inst_wf >> irule ao_pre_flip_inst_wf >> simp[])
  >- (* SOME result: post-flip *)
     (rename1 `ao_opt_producer dfg inst0 = SOME result` >>
      irule post_flip_last_inst_wf >>
      irule ao_opt_producer_inst_wf >> metis_tac[])
QED

Triviality ao_transform_block_inst_wf[local]:
  !mid dfg ra fn0 bb.
    EVERY inst_wf bb.bb_instructions ==>
    EVERY inst_wf
      (ao_transform_block mid dfg ra
         (ao_compute_fn_iszero_targets fn0) bb).bb_instructions
Proof
  rpt strip_tac >>
  simp[ao_transform_block_def] >>
  irule ao_resolve_phis_block_inst_wf >>
  simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
       indexedListsTheory.MEM_MAPi, PULL_EXISTS] >>
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM x (ao_transform_inst _ _ _ _ i _ _)` >>
  `EVERY inst_wf (ao_transform_inst mid dfg ra bb.bb_label i
     (ao_compute_fn_iszero_targets fn0) (EL i bb.bb_instructions))` by
    (irule ao_transform_inst_inst_wf >> fs[listTheory.EVERY_EL]) >>
  fs[listTheory.EVERY_MEM]
QED

Theorem ao_phase3_preserves_inst_wf:
  !mid dfg ra fn0.
    EVERY inst_wf (fn_insts fn0) ==>
    EVERY inst_wf (fn_insts (function_map_transform
      (ao_transform_block mid dfg ra (ao_compute_fn_iszero_targets fn0)) fn0))
Proof
  rpt strip_tac >>
  simp[function_map_transform_def, fn_insts_def] >>
  qpat_x_assum `EVERY inst_wf (fn_insts fn0)` mp_tac >>
  simp[fn_insts_def] >>
  qspec_tac (`fn0.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> fs[listTheory.EVERY_APPEND] >> rpt conj_tac >>
  TRY (irule ao_transform_block_inst_wf >> simp[] >> NO_TAC) >>
  first_x_assum irule >> simp[]
QED

val _ = export_theory();
