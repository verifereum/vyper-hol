(* Chain-structure facts + per-operand iszero relationship derivation.
 *
 *   chain_iszero_rel_from_inv  — derives the (rel) adjacency condition of
 *   ao_resolve_iszero_inst_sim_local from the loop-robust invariants
 *   strict_dom_iszero_inv (aoStrictDomObligation) and
 *   within_block_iszero_inv (aoIsZeroInv), via chain_iszero_placement.
 *
 * Ported verbatim from the (deleted) monolith proof. The exported
 * ao_fn_targets_* facts live in aoTargetProps and are reused from there.
 *)
Theory aoChainStruct
Ancestors
  algebraicOptDefs aoStrictDomObligation aoIsZeroInv
  aoTargetProps aoResolveObligation
  venomWf venomState venomInst venomExecSemantics
  venomInstProps venomExecProps venomExecProofs
  stateEquiv dfgAnalysisProps passSimulationProps
Libs
  pairLib BasicProvers

val _ = delsimps ["strict_dom_iszero_inv_def"]

(* ===== chain alist case lemma ===== *)
Triviality iszero_step_cases_strong[local]:
  !acc h. ao_compute_iszero_step acc h = acc \/
    ?out inp prev.
      h.inst_opcode = ISZERO /\
      h.inst_operands = [inp] /\ h.inst_outputs = [out] /\
      ao_compute_iszero_step acc h = (out, SNOC (Var out) prev) :: acc /\
      (prev = [inp] \/ ?s. inp = Var s /\ ALOOKUP acc s = SOME prev)
Proof
  rpt gen_tac >> simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  disj2_tac >> simp[] >> metis_tac[]
QED

(* ===== chain last / consecutive / placement / rel ===== *)
Triviality iszero_step_chain_last[local]:
  !h acc.
    (!v ch. ALOOKUP acc v = SOME ch /\ ch <> [] ==> LAST ch = Var v) ==>
    (!v ch. ALOOKUP (ao_compute_iszero_step acc h) v = SOME ch /\
       ch <> [] ==> LAST ch = Var v)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY (strip_tac >> first_x_assum irule >> gvs[] >> NO_TAC) >>
  simp[alistTheory.ALOOKUP_def] >>
  IF_CASES_TAC >> gvs[] >> strip_tac >>
  gvs[listTheory.LAST_SNOC, listTheory.LAST_DEF] >>
  first_x_assum irule >> gvs[]
QED

Triviality foldl_chain_last[local]:
  !insts acc.
    (!v ch. ALOOKUP acc v = SOME ch /\ ch <> [] ==> LAST ch = Var v) ==>
    (!v ch. ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME ch /\
       ch <> [] ==> LAST ch = Var v)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac iszero_step_chain_last >> first_assum ACCEPT_TAC
QED

Triviality ao_fn_targets_chain_last[local]:
  !fn v chain.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain /\
    chain <> [] ==>
    LAST chain = Var v
Proof
  rpt strip_tac >>
  gvs[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  mp_tac (Q.SPECL [`fn_insts fn`, `[]`] foldl_chain_last) >>
  simp[alistTheory.ALOOKUP_def]
QED

(* Chain consecutive ISZERO: consecutive chain elements correspond to
   an ISZERO instruction. EL (k+1) chain = Var w is an ISZERO output
   whose operand is EL k chain. *)
Triviality chain_consecutive_iszero_step_aux[local]:
  !acc inst v chain k w.
    (!v' ch. ALOOKUP acc v' = SOME ch /\ ch <> [] ==>
       LAST ch = Var v') ==>
    ALOOKUP (ao_compute_iszero_step acc inst) v = SOME chain ==>
    k + 1 < LENGTH chain ==>
    EL (k + 1) chain = Var w ==>
    (inst.inst_opcode = ISZERO /\
     inst.inst_operands = [EL k chain] /\
     MEM w inst.inst_outputs) \/
    (?v' chain'. ALOOKUP acc v' = SOME chain' /\
       k + 1 < LENGTH chain' /\ EL (k + 1) chain' = Var w /\
       EL k chain' = EL k chain)
Proof
  rpt gen_tac >> rpt strip_tac >>
  qspecl_then [`acc`, `inst`] strip_assume_tac iszero_step_cases_strong
  >- (* step = acc, passthrough *)
     (DISJ2_TAC >> qexistsl_tac [`v`, `chain`] >> gvs[])
  >- (* step changed, prev = [inp] *)
     (gvs[alistTheory.ALOOKUP_def, listTheory.SNOC] >>
      Cases_on `v = out` >> gvs[]
      >- (DISJ1_TAC >> `k = 0` by simp[] >>
          gvs[listTheory.EL, listTheory.HD])
      >- (DISJ2_TAC >> qexistsl_tac [`v`, `chain`] >> gvs[]))
  >- (* step changed, prev from ALOOKUP acc s *)
     (gvs[alistTheory.ALOOKUP_def] >>
      Cases_on `v = out` >> gvs[listTheory.LENGTH_SNOC]
      >- (rename1 `ALOOKUP acc sv = SOME prev` >>
          Cases_on `k + 1 < LENGTH prev`
          >- (DISJ2_TAC >>
              qexistsl_tac [`sv`, `prev`] >> simp[] >>
              `k < LENGTH prev` by simp[] >>
              gvs[listTheory.EL_SNOC])
          >- (DISJ1_TAC >>
              `k + 1 = LENGTH prev` by simp[] >>
              `prev <> []` by (strip_tac >> gvs[]) >>
              `LAST prev = Var sv` by metis_tac[] >>
              `k = PRE (LENGTH prev)` by simp[] >>
              `EL k prev = Var sv` by gvs[listTheory.LAST_EL] >>
              `k < LENGTH prev` by simp[] >>
              gvs[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC]))
      >- (DISJ2_TAC >> qexistsl_tac [`v`, `chain`] >> simp[]))
QED

Triviality chain_consecutive_iszero_foldl[local]:
  !insts acc v chain k w.
    (!v' ch. ALOOKUP acc v' = SOME ch /\ ch <> [] ==>
       LAST ch = Var v') ==>
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    k + 1 < LENGTH chain /\ EL (k + 1) chain = Var w ==>
    (?inst. MEM inst insts /\
            inst.inst_opcode = ISZERO /\
            inst.inst_operands = [EL k chain] /\
            MEM w inst.inst_outputs) \/
    (?v' chain'. ALOOKUP acc v' = SOME chain' /\
       k + 1 < LENGTH chain' /\ EL (k + 1) chain' = Var w /\
       EL k chain' = EL k chain)
Proof
  Induct >> rpt gen_tac >> strip_tac >> strip_tac
  >- (DISJ2_TAC >> qexistsl_tac [`v`, `chain`] >> gvs[])
  >- (gvs[Once listTheory.FOLDL] >>
      `!v' ch. ALOOKUP (ao_compute_iszero_step acc h) v' = SOME ch /\
         ch <> [] ==> LAST ch = Var v'` by
        (match_mp_tac iszero_step_chain_last >> first_assum ACCEPT_TAC) >>
      first_x_assum
        (qspecl_then [`ao_compute_iszero_step acc h`,
                      `v`, `chain`, `k`, `w`] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      impl_tac >- simp[] >>
      strip_tac
      >- (DISJ1_TAC >> metis_tac[])
      >- (mp_tac chain_consecutive_iszero_step_aux >>
          disch_then (qspecl_then [`acc`, `h`, `v'`, `chain'`, `k`, `w`]
            mp_tac) >>
          impl_tac >- first_x_assum ACCEPT_TAC >>
          impl_tac >- first_assum ACCEPT_TAC >>
          impl_tac >- first_assum ACCEPT_TAC >>
          impl_tac >- first_assum ACCEPT_TAC >>
          strip_tac
          >- (DISJ1_TAC >> qexists_tac `h` >> gvs[])
          >- (DISJ2_TAC >>
              qexistsl_tac [`v''`, `chain''`] >> gvs[] >>
              metis_tac[])))
QED

Theorem chain_consecutive_iszero:
  !fn v chain k w.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain /\
    k + 1 < LENGTH chain /\ EL (k + 1) chain = Var w ==>
    ?inst. MEM inst (fn_insts fn) /\
           inst.inst_opcode = ISZERO /\
           inst.inst_operands = [EL k chain] /\
           MEM w inst.inst_outputs
Proof
  rpt strip_tac >>
  gvs[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  mp_tac (Q.SPECL [`fn_insts fn`, `[]`] chain_consecutive_iszero_foldl) >>
  simp[alistTheory.ALOOKUP_def] >>
  disch_then drule_all >> strip_tac >>
  gvs[alistTheory.ALOOKUP_def] >> metis_tac[]
QED

(* Helper: definer of variable v used at position use_idx
   is either at position < use_idx in same block or in a strict dominator *)
Triviality def_dom_at_use[local]:
  !fn0 bb use_idx v.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    use_idx < LENGTH bb.bb_instructions /\
    MEM (Var v) (EL use_idx bb.bb_instructions).inst_operands ==>
    !def_inst.
      MEM def_inst (fn_insts fn0) /\
      MEM v def_inst.inst_outputs ==>
      (?j. j < use_idx /\ j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = def_inst) \/
      (?d_bb. MEM d_bb fn0.fn_blocks /\
              MEM def_inst d_bb.bb_instructions /\
              fn_dominates fn0 d_bb.bb_label bb.bb_label /\
              d_bb.bb_label <> bb.bb_label)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `def_dominates_uses fn0` by fs[wf_ssa_def] >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE [def_dominates_uses_def]) >>
  first_x_assum (qspecl_then [`bb`,
    `EL use_idx bb.bb_instructions`, `v`] mp_tac) >>
  impl_tac
  >- (simp[] >> irule listTheory.EL_MEM >> simp[]) >>
  strip_tac >>
  `MEM def_inst' (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts] >>
  `def_inst = def_inst'` by
    metis_tac[all_distinct_flat_map_unique, ssa_form_def] >>
  gvs[] >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `j = use_idx` by metis_tac[inst_ids_el_eq] >>
      gvs[] >> DISJ1_TAC >> qexists_tac `i` >> simp[])
  >- (DISJ2_TAC >> qexists_tac `def_bb` >> gvs[] >>
      `def_bb.bb_label <> bb.bb_label` by
        metis_tac[same_label_same_block] >>
      simp[])
QED

(* Base case: w = v, definer of v is at j < idx or strict dominator *)
Triviality chain_iszero_placement_base[local]:
  !fn0 bb idx v chain k iz_inst.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    MEM (Var v) (EL idx bb.bb_instructions).inst_operands /\
    ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    k + 1 < LENGTH chain /\
    EL (k + 1) chain = Var v /\
    MEM iz_inst (fn_insts fn0) /\
    MEM v iz_inst.inst_outputs ==>
    (?j. j < idx /\ j < LENGTH bb.bb_instructions /\
         EL j bb.bb_instructions = iz_inst) \/
    (?d_bb. MEM d_bb fn0.fn_blocks /\ MEM iz_inst d_bb.bb_instructions /\
            fn_dominates fn0 d_bb.bb_label bb.bb_label /\
            d_bb.bb_label <> bb.bb_label)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`fn0`, `bb`, `idx`, `v`] mp_tac def_dom_at_use >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `iz_inst` mp_tac) >>
  simp[]
QED

(* Chain ISZERO placement: each ISZERO in a chain for an operand of
   instruction idx is either at position j < idx in bb, or in a strict
   dominator. Uses complete induction on distance to chain end. *)
Triviality chain_iszero_placement_ind[local]:
  !n fn0 bb idx v chain k w iz_inst.
    n = LENGTH chain - (k + 2) /\
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    MEM (Var v) (EL idx bb.bb_instructions).inst_operands /\
    ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    k + 1 < LENGTH chain /\
    EL (k + 1) chain = Var w /\
    MEM iz_inst (fn_insts fn0) /\
    iz_inst.inst_opcode = ISZERO /\
    iz_inst.inst_operands = [EL k chain] /\
    MEM w iz_inst.inst_outputs ==>
    (?j. j < idx /\ j < LENGTH bb.bb_instructions /\
         EL j bb.bb_instructions = iz_inst) \/
    (?d_bb. MEM d_bb fn0.fn_blocks /\ MEM iz_inst d_bb.bb_instructions /\
            fn_dominates fn0 d_bb.bb_label bb.bb_label /\
            d_bb.bb_label <> bb.bb_label)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  Cases_on `k + 2 = LENGTH chain`
  >- (* Base: k+1 = LENGTH chain - 1, so w = v *)
     (`chain <> []` by (strip_tac >> gvs[]) >>
      `LAST chain = Var v` by
        metis_tac[ao_fn_targets_chain_last] >>
      `EL (k + 1) chain = Var v` by
        (`EL (k + 1) chain = EL (PRE (LENGTH chain)) chain` by
           (`PRE (LENGTH chain) = k + 1` by DECIDE_TAC >> simp[]) >>
         `EL (PRE (LENGTH chain)) chain = LAST chain` by
           simp[GSYM listTheory.LAST_EL] >>
         gvs[]) >>
      `w = v` by gvs[] >>
      irule chain_iszero_placement_base >> gvs[] >>
      qexists_tac `chain` >> qexists_tac `k` >> simp[])
  >- (* Step: k+2 < LENGTH chain, next chain element exists *)
     (`k + 2 < LENGTH chain` by DECIDE_TAC >>
      `?w'. EL (k + 2) chain = Var w'` by
        (qspecl_then [`fn0`, `v`, `chain`, `k + 2`] mp_tac
           ao_fn_targets_chain_tail_var >>
         impl_tac >- simp[] >> simp[]) >>
      qspecl_then [`fn0`, `v`, `chain`, `k + 1`, `w'`] mp_tac
        chain_consecutive_iszero >>
      impl_tac >- gvs[] >> strip_tac >>
      rename1 `MEM iz2 (fn_insts fn0)` >>
      (* iz2 uses Var w as operand, so def_dom gives iz_inst placement
         relative to iz2's position *)
      (* By IH, iz2 is at j2 < idx or in strict dominator *)
      `(?j2. j2 < idx /\ j2 < LENGTH bb.bb_instructions /\
             EL j2 bb.bb_instructions = iz2) \/
       (?d_bb2. MEM d_bb2 fn0.fn_blocks /\
                MEM iz2 d_bb2.bb_instructions /\
                fn_dominates fn0 d_bb2.bb_label bb.bb_label /\
                d_bb2.bb_label <> bb.bb_label)` by
        (first_x_assum (qspec_then `LENGTH chain - (k + 3)` mp_tac) >>
         impl_tac >- DECIDE_TAC >>
         disch_then (qspecl_then [`fn0`, `bb`, `idx`, `v`, `chain`,
           `k + 1`, `w'`, `iz2`] mp_tac) >>
         impl_tac >- gvs[] >>
         simp[]) >>
      gvs[]
      >- (* iz2 at j2 < idx in bb: w used at j2, def at < j2 *)
         (qspecl_then [`fn0`, `bb`, `j2`, `w`] mp_tac def_dom_at_use >>
          impl_tac >- (simp[] >> gvs[]) >>
          disch_then (qspec_then `iz_inst` mp_tac) >> simp[] >>
          strip_tac >> gvs[]
          >- (DISJ1_TAC >> qexists_tac `j` >> simp[])
          >- (DISJ2_TAC >> qexists_tac `d_bb` >> simp[]))
      >- (* iz2 in strict dominator d_bb2: w used in d_bb2 *)
         (`def_dominates_uses fn0` by fs[wf_ssa_def] >>
          qpat_x_assum `def_dominates_uses _`
            (strip_assume_tac o REWRITE_RULE [def_dominates_uses_def]) >>
          `MEM iz2 d_bb2.bb_instructions` by gvs[] >>
          `MEM (Var w) iz2.inst_operands` by gvs[] >>
          first_x_assum (qspecl_then [`d_bb2`, `iz2`, `w`] mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          `fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
          `MEM def_inst (fn_insts fn0)` by
            metis_tac[mem_block_mem_fn_insts] >>
          `iz_inst = def_inst` by
            metis_tac[all_distinct_flat_map_unique, ssa_form_def] >>
          gvs[] >>
          DISJ2_TAC >>
          Cases_on `def_bb = d_bb2`
          >- (qexists_tac `d_bb2` >> gvs[])
          >- (`def_bb.bb_label <> d_bb2.bb_label` by
                metis_tac[same_label_same_block] >>
              qexists_tac `def_bb` >> gvs[] >>
              conj_tac
              >- metis_tac[fn_dominates_trans]
              >- (strip_tac >>
                  `fn_dominates fn0 bb.bb_label d_bb2.bb_label` by
                    (gvs[] >> metis_tac[fn_dominates_trans]) >>
                  metis_tac[fn_dominates_antisym]))))
QED

Triviality chain_iszero_placement[local]:
  !fn0 bb idx v chain k w iz_inst.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    MEM (Var v) (EL idx bb.bb_instructions).inst_operands /\
    ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    k + 1 < LENGTH chain /\
    EL (k + 1) chain = Var w /\
    MEM iz_inst (fn_insts fn0) /\
    iz_inst.inst_opcode = ISZERO /\
    iz_inst.inst_operands = [EL k chain] /\
    MEM w iz_inst.inst_outputs ==>
    (?j. j < idx /\ j < LENGTH bb.bb_instructions /\
         EL j bb.bb_instructions = iz_inst) \/
    (?d_bb. MEM d_bb fn0.fn_blocks /\ MEM iz_inst d_bb.bb_instructions /\
            fn_dominates fn0 d_bb.bb_label bb.bb_label /\
            d_bb.bb_label <> bb.bb_label)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`LENGTH chain - (k + 2)`, `fn0`, `bb`, `idx`, `v`,
    `chain`, `k`, `w`, `iz_inst`] mp_tac chain_iszero_placement_ind >>
  simp[]
QED

(* Derive ao_resolve_iszero_inst_sim_local conditions from
   strict_dom_iszero_inv + within_block_iszero_inv *)
Theorem chain_iszero_rel_from_inv:
  !fn0 dfg targets bb idx inst s.
    wf_function fn0 /\ wf_ssa fn0 /\
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ao_targets_wf targets /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst = EL idx bb.bb_instructions /\
    bb.bb_label = s.vs_current_bb /\
    strict_dom_iszero_inv fn0 dfg s /\
    within_block_iszero_inv fn0 bb idx s ==>
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\ k + 1 < LENGTH chain ==>
                 !val_k val_k1.
                   eval_operand (EL k chain) s = SOME val_k /\
                   eval_operand (EL (k + 1) chain) s = SOME val_k1 ==>
                   val_k1 = bool_to_word (val_k = 0w))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  qpat_x_assum `targets = _` (SUBST_ALL_TAC) >>
  `?w. EL (k + 1) chain = Var w` by
    (qspecl_then [`fn0`, `v`, `chain`, `k + 1`] mp_tac
       ao_fn_targets_chain_tail_var >>
     impl_tac >- simp[] >> simp[]) >>
  qspecl_then [`fn0`, `v`, `chain`, `k`, `w`] mp_tac
    chain_consecutive_iszero >>
  impl_tac >- fs[] >> strip_tac >>
  rename1 `MEM iz_inst (fn_insts fn0)` >>
  `lookup_var w s = SOME val_k1` by
    (fs[eval_operand_def]) >>
  qspecl_then [`fn0`, `bb`, `idx`, `v`, `chain`, `k`, `w`,
    `iz_inst`] mp_tac chain_iszero_placement >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[]
  >- (* iz_inst at position j < idx in bb *)
     (qpat_x_assum `within_block_iszero_inv _ _ _ _`
        (mp_tac o REWRITE_RULE [within_block_iszero_inv_def]) >>
      disch_then (qspecl_then [`j`, `w`, `EL k chain`] mp_tac) >>
      impl_tac >- gvs[] >>
      disch_then (qspecl_then [`val_k1`, `val_k`] mp_tac) >>
      simp[])
  >- (* iz_inst in strict dominator *)
     (`?inst'. dfg_get_def (dfg_build_function fn0) w = SOME inst'` by
        metis_tac[dfgAnalysisPropsTheory.dfg_build_function_defs_complete] >>
      `MEM w inst'.inst_outputs /\ MEM inst' (fn_insts fn0)` by
        metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
      `iz_inst = inst'` by
        metis_tac[all_distinct_flat_map_unique, ssa_form_def] >>
      gvs[] >>
      qpat_x_assum `strict_dom_iszero_inv _ _ _`
        (mp_tac o REWRITE_RULE [strict_dom_iszero_inv_def]) >>
      disch_then (qspecl_then [`w`, `inst'`, `EL k chain`, `d_bb`]
        mp_tac) >>
      impl_tac >- gvs[] >>
      disch_then (qspecl_then [`val_k1`, `val_k`] mp_tac) >>
      simp[])
QED

val _ = export_theory();
