(* Step-level invariant obligations for algebraic optimization.
 *
 * Three obligations required by analysis_block_sim_inv_at in
 * ao_block_sim_range (algebraicOptProofsScript.sml):
 *
 *   1. in_range_state compatible with state_equiv fv
 *   2. sinv (dfg + chain_inv + chains_defined) preserved by step_inst
 *   3. sinv compatible with state_equiv fv
 *
 * Also: chain variable freshness (needed by 3 and block-level compat).
 *
 * Proof strategy:
 *   1. Range-tracked vars come from fn0 instruction outputs/operands,
 *      which map to fn outputs/operands, which are NOTIN fv.
 *   2. ao_dfg_inv: use ao_dfg_inv_step_any (exists).
 *      chain_inv/chains_defined: use step_preserved lemmas from
 *      aoResolveObligation with SSA side condition (chain vars not
 *      overwritten by the stepped instruction).
 *   3. ao_dfg_inv: use ao_dfg_inv_state_equiv_compat (exists).
 *      chain_inv/chains_defined: use state_equiv_compat lemmas from
 *      aoResolveObligation with ao_chain_vars_not_in_fv.
 *)

Theory aoStepInvObligation
Ancestors
  algebraicOptDefs aoResolveObligation aoRangeObligation
  algebraicOptWf
  stateEquiv venomWf venomExecSemantics venomInst venomInstProofs
  venomInstProps
  analysisSimDefs rangeAnalysisProofs dfgAnalysisProps
Libs
  pairLib BasicProvers

(* Chain variable names from ao_compute_fn_iszero_targets fn0 are
   not in ao_fn_fresh_vars fn. Chain elements are Var references to
   instruction operands/outputs of fn0, which map back to fn instruction
   operands/outputs via ao_handle_offset_inst. *)
Triviality fn_insts_blocks_map_offset:
  !bbs inst.
    MEM inst (fn_insts_blocks
      (MAP (\b. b with bb_instructions :=
        MAP ao_handle_offset_inst b.bb_instructions) bbs)) ==>
    ?inst0. MEM inst0 (fn_insts_blocks bbs) /\
            inst = ao_handle_offset_inst inst0
Proof
  Induct >> rpt strip_tac
  >- fs[fn_insts_blocks_def, listTheory.MAP]
  >- (fs[fn_insts_blocks_def, listTheory.MAP,
         listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
      metis_tac[])
QED

Triviality chain_el_from_insts:
  !insts acc v chain k.
    (!v' chain' k'. ALOOKUP acc v' = SOME chain' /\
       k' < LENGTH chain' ==>
       (?inst. MEM inst insts /\ MEM (EL k' chain') inst.inst_operands) \/
       (?inst x. MEM inst insts /\ MEM x inst.inst_outputs /\
                 EL k' chain' = Var x)) /\
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    k < LENGTH chain ==>
    (?inst. MEM inst insts /\ MEM (EL k chain) inst.inst_operands) \/
    (?inst x. MEM inst insts /\ MEM x inst.inst_outputs /\
              EL k chain = Var x)
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> conj_tac
  >- (rpt strip_tac >>
      simp[ao_compute_iszero_step_def] >>
      Cases_on `h.inst_opcode = ISZERO` >> simp[]
      >- (Cases_on `h.inst_operands` >> simp[] >>
          Cases_on `h.inst_outputs` >> simp[] >>
          Cases_on `t` >> simp[] >>
          Cases_on `t'` >> simp[] >>
          simp[LET_THM] >>
          rename1 `h.inst_operands = [inp]` >>
          rename1 `h.inst_outputs = [out_var]` >>
          Cases_on `v' = out_var` >> simp[]
          >- (strip_tac >> gvs[listTheory.LENGTH_SNOC] >>
              Cases_on `k' < LENGTH
                (case inp of
                   Var v'' => (case ALOOKUP acc v'' of
                                 SOME ch => ch
                               | NONE => [inp])
                 | _ => [inp])`
              >- (simp[listTheory.EL_SNOC] >>
                  Cases_on `inp`
                  >- (simp[] >> DISJ1_TAC >> qexists_tac `h` >> simp[])
                  >- (simp[] >> Cases_on `ALOOKUP acc s` >> simp[]
                      >- (res_tac >> metis_tac[])
                      >- (DISJ1_TAC >> qexists_tac `h` >> simp[]))
                  >- (simp[] >> DISJ1_TAC >> qexists_tac `h` >> simp[]))
              >- (`k' = LENGTH
                    (case inp of
                       Var v'' => (case ALOOKUP acc v'' of
                                     SOME ch => ch
                                   | NONE => [inp])
                     | _ => [inp])` by simp[] >>
                  simp[listTheory.EL_SNOC] >>
                  DISJ2_TAC >> qexists_tac `h` >> qexists_tac `out_var` >>
                  simp[]))
          >- (strip_tac >> res_tac >> metis_tac[]))
      >- (rpt strip_tac >> res_tac >> metis_tac[]))
  >- metis_tac[]
QED

Theorem ao_chain_vars_not_in_fv:
  !fn fn0 targets fv v chain k x.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    ALOOKUP targets v = SOME chain /\
    k < LENGTH chain /\ EL k chain = Var x ==>
    x NOTIN fv
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qspecl_then [`fn_insts (fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks)`,
    `[] : (string # operand list) list`, `v`, `chain`, `k`]
    mp_tac chain_el_from_insts >>
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  strip_tac >> gvs[]
  >- (qpat_x_assum `MEM inst _` mp_tac >>
      simp[fn_insts_def] >> strip_tac >>
      drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
      Cases_on `inst0.inst_opcode = ADD /\
                ?l v'. inst0.inst_operands = [Label l; Lit v']`
      >- (gvs[ao_handle_offset_inst_def] >>
          `MEM (Var x) [Label l; Lit v']` by metis_tac[] >> gvs[])
      >- (`(ao_handle_offset_inst inst0).inst_operands = inst0.inst_operands` by
            (simp[ao_handle_offset_inst_def] >>
             Cases_on `inst0.inst_opcode = ADD` >> simp[] >>
             Cases_on `inst0.inst_operands` >> simp[] >>
             Cases_on `t` >> simp[] >>
             Cases_on `h` >> simp[] >>
             Cases_on `h'` >> simp[] >>
             Cases_on `t'` >> simp[]) >>
          gvs[] >>
          first_x_assum irule >>
          qexists_tac `inst0` >>
          simp[fn_insts_def] >>
          Induct_on `fn.fn_blocks` >> simp[fn_insts_blocks_def] >>
          rpt strip_tac >> gvs[] >> metis_tac[]))
  >- (qpat_x_assum `MEM inst _` mp_tac >>
      simp[fn_insts_def] >> strip_tac >>
      drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
      fs[ao_handle_offset_inst_outputs] >>
      first_x_assum irule >> qexists_tac `inst0` >>
      simp[fn_insts_def] >>
      Induct_on `fn.fn_blocks` >> simp[fn_insts_blocks_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
QED

(* in_range_state compatible with state_equiv fv:
   Range analysis only tracks variables from fn0 instruction
   outputs/operands, which are not in fv = ao_fn_fresh_vars fn. *)
Theorem ao_in_range_state_equiv_compat:
  !fn fn0 ra lbl n fv s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ra = range_analyze fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    in_range_state (range_at_inst ra lbl n) s1.vs_vars ==>
    in_range_state (range_at_inst ra lbl n) s2.vs_vars
Proof
  cheat
QED

(* sinv = ao_dfg_inv /\ ao_iszero_chain_inv /\ ao_chains_defined
   preserved through step_inst.
   ao_dfg_inv: via ao_dfg_inv_step_any (no INVOKE).
   chain_inv/chains_defined: via step_preserved lemmas + SSA side
   condition (chain vars not overwritten by instruction). *)
Theorem ao_sinv_step_preserved:
  !fn fn0 dfg targets bb idx fuel ctx s s'.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined targets s /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    ao_dfg_inv dfg (s' with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s' /\
    ao_chains_defined targets s'
Proof
  cheat
QED

(* sinv compatible with state_equiv fv:
   ao_dfg_inv: via ao_dfg_inv_state_equiv_compat + ao_dfg_outputs_not_in_fv.
   chain_inv/chains_defined: via state_equiv_compat lemmas +
   ao_chain_vars_not_in_fv. *)
Theorem ao_sinv_state_equiv_compat:
  !fn fn0 dfg targets fv s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    ao_dfg_inv dfg (s1 with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s1 /\
    ao_chains_defined targets s1 ==>
    ao_dfg_inv dfg (s2 with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s2 /\
    ao_chains_defined targets s2
Proof
  cheat
QED

(* range_sound compatible with state_equiv fv:
   range_sound tracks variables from fn0, which are not in fv. *)
Theorem ao_range_sound_state_equiv_compat:
  !fn fn0 ra fv lbl s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ra = range_analyze fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    range_sound (df_widen_at NONE ra lbl 0) s1 ==>
    range_sound (df_widen_at NONE ra lbl 0) s2
Proof
  cheat
QED
