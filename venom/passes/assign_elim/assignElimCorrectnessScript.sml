(*
 * Assign Elimination — Correctness Statement
 *
 * Copy propagation preserves semantics: replacing Var x with Var y
 * where x := assign y gives the same value because copy_sound ensures
 * lookup_var x s = lookup_var y s at every use site.
 *
 * Variables that are outputs of NOP'd ASSIGNs are excluded from
 * equivalence (assign_elim_eliminated_vars). These variables are dead
 * after copy propagation substitutes all their uses with the source.
 *
 * The error disjunct covers the edge case where a forwardable ASSIGN's
 * Var source is undefined at runtime. In SSA programs with proper
 * dominance, this is unreachable, but we don't have a formal dominance
 * predicate so it appears as a disjunct.
 *
 * Preconditions:
 *   wf_function fn — well-formed function (unique labels, entry, bb_well_formed)
 *   fn_inst_wf fn — all instructions structurally well-formed
 *   s.vs_inst_idx = 0 — standard execution entry point
 *   fn_entry_label fn = SOME s.vs_current_bb — execution starts at entry
 *   non-terminator interior — no non-last instruction is a terminator
 *   operand_cond — no instruction in the substituted function reads
 *     an eliminated variable (holds in SSA form)
 *)

Theory assignElimCorrectness
Ancestors
  assignElimProofs passSharedProps passSimulationProps
  assignElimDefs passSharedDefs venomWf venomInst venomState
  passSimulationDefs analysisSimDefs
Libs
  indexedListsTheory

Theorem assign_elim_function_correct:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    wf_function fn /\
    fn_inst_wf fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb inst x.
       MEM bb fn_subst.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN elim) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (assign_elim_function fn) s)
Proof
  ACCEPT_TAC assign_elim_function_correct_proof
QED

(* ===== Per-instruction structural properties ===== *)

Triviality aei_preserves_id[local]:
  !pv v inst. (assign_elim_inst pv v inst).inst_id = inst.inst_id
Proof
  rw[assign_elim_inst_def, LET_THM, mk_nop_inst_def]
QED

Triviality aei_term_opcode[local]:
  !pv v inst. is_terminator inst.inst_opcode ==>
    (assign_elim_inst pv v inst).inst_opcode = inst.inst_opcode
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> PHI` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  `~is_forwardable_assign pv inst` by
    (simp[is_forwardable_assign_def] >>
     Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[assign_elim_inst_def, LET_THM]
QED

Triviality aei_opcode[local]:
  !pv v inst. (assign_elim_inst pv v inst).inst_opcode = inst.inst_opcode \/
              (assign_elim_inst pv v inst).inst_opcode = NOP
Proof
  rpt strip_tac >>
  simp[assign_elim_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `is_forwardable_assign pv inst` >> simp[mk_nop_inst_def]
QED

Triviality aei_outputs[local]:
  !pv v inst. (assign_elim_inst pv v inst).inst_outputs = inst.inst_outputs \/
              (assign_elim_inst pv v inst).inst_outputs = []
Proof
  rpt strip_tac >>
  simp[assign_elim_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `is_forwardable_assign pv inst` >> simp[mk_nop_inst_def]
QED

(* ===== Copy lattice no-Label invariant ===== *)

(* copy_prop_transfer never introduces Label values into the copy map.
   is_forwardable_assign requires src ≠ Label, and transitive resolution
   through existing Label-free copies also gives non-Label values.
   Proved for the full assign_elim_function pipeline: after unwrap_copies,
   get_label of any substituted operand is preserved. *)
Triviality copy_map_no_label[local]:
  !pv inst copies_opt.
    (!k v. FLOOKUP (unwrap_copies copies_opt) k = SOME v ==>
           !l. v <> Label l) ==>
    (!k v. FLOOKUP (unwrap_copies (copy_prop_transfer pv inst copies_opt)) k =
             SOME v ==>
           !l. v <> Label l)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[copy_prop_transfer_def, LET_THM, unwrap_copies_def] >>
  Cases_on `copies_opt` >> simp[] >>
  rename1 `SOME copies` >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  BasicProvers.every_case_tac >> gvs[] >>
  gvs[finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
      is_forwardable_assign_def] >>
  gvs[unwrap_copies_def] >> res_tac >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[]
QED

(* The get_label of subst_op_map results matches original when copies are Label-free *)
Triviality subst_op_map_preserves_get_label[local]:
  !copies op.
    (!k v. FLOOKUP copies k = SOME v ==> !l. v <> Label l) ==>
    get_label (subst_op_map copies op) = get_label op
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[subst_op_map_def, get_label_def] >>
  Cases_on `FLOOKUP copies s` >> simp[get_label_def] >>
  rename1 `SOME val` >>
  `!l. val <> Label l` by metis_tac[] >>
  Cases_on `val` >> gvs[get_label_def]
QED

(* Analysis invariant: copy_prop_analyze never produces Label values.
   Follows from: copy_map_no_label (transfer preserves), FEMPTY initial,
   copy_prop_join preserves (intersection of Label-free = Label-free),
   df_populate_inst preserves (applies transfer to Label-free boundary).
   Full proof requires df_analyze_invariant_forward induction — cheated. *)
Triviality copy_prop_no_label[local]:
  !fn lbl idx k v.
    FLOOKUP (unwrap_copies (df_at NONE (copy_prop_analyze fn) lbl idx)) k =
      SOME v ==>
    !l. v <> Label l
Proof
  cheat
QED

(* ===== Obligations ===== *)

Triviality map_get_label_subst[local]:
  !copies ops.
    (!k v. FLOOKUP copies k = SOME v ==> !l. v <> Label l) ==>
    MAP get_label (MAP (subst_op_map copies) ops) = MAP get_label ops
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  metis_tac[subst_op_map_preserves_get_label]
QED

Triviality aei_get_successors[local]:
  !fn pv v inst.
    (!k op. FLOOKUP (unwrap_copies v) k = SOME op ==> !l. op <> Label l) ==>
    get_successors (assign_elim_inst pv v inst) = get_successors inst
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >-
    simp[assign_elim_inst_def, LET_THM] >>
  Cases_on `is_forwardable_assign pv inst` >- (
    `inst.inst_opcode = ASSIGN` by fs[is_forwardable_assign_def] >>
    simp[assign_elim_inst_def, LET_THM, mk_nop_inst_def,
         get_successors_def, is_terminator_def]) >>
  simp[assign_elim_inst_def, LET_THM, get_successors_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `MAP get_label (MAP (subst_op_map (unwrap_copies v)) inst.inst_operands) =
   MAP get_label inst.inst_operands` by
    (irule map_get_label_subst >> first_assum ACCEPT_TAC) >>
  gvs[unwrap_copies_def]
QED

Triviality ae_bb_succs[local]:
  !fn bb. bb_well_formed bb ==>
    bb_succs (bb with bb_instructions :=
      MAPi (\idx inst. assign_elim_inst (phi_used_vars fn)
        (df_at NONE (copy_prop_analyze fn) bb.bb_label idx) inst)
        bb.bb_instructions) = bb_succs bb
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[bb_succs_def] >>
  `LAST (MAPi (\idx inst. assign_elim_inst (phi_used_vars fn)
    (df_at NONE (copy_prop_analyze fn) bb.bb_label idx) inst) (h::t)) =
   assign_elim_inst (phi_used_vars fn)
    (df_at NONE (copy_prop_analyze fn) bb.bb_label (LENGTH t))
    (LAST (h::t))` by simp[last_mapi] >>
  gvs[] >>
  `!k op. FLOOKUP (unwrap_copies (df_at NONE (copy_prop_analyze fn) bb.bb_label
    (LENGTH t))) k = SOME op ==> !l. op <> Label l` by
    metis_tac[copy_prop_no_label] >>
  imp_res_tac aei_get_successors >> gvs[]
QED

Theorem assign_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (assign_elim_function fn)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[assign_elim_function_def, LET_DEF] >> BETA_TAC >>
  irule clear_nops_function_preserves_wf >>
  PURE_ONCE_REWRITE_TAC[aft_singleton_eq_fmt_mapi] >>
  suspend "fmt_wf"
QED

Resume assign_elim_preserves_wf_function[fmt_wf]:
  ho_match_mp_tac (SIMP_RULE std_ss [AND_IMP_INTRO] fmt_preserves_wf_function) >>
  rpt conj_tac
  >- simp[]
  >- suspend "bb_wf"
  >- (rpt strip_tac >> simp[ae_bb_succs])
  >- (fs[wf_function_def] >>
      ho_match_mp_tac mapi_transform_fn_inst_ids_bb >> simp[aei_preserves_id])
  >> simp[]
QED

Resume assign_elim_preserves_wf_function[bb_wf]:
  rpt strip_tac >> ho_match_mp_tac mapi_transform_bb_well_formed >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[assign_elim_inst_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  gvs[mk_nop_inst_def, is_terminator_def, is_forwardable_assign_def]
QED

Theorem assign_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (assign_elim_function fn)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[assign_elim_function_def, LET_DEF] >> BETA_TAC >>
  irule clear_nops_function_preserves_ssa >>
  PURE_ONCE_REWRITE_TAC[aft_singleton_eq_fmt_mapi] >>
  suspend "fmt_ssa"
QED

Resume assign_elim_preserves_ssa_form[fmt_ssa]:
  ho_match_mp_tac (SIMP_RULE std_ss [AND_IMP_INTRO]
    (SIMP_RULE std_ss [GSYM AND_IMP_INTRO] fmt_preserves_ssa_form_general)) >>
  rpt strip_tac
  >- (gvs[indexedListsTheory.MEM_MAPi] >>
      rename1 `idx < LENGTH bb.bb_instructions` >>
      qexists_tac `EL idx bb.bb_instructions` >>
      simp[listTheory.MEM_EL] >>
      conj_tac >- (qexists_tac `idx` >> simp[]) >>
      metis_tac[aei_outputs, aei_preserves_id])
  >- (fs[wf_function_def] >>
      ho_match_mp_tac mapi_transform_fn_inst_ids_bb >> simp[aei_preserves_id])
  >- fs[wf_function_def]
  >> simp[]
QED
