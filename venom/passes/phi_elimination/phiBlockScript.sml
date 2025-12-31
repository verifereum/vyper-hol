(*
 * PHI Elimination Block-Level Correctness
 *
 * This theory proves block-level correctness of PHI elimination.
 * transform_block_correct handles the OK case.
 * transform_block_result_equiv handles all result types.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - step_in_block_equiv            : Single step produces equivalent states
 *   - transform_block_correct        : Block OK case
 *   - transform_block_result_equiv   : Block result equivalence
 *
 * HELPER THEOREMS:
 *   - step_inst_*                    : PHI/ASSIGN evaluation lemmas
 *   - step_in_block_*_transform      : Halt/Revert/Error cases
 *   - step_*_preserves_prev_bb       : prev_bb preservation
 *
 * ============================================================================
 *)

Theory phiBlock
Ancestors
  phiWellFormed execEquiv venomSemProps venomSem venomState venomInst dfgDefs dfgOrigins phiTransform stateEquiv list

(* ==========================================================================
   Instruction Step Lemmas
   ========================================================================== *)

Theorem step_inst_assign_eval:
  !inst out op s.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    inst.inst_outputs = [out]
  ==>
    step_inst inst s =
      case eval_operand op s of
        SOME v => OK (update_var out v s)
      | NONE => Error "undefined operand"
Proof
  rw[step_inst_def]
QED

Theorem step_inst_phi_resolves_var_ok:
  !inst s s' src_var out prev.
    is_phi_inst inst /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var src_var) /\
    step_inst inst s = OK s'
  ==>
    ?v. lookup_var src_var s = SOME v /\ s' = update_var out v s
Proof
  rpt strip_tac >>
  fs[is_phi_inst_def] >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  simp[step_inst_def, eval_operand_def] >>
  Cases_on `lookup_var src_var s` >> simp[]
QED

(* ==========================================================================
   Transform Instruction Correctness
   ========================================================================== *)

(* KEY LEMMA: Transform instruction correctness *)
Theorem transform_inst_correct:
  !dfg inst s s' origin prev_bb v.
    step_inst inst s = OK s' /\
    well_formed_dfg dfg /\
    phi_single_origin dfg inst = SOME origin /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v) /\
    FLOOKUP dfg v = SOME origin
  ==>
    ?s''. step_inst (transform_inst dfg inst) s = OK s'' /\
          state_equiv s' s''
Proof
  rpt strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `origin.inst_outputs = [v]` by fs[well_formed_dfg_def] >>
  fs[transform_inst_def, is_phi_inst_def] >>
  qexists_tac `s'` >>
  conj_tac >- (
    qpat_x_assum `step_inst inst s = OK s'` mp_tac >>
    simp[step_inst_def, eval_operand_def] >>
    Cases_on `lookup_var v s` >> simp[] >>
    strip_tac >> fs[] >>
    Cases_on `inst.inst_outputs` >> fs[] >>
    Cases_on `t` >> fs[]
  ) >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Block Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Single step in block produces equivalent states *)
Theorem step_in_block_equiv:
  !dfg fn bb s s' is_term.
    step_in_block fn bb s = (OK s', is_term) /\
    well_formed_dfg dfg /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       s.vs_prev_bb = SOME prev_bb /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       FLOOKUP dfg v = SOME origin)
  ==>
    ?s''. step_in_block fn (transform_block dfg bb) s = (OK s'', is_term) /\
          state_equiv s' s''
Proof
  rpt strip_tac >>
  fs[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  rename1 `get_instruction bb _ = SOME curr_inst` >>
  imp_res_tac get_instruction_transform >>
  simp[] >>
  Cases_on `step_inst curr_inst s` >> fs[] >>
  simp[transform_inst_preserves_terminator] >>
  Cases_on `is_phi_inst curr_inst` >- (
    Cases_on `phi_single_origin dfg curr_inst` >- (
      imp_res_tac transform_inst_identity >> simp[state_equiv_refl]
    ) >>
    rename1 `phi_single_origin dfg curr_inst = SOME origin_inst` >>
    `phi_well_formed curr_inst.inst_operands` by metis_tac[] >>
    fs[is_phi_inst_def, step_inst_def] >>
    Cases_on `curr_inst.inst_outputs` >> fs[] >>
    Cases_on `t` >> fs[] >>
    rename1 `curr_inst.inst_outputs = [out_var]` >>
    Cases_on `s.vs_prev_bb` >> fs[] >>
    rename1 `s.vs_prev_bb = SOME prev_label` >>
    Cases_on `resolve_phi prev_label curr_inst.inst_operands` >> fs[] >>
    rename1 `resolve_phi _ _ = SOME resolved_op` >>
    Cases_on `eval_operand resolved_op s` >> fs[] >>
    `?var. resolved_op = Var var` by metis_tac[resolve_phi_well_formed] >>
    gvs[] >>
    (* Use the FLOOKUP assumption - prev_bb already substituted, 4 args *)
    first_x_assum (qspecl_then [`s.vs_inst_idx`, `curr_inst`, `origin_inst`, `var`] mp_tac) >>
    simp[] >> strip_tac >>
    `origin_inst.inst_outputs = [var]` by fs[well_formed_dfg_def] >>
    fs[transform_inst_def, eval_operand_def, step_inst_def] >>
    simp[state_equiv_refl]
  ) >>
  imp_res_tac transform_inst_non_phi >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Halt/Revert/Error Cases
   ========================================================================== *)

(* Halt/Revert results only come from non-PHI instructions *)
Theorem step_inst_halt_revert_not_phi:
  !inst s r.
    (step_inst inst s = Halt r \/ step_inst inst s = Revert r) ==>
    ~is_phi_inst inst
Proof
  rpt strip_tac >> fs[is_phi_inst_def, step_inst_def] >> gvs[AllCaseEqs()]
QED

(* For Halt/Revert cases, step_in_block on transformed block gives same result *)
Theorem step_in_block_halt_revert_transform:
  !dfg fn bb s s' is_term.
    (step_in_block fn bb s = (Halt s', is_term) \/
     step_in_block fn bb s = (Revert s', is_term))
  ==>
    step_in_block fn (transform_block dfg bb) s = step_in_block fn bb s
Proof
  rw[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  imp_res_tac get_instruction_transform >> fs[] >>
  gvs[AllCaseEqs()] >>
  `~is_phi_inst x` by (
    CCONTR_TAC >> fs[is_phi_inst_def, step_inst_def] >> gvs[AllCaseEqs()]
  ) >>
  imp_res_tac transform_inst_non_phi >> fs[]
QED

(* Convenient corollaries for the specific cases *)
Theorem step_in_block_halt_transform:
  !dfg fn bb s s' is_term.
    step_in_block fn bb s = (Halt s', is_term) ==>
    step_in_block fn (transform_block dfg bb) s = (Halt s', is_term)
Proof
  metis_tac[step_in_block_halt_revert_transform]
QED

Theorem step_in_block_revert_transform:
  !dfg fn bb s s' is_term.
    step_in_block fn bb s = (Revert s', is_term) ==>
    step_in_block fn (transform_block dfg bb) s = (Revert s', is_term)
Proof
  metis_tac[step_in_block_halt_revert_transform]
QED

(* ==========================================================================
   prev_bb Preservation
   ========================================================================== *)

(* ==========================================================================
   Block-level Correctness
   ========================================================================== *)

(* Helper: Block-level correctness for OK result *)
Theorem transform_block_correct:
  !fn bb st graph final_st.
    run_block fn bb st = OK final_st /\
    well_formed_dfg graph /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin graph inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       FLOOKUP graph v = SOME origin)
  ==>
    ?xformed_st. run_block fn (transform_block graph bb) st = OK xformed_st /\
                 state_equiv final_st xformed_st
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb st` >>
  Cases_on `q` >> simp[] >>
  strip_tac >>
  (* Apply step_in_block_equiv *)
  drule step_in_block_equiv >> simp[] >>
  disch_then (qspec_then `graph` mp_tac) >> simp[] >>
  impl_tac >- (
    conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
    rpt strip_tac >> first_x_assum drule_all >> simp[]
  ) >>
  strip_tac >> simp[Once run_block_def] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  `~s''.vs_halted` by gvs[state_equiv_def] >> simp[] >>
  Cases_on `r` >> gvs[] >- (
    qexists_tac `s''` >> simp[Once run_block_def]
  ) >>
  (* Non-terminator case: apply IH then run_block_state_equiv *)
  simp[Once run_block_def] >>
  first_x_assum (qspec_then `graph` mp_tac) >> simp[] >> impl_tac >- (
    conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
    rpt strip_tac >> first_x_assum drule_all >> simp[]
  ) >>
  strip_tac >> drule_all run_block_state_equiv >> strip_tac >>
  qexists_tac `r2` >> simp[] >>
  irule state_equiv_trans >> qexists_tac `xformed_st` >> simp[]
QED

(* result_equiv transitivity *)
Theorem result_equiv_trans:
  !r1 r2 r3. result_equiv r1 r2 /\ result_equiv r2 r3 ==> result_equiv r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[result_equiv_def] >> metis_tac[state_equiv_trans]
QED

(* Block-level correctness: transform preserves result equivalence. *)
Theorem transform_block_result_equiv:
  !fn bb st graph.
    well_formed_dfg graph /\
    st.vs_prev_bb <> NONE /\  (* Not at entry - PHI semantics require prev_bb *)
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin graph inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       FLOOKUP graph v = SOME origin) /\
    (* For Error case: if PHI with single origin errors, origin's output undefined *)
    (!inst origin src_var prev e s'.
       get_instruction bb s'.vs_inst_idx = SOME inst /\
       phi_single_origin graph inst = SOME origin /\
       origin.inst_outputs = [src_var] /\
       s'.vs_prev_bb = SOME prev /\
       step_inst inst s' = Error e ==>
       lookup_var src_var s' = NONE)
  ==>
    result_equiv (run_block fn bb st) (run_block fn (transform_block graph bb) st)
Proof
  recInduct run_block_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (* Unfold run_block on both sides *)
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >>
  rename1 `step_in_block fn bb s = (res, is_term)` >>
  Cases_on `res` >> gvs[]
  (* 4 cases: OK, Halt, Revert, Error *)
  >- ((* OK case *)
    drule step_in_block_equiv >> simp[] >>
    disch_then (qspec_then `graph` mp_tac) >> simp[] >>
    impl_tac >- (
      conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]
    ) >>
    strip_tac >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[] >>
    Cases_on `v.vs_halted` >> gvs[]
    >- (
      `s''.vs_halted` by fs[state_equiv_def] >>
      gvs[result_equiv_def]
    ) >>
    `~s''.vs_halted` by fs[state_equiv_def] >> simp[] >>
    Cases_on `is_term` >> gvs[result_equiv_def] >>
    `v.vs_prev_bb = s.vs_prev_bb` by (
      qspecl_then [`fn`, `bb`, `s`, `v`, `F`] mp_tac step_in_block_preserves_prev_bb >> simp[]
    ) >>
    `v.vs_prev_bb <> NONE` by simp[] >>
    first_x_assum (qspec_then `graph` mp_tac) >> simp[] >>
    impl_tac >- (
      conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]
    ) >>
    strip_tac >>
    irule result_equiv_trans >>
    qexists_tac `run_block fn (transform_block graph bb) v` >> simp[] >>
    irule run_block_result_equiv >> simp[]
  )
  >- ((* Halt case *)
    drule step_in_block_halt_transform >>
    disch_then (qspec_then `graph` mp_tac) >>
    simp[Once run_block_def, result_equiv_def, state_equiv_refl]
  )
  >- ((* Revert case *)
    drule step_in_block_revert_transform >>
    disch_then (qspec_then `graph` mp_tac) >>
    simp[Once run_block_def, result_equiv_def, state_equiv_refl]
  ) >>
  (* Error case - prove directly by case analysis *)
  simp[Once run_block_def] >>
  fs[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[AllCaseEqs()]
  >- (
    (* NONE case: transform_block preserves instruction count *)
    `get_instruction (transform_block graph bb) s.vs_inst_idx = NONE` by
      fs[get_instruction_def, transform_block_def] >>
    simp[result_equiv_def]
  ) >>
  (* SOME x case: need to show transform_inst graph x also errors *)
  `get_instruction (transform_block graph bb) s.vs_inst_idx = SOME (transform_inst graph x)` by (
    fs[get_instruction_def, transform_block_def] >>
    Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> gvs[] >>
    simp[EL_MAP]
  ) >>
  simp[] >>
  (* First handle ~is_phi_inst: transform is identity, same error *)
  reverse (Cases_on `is_phi_inst x`) >> gvs[]
  >- (
    `phi_single_origin graph x = NONE` by (
      CCONTR_TAC >> fs[] >>
      Cases_on `phi_single_origin graph x` >> gvs[] >>
      imp_res_tac phi_single_origin_is_phi
    ) >>
    gvs[transform_inst_def, result_equiv_def]
  ) >>
  (* is_phi_inst x: need detailed case analysis *)
  gvs[transform_inst_def] >>
  Cases_on `phi_single_origin graph x` >> gvs[result_equiv_def] >>
  (* SOME origin case *)
  Cases_on `x'.inst_outputs` >> gvs[result_equiv_def] >>
  Cases_on `t`
  >| [
    (* [h]: transform to ASSIGN [Var h] *)
    gvs[] >>  (* First simplify with t = [] giving x'.inst_outputs = [h] *)
    Cases_on `step_inst (x with <| inst_opcode := ASSIGN; inst_operands := [Var h] |>) s`
    (* 4 subcases: OK, Halt, Revert, Error *)
    >| [
      (* OK case: derive contradiction - ASSIGN succeeds means lookup_var h is SOME,
         but hypothesis says PHI erroring means lookup_var h is NONE *)
      simp[is_terminator_def] >>
      Cases_on `s.vs_prev_bb` >> gvs[result_equiv_def] >>
      (* Get lookup_var h s = NONE from Error hypothesis using drule_all *)
      first_x_assum drule_all >> strip_tac >>
      (* Now we have lookup_var h s = NONE, unfold step_inst to show contradiction *)
      qpat_x_assum `step_inst _ s = OK _` mp_tac >>
      simp[step_inst_def, eval_operand_def] >>
      gvs[AllCaseEqs()],
      (* Halt case: impossible for ASSIGN *)
      qpat_x_assum `step_inst _ _ = Halt _` mp_tac >> simp[step_inst_def] >> gvs[AllCaseEqs()],
      (* Revert case: impossible for ASSIGN *)
      qpat_x_assum `step_inst _ _ = Revert _` mp_tac >> simp[step_inst_def] >> gvs[AllCaseEqs()],
      (* Error case *)
      simp[result_equiv_def]
    ],
    (* h::h'::t': transform = identity *)
    simp[result_equiv_def]
  ]
QED
