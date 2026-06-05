(* Phase 3 SSA: output-variable distinctness for ao_transform_block.
 *
 * TOP-LEVEL:
 *   ao_phase3_preserves_ssa — ssa_form preserved by the phase-3 rewrite,
 *     given the original outputs avoid the fresh-var namespace
 *     (ao_fn_fresh_vars) and the original instruction ids are distinct.
 *
 * Strategy (mirrors phase-3 id distinctness): every transformed instruction
 * keeps its original outputs exactly once (these avoid ao_fn_fresh_vars);
 * helper instructions get fresh outputs ao_fresh_var (original id) s for
 * s in {not, iz, xor}, injective in (id, s). Split the flattened output
 * list into the part inside ao_fn_fresh_vars (fresh, distinct via id
 * distinctness) and the part outside (the original SSA outputs, distinct
 * via ssa_form).
 *)

Theory aoPhase3Ssa
Ancestors
  algebraicOptDefs aoPhase3Wf venomInst venomWf passSimulationDefs
  passSimulationProps passSharedDefs indexedLists rich_list string ASCIInumbers
Libs
  pairLib BasicProvers

(* ===== fresh-var injectivity ===== *)

Triviality ao_fresh_var_full_inj[local]:
  !id1 s1 id2 s2.
    (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
    (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
    ao_fresh_var id1 s1 = ao_fresh_var id2 s2 ==>
    id1 = id2 /\ s1 = s2
Proof
  rpt strip_tac >> gvs[] >>
  fs[ao_fresh_var_def, stringTheory.STRCAT_11,
     ASCIInumbersTheory.toString_inj]
QED

(* ===== fresh-var membership in ao_fn_fresh_vars ===== *)

Triviality fresh_mem[local]:
  !g id s. MEM id (MAP (\i. i.inst_id) (fn_insts g)) /\
    (s = "not" \/ s = "iz" \/ s = "xor") ==>
    ao_fresh_var id s IN ao_fn_fresh_vars g
Proof
  rw[ao_fn_fresh_vars_def] >> qexists_tac `id` >> rw[]
QED

(* ===== outok: the per-instruction SSA invariant ===== *)

Definition outok_def:
  outok fv id origs (outs:string list) <=>
    FILTER (\v. ~(v IN fv)) outs = origs /\
    ALL_DISTINCT (FILTER (\v. v IN fv) outs) /\
    (!x. MEM x outs /\ x IN fv ==>
         ?s. (s = "not" \/ s = "iz" \/ s = "xor") /\ x = ao_fresh_var id s)
End

(* clean instruction: no fresh outputs *)
Triviality outok_clean[local]:
  !fv id origs.
    EVERY (\v. ~(v IN fv)) origs ==> outok fv id origs origs
Proof
  rw[outok_def]
  >- (simp[listTheory.FILTER_EQ_ID] >> fs[listTheory.EVERY_MEM])
  >- (`FILTER (\v. v IN fv) origs = []` suffices_by simp[] >>
      simp[listTheory.FILTER_EQ_NIL] >> fs[listTheory.EVERY_MEM])
  >- (fs[listTheory.EVERY_MEM] >> metis_tac[])
QED

(* instruction with a fresh prefix followed by clean outputs *)

(* single fresh output prepended *)
Triviality outok_one_fresh[local]:
  !g id origs s.
    (s = "not" \/ s = "iz" \/ s = "xor") /\
    MEM id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\w. ~(w IN ao_fn_fresh_vars g)) origs ==>
    outok (ao_fn_fresh_vars g) id origs (ao_fresh_var id s :: origs)
Proof
  rpt strip_tac >>
  `ao_fresh_var id s IN ao_fn_fresh_vars g` by (irule fresh_mem >> simp[]) >>
  `!y. MEM y origs ==> ~(y IN ao_fn_fresh_vars g)` by fs[listTheory.EVERY_MEM] >>
  `FILTER (\v. ~(v IN ao_fn_fresh_vars g)) origs = origs` by
    (simp[listTheory.FILTER_EQ_ID] >> fs[]) >>
  `FILTER (\v. v IN ao_fn_fresh_vars g) origs = []` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[]) >>
  gvs[outok_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* two distinct fresh outputs prepended *)
Triviality outok_two_fresh[local]:
  !g id origs s1 s2.
    (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
    (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\ s1 <> s2 /\
    MEM id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\w. ~(w IN ao_fn_fresh_vars g)) origs ==>
    outok (ao_fn_fresh_vars g) id origs
      (ao_fresh_var id s1 :: ao_fresh_var id s2 :: origs)
Proof
  rpt strip_tac >>
  `ao_fresh_var id s1 IN ao_fn_fresh_vars g` by (irule fresh_mem >> simp[]) >>
  `ao_fresh_var id s2 IN ao_fn_fresh_vars g` by (irule fresh_mem >> simp[]) >>
  `ao_fresh_var id s1 <> ao_fresh_var id s2` by
    metis_tac[ao_fresh_var_full_inj] >>
  `!y. MEM y origs ==> ~(y IN ao_fn_fresh_vars g)` by fs[listTheory.EVERY_MEM] >>
  `FILTER (\v. ~(v IN ao_fn_fresh_vars g)) origs = origs` by
    (simp[listTheory.FILTER_EQ_ID] >> fs[]) >>
  `FILTER (\v. v IN ao_fn_fresh_vars g) origs = []` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[]) >>
  gvs[outok_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ===== output preservation for resolve / flips ===== *)

Triviality resolve_id[local]:
  !targets inst. (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality resolve_outputs[local]:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality pre_flip_id[local]:
  !inst. (ao_pre_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality pre_flip_outputs[local]:
  !inst. (ao_pre_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_outputs[local]:
  !inst. (ao_post_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_last_outputs[local]:
  !l. FLAT (MAP (\i. i.inst_outputs) (ao_post_flip_last l)) =
      FLAT (MAP (\i. i.inst_outputs) l)
Proof
  ho_match_mp_tac ao_post_flip_last_ind >>
  rw[ao_post_flip_last_def, post_flip_outputs]
QED

(* ===== output lists for each per-opcode helper ===== *)

(* simple opts: single output-preserving instruction *)
Triviality opt_shift_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_shift inst)) = inst.inst_outputs
Proof
  rw[ao_opt_shift_def] >> every_case_tac >> gvs[]
QED

Triviality opt_signextend_outs[local]:
  !ra lbl idx inst.
    FLAT (MAP (\i. i.inst_outputs) (ao_opt_signextend ra lbl idx inst)) =
    inst.inst_outputs
Proof
  rw[ao_opt_signextend_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_exp_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_exp inst)) = inst.inst_outputs
Proof
  rw[ao_opt_exp_def] >> every_case_tac >> gvs[]
QED

Triviality opt_addsub_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_addsub inst)) = inst.inst_outputs
Proof
  rw[ao_opt_addsub_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_and_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_and inst)) = inst.inst_outputs
Proof
  rw[ao_opt_and_def] >> every_case_tac >> gvs[]
QED

Triviality opt_muldiv_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_muldiv inst)) = inst.inst_outputs
Proof
  rw[ao_opt_muldiv_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_or_outs[local]:
  !dfg inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_or dfg inst)) =
    inst.inst_outputs
Proof
  rw[ao_opt_or_def] >> every_case_tac >> gvs[]
QED

(* eq: branches that introduce a single fresh helper ("not" or "xor") *)
Triviality opt_eq_outok[local]:
  !g mid dfg inst.
    MEM inst.inst_id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs) (ao_opt_eq mid dfg inst)))
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >> gvs[] >>
  TRY (irule outok_clean >> fs[] >> NO_TAC) >>
  FIRST [
    (irule outok_one_fresh >> simp[] >> qexists_tac `g` >> fs[]),
    (irule outok_one_fresh >> simp[] >> qexists_tac `g` >> fs[])
  ]
QED

(* comparator helpers *)
Triviality cmp_prefer_iz_zero_outok[local]:
  !g mid id op1 inst.
    inst.inst_id = id /\ MEM id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs) (ao_cmp_prefer_iz_zero mid id op1 inst)))
Proof
  rw[ao_cmp_prefer_iz_zero_def] >>
  irule outok_one_fresh >> simp[] >> qexists_tac `g` >> fs[]
QED

Triviality cmp_prefer_iz_max_outok[local]:
  !g mid id op1 inst.
    inst.inst_id = id /\ MEM id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs) (ao_cmp_prefer_iz_max mid id op1 inst)))
Proof
  rw[ao_cmp_prefer_iz_max_def] >>
  irule outok_two_fresh >> simp[] >> qexists_tac `g` >> fs[]
QED

Triviality cmp_prefer_iz_general_outok[local]:
  !g mid id op1 op2 inst.
    inst.inst_id = id /\ MEM id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_cmp_prefer_iz_general mid id op1 op2 inst)))
Proof
  rw[ao_cmp_prefer_iz_general_def] >>
  irule outok_two_fresh >> simp[] >> qexists_tac `g` >> fs[]
QED

Triviality opt_comparator_outok[local]:
  !g mid dfg ra lbl idx inst.
    MEM inst.inst_id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_opt_comparator mid dfg ra lbl idx inst)))
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  TRY (irule outok_clean >> fs[] >> NO_TAC) >>
  FIRST [
    (irule cmp_prefer_iz_zero_outok >> fs[]),
    (irule cmp_prefer_iz_max_outok >> fs[]),
    (irule cmp_prefer_iz_general_outok >> fs[]),
    (irule outok_one_fresh >> simp[] >> qexists_tac `g` >> fs[])
  ]
QED

(* ===== peephole and transform_inst ===== *)

Triviality peephole_outok[local]:
  !g mid dfg ra lbl idx inst.
    MEM inst.inst_id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_peephole_inst mid dfg ra lbl idx inst)))
Proof
  rpt strip_tac >>
  rw[ao_peephole_inst_def] >>
  simp[opt_shift_outs, opt_signextend_outs, opt_exp_outs, opt_addsub_outs,
       opt_and_outs, opt_muldiv_outs, opt_or_outs] >>
  TRY (irule outok_clean >> fs[] >> NO_TAC) >>
  FIRST [
    (irule opt_eq_outok >> fs[] >> qexists_tac `g` >> fs[]),
    (irule opt_comparator_outok >> fs[] >> qexists_tac `g` >> fs[])
  ]
QED

Triviality producer_outs[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r ==>
    FLAT (MAP (\i. i.inst_outputs) r) = inst.inst_outputs
Proof
  rw[ao_opt_producer_def] >> every_case_tac >> gvs[]
QED

Triviality transform_inst_outok[local]:
  !g mid dfg ra lbl idx targets inst.
    MEM inst.inst_id (MAP (\i. i.inst_id) (fn_insts g)) /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_transform_inst mid dfg ra lbl idx targets inst)))
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM, post_flip_last_outputs] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >>
       simp[post_flip_last_outputs, resolve_outputs]) >>
  TRY (irule outok_clean >> simp[resolve_outputs] >> fs[] >> NO_TAC) >>
  FIRST [
    (drule producer_outs >> strip_tac >>
     gvs[post_flip_last_outputs, resolve_outputs] >>
     irule outok_clean >> fs[]),
    (qspecl_then [`g`, `mid`, `dfg`, `ra`, `lbl`, `idx`,
       `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
       mp_tac peephole_outok >>
     impl_tac
     >- (gvs[pre_flip_id, resolve_id, pre_flip_outputs, resolve_outputs])
     >- simp[pre_flip_id, resolve_id, pre_flip_outputs, resolve_outputs,
             post_flip_last_outputs])
  ]
QED

(* ===== cmpok: comparator pieces are clean originals =====
   Phase 3 never creates or flips comparators (pre/post-flip only act on
   ADD/MUL/AND/OR/XOR/EQ).  So any comparator piece is an unchanged original
   instruction (id = base) whose whole expansion produces only clean outputs
   (no fresh vars).  This is what lets phase 4's inserted fresh "iz" var
   (named after a comparator id) avoid colliding with phase-3 outputs. *)

Definition cmpok_def:
  cmpok fv base (pieces:instruction list) <=>
    (!p. MEM p pieces /\ is_comparator p.inst_opcode ==> p.inst_id = base) /\
    ((?p. MEM p pieces /\ is_comparator p.inst_opcode) ==>
       EVERY (\v. v NOTIN fv) (FLAT (MAP (\q. q.inst_outputs) pieces)))
End

Triviality cmpok_no_comp[local]:
  !fv base l. (!p. MEM p l ==> ~is_comparator p.inst_opcode) ==> cmpok fv base l
Proof
  rw[cmpok_def] >> metis_tac[]
QED

Triviality cmpok_single_clean[local]:
  !fv base i.
    i.inst_id = base /\ EVERY (\v. v NOTIN fv) i.inst_outputs ==>
    cmpok fv base [i]
Proof
  rw[cmpok_def] >> gvs[]
QED

Triviality post_flip_opcode[local]:
  !inst. (ao_post_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_id[local]:
  !inst. (ao_post_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_operand_mem[local]:
  !x inst. MEM x (ao_post_flip_inst inst).inst_operands ==> MEM x inst.inst_operands
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

(* Fix B: every member of ao_post_flip_last l is either an original element or
   the post-flip of one; either way it has the same opcode/id and its operands
   are a subset (post_flip only swaps operands). *)
Triviality post_flip_last_mem[local]:
  !l p. MEM p (ao_post_flip_last l) ==>
        ?q. MEM q l /\ p.inst_opcode = q.inst_opcode /\
            p.inst_id = q.inst_id /\
            (!x. MEM x p.inst_operands ==> MEM x q.inst_operands)
Proof
  ho_match_mp_tac ao_post_flip_last_ind >> rpt conj_tac
  >- rw[ao_post_flip_last_def]
  >- (rw[ao_post_flip_last_def] >>
      gvs[post_flip_opcode, post_flip_id] >>
      metis_tac[post_flip_operand_mem])
  >- (rw[ao_post_flip_last_def] >> gvs[]
      >- (qexists_tac `inst` >> simp[])
      >- (first_x_assum drule >> strip_tac >> qexists_tac `q` >> simp[]))
QED

Triviality cmpok_post_flip_last[local]:
  !fv base l. cmpok fv base l ==> cmpok fv base (ao_post_flip_last l)
Proof
  rpt gen_tac >> simp[cmpok_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> drule post_flip_last_mem >> strip_tac >>
      gvs[] >> first_x_assum irule >> simp[])
  >> simp[post_flip_last_outputs] >> rpt strip_tac >>
     first_x_assum irule >>
     drule post_flip_last_mem >> strip_tac >> gvs[] >> metis_tac[]
QED

(* per-opt cmpok: single-piece opts stay clean originals;
   multi-piece opts (eq, comparator helpers) produce no comparators *)
Triviality opt_shift_cmpok[local]:
  !fv inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_shift inst)
Proof
  rw[ao_opt_shift_def] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_signextend_cmpok[local]:
  !fv ra lbl idx inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_signextend ra lbl idx inst)
Proof
  rw[ao_opt_signextend_def, LET_THM] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_exp_cmpok[local]:
  !fv inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_exp inst)
Proof
  rw[ao_opt_exp_def] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_addsub_cmpok[local]:
  !fv inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_addsub inst)
Proof
  rw[ao_opt_addsub_def, LET_THM] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_and_cmpok[local]:
  !fv inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_and inst)
Proof
  rw[ao_opt_and_def] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_muldiv_cmpok[local]:
  !fv inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_muldiv inst)
Proof
  rw[ao_opt_muldiv_def, LET_THM] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_or_cmpok[local]:
  !fv dfg inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_or dfg inst)
Proof
  rw[ao_opt_or_def] >> every_case_tac >> gvs[] >>
  irule cmpok_single_clean >> gvs[]
QED

Triviality opt_eq_cmpok[local]:
  !fv mid dfg inst. EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_eq mid dfg inst)
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >> gvs[] >>
  TRY (irule cmpok_single_clean >> gvs[] >> NO_TAC) >>
  irule cmpok_no_comp >> rw[] >> gvs[is_comparator_def]
QED

Triviality cmp_prefer_iz_zero_cmpok[local]:
  !fv mid id op1 inst. cmpok fv id (ao_cmp_prefer_iz_zero mid id op1 inst)
Proof
  rw[ao_cmp_prefer_iz_zero_def] >> irule cmpok_no_comp >> rw[] >>
  gvs[is_comparator_def]
QED

Triviality cmp_prefer_iz_max_cmpok[local]:
  !fv mid id op1 inst. cmpok fv id (ao_cmp_prefer_iz_max mid id op1 inst)
Proof
  rw[ao_cmp_prefer_iz_max_def] >> irule cmpok_no_comp >> rw[] >>
  gvs[is_comparator_def]
QED

Triviality cmp_prefer_iz_general_cmpok[local]:
  !fv mid id op1 op2 inst.
    cmpok fv id (ao_cmp_prefer_iz_general mid id op1 op2 inst)
Proof
  rw[ao_cmp_prefer_iz_general_def] >> irule cmpok_no_comp >> rw[] >>
  gvs[is_comparator_def]
QED

Triviality opt_comparator_cmpok[local]:
  !fv mid dfg ra lbl idx inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  TRY (irule cmpok_single_clean >> gvs[] >> NO_TAC) >>
  FIRST [
    (irule cmp_prefer_iz_zero_cmpok),
    (irule cmp_prefer_iz_max_cmpok),
    (irule cmp_prefer_iz_general_cmpok),
    (irule cmpok_no_comp >> rw[] >> gvs[is_comparator_def])
  ]
QED

Triviality peephole_cmpok[local]:
  !fv mid dfg ra lbl idx inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  rw[ao_peephole_inst_def] >>
  TRY (irule cmpok_single_clean >> gvs[] >> NO_TAC) >>
  FIRST [
    irule opt_shift_cmpok >> gvs[],
    irule opt_signextend_cmpok >> gvs[],
    irule opt_exp_cmpok >> gvs[],
    irule opt_addsub_cmpok >> gvs[],
    irule opt_and_cmpok >> gvs[],
    irule opt_muldiv_cmpok >> gvs[],
    irule opt_or_cmpok >> gvs[],
    irule opt_eq_cmpok >> gvs[],
    irule opt_comparator_cmpok >> gvs[]
  ]
QED

Triviality producer_no_comp[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r ==>
    EVERY (\p. ~is_comparator p.inst_opcode) r
Proof
  rw[ao_opt_producer_def] >> every_case_tac >>
  gvs[is_comparator_def]
QED

Triviality transform_inst_cmpok[local]:
  !fv mid dfg ra lbl idx targets inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    cmpok fv inst.inst_id
      (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >> simp[resolve_id, resolve_outputs]) >>
  TRY (irule cmpok_single_clean >> simp[resolve_id, resolve_outputs] >>
       gvs[] >> NO_TAC) >>
  FIRST [
    (irule cmpok_post_flip_last >> irule cmpok_no_comp >> rpt strip_tac >>
     drule producer_no_comp >> strip_tac >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]),
    (irule cmpok_post_flip_last >>
     qspecl_then [`fv`, `mid`, `dfg`, `ra`, `lbl`, `idx`,
       `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
       mp_tac peephole_cmpok >>
     impl_tac
     >- gvs[pre_flip_outputs, resolve_outputs]
     >> simp[pre_flip_id, resolve_id])
  ]
QED

(* ===== pieces: distinctness over a flattened list of transformed insts ===== *)

(* clean part: outputs outside fv recover the original output lists *)
Triviality pieces_clean[local]:
  !fv pieces.
    EVERY (\p. outok fv (FST p) (FST (SND p)) (SND (SND p))) pieces ==>
    FILTER (\v. ~(v IN fv)) (FLAT (MAP (\p. SND (SND p)) pieces)) =
    FLAT (MAP (\p. FST (SND p)) pieces)
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.FILTER_APPEND_DISTRIB] >>
  fs[outok_def]
QED

(* fresh part: every fresh output is ao_fresh_var (some piece id) s *)
Triviality pieces_fresh_mem[local]:
  !fv pieces y.
    EVERY (\p. outok fv (FST p) (FST (SND p)) (SND (SND p))) pieces /\
    MEM y (FILTER (\v. v IN fv) (FLAT (MAP (\p. SND (SND p)) pieces))) ==>
    ?b s. MEM b (MAP FST pieces) /\
          (s = "not" \/ s = "iz" \/ s = "xor") /\ y = ao_fresh_var b s
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.FILTER_APPEND_DISTRIB, listTheory.MEM_FILTER] >> gvs[]
  >- (fs[outok_def] >> res_tac >> metis_tac[])
  >- (first_x_assum drule >> simp[listTheory.MEM_FILTER] >>
      strip_tac >> metis_tac[])
QED

Triviality pieces_fresh_distinct[local]:
  !fv pieces.
    ALL_DISTINCT (MAP FST pieces) /\
    EVERY (\p. outok fv (FST p) (FST (SND p)) (SND (SND p))) pieces ==>
    ALL_DISTINCT
      (FILTER (\v. v IN fv) (FLAT (MAP (\p. SND (SND p)) pieces)))
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.MAP, listTheory.FLAT] >>
  PURE_REWRITE_TAC[listTheory.FILTER_APPEND_DISTRIB,
    listTheory.ALL_DISTINCT_APPEND] >>
  rpt conj_tac
  >- fs[outok_def]
  >- (first_x_assum irule >> fs[])
  >- (rpt strip_tac >>
      rename1 `MEM y (FILTER _ h2)` >>
      `MEM y h2 /\ y IN fv` by
        (qpat_x_assum `MEM y (FILTER _ h2)` mp_tac >>
         simp[listTheory.MEM_FILTER]) >>
      `?s1. (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
            y = ao_fresh_var h0 s1` by
        (fs[outok_def] >> metis_tac[]) >>
      `?b s2. MEM b (MAP FST pieces) /\
              (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
              y = ao_fresh_var b s2` by
        (irule pieces_fresh_mem >> fs[] >> metis_tac[]) >>
      gvs[] >>
      `h0 = b` by metis_tac[ao_fresh_var_full_inj] >>
      gvs[])
QED

(* ===== MAPi fusion ===== *)

Triviality mapi_no_index[local]:
  !l (f:'a -> 'b). MAPi (\i x. f x) l = MAP f l
Proof
  Induct >> simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF]
QED

Triviality map_mapi[local]:
  !l (h:'b -> 'c) (g:num -> 'a -> 'b).
    MAP h (MAPi g l) = MAPi (\i x. h (g i x)) l
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`h`, `g o SUC`] mp_tac) >>
  simp[combinTheory.o_DEF]
QED

Triviality flat_map_flat_mapi[local]:
  !l (f:'b -> 'c list) (g:num -> 'a -> 'b list).
    FLAT (MAP f (FLAT (MAPi g l))) =
    FLAT (MAPi (\i x. FLAT (MAP f (g i x))) l)
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  simp[listTheory.MAP_FLAT, listTheory.FLAT_APPEND] >>
  first_x_assum (qspecl_then [`f`, `g o SUC`] mp_tac) >>
  simp[combinTheory.o_DEF, listTheory.MAP_FLAT]
QED

(* ===== block / function plumbing ===== *)

Definition block_outpieces_def:
  block_outpieces mid dfg ra targets bb =
    MAPi (\idx inst.
      (inst.inst_id, inst.inst_outputs,
       FLAT (MAP (\i. i.inst_outputs)
         (ao_transform_inst mid dfg ra bb.bb_label idx targets inst))))
      bb.bb_instructions
End

Triviality block_outpieces_fst[local]:
  !mid dfg ra targets bb.
    MAP FST (block_outpieces mid dfg ra targets bb) =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[block_outpieces_def, map_mapi, mapi_no_index] >> simp[ETA_AX]
QED

Triviality block_outpieces_fst_snd[local]:
  !mid dfg ra targets bb.
    MAP (\p. FST (SND p)) (block_outpieces mid dfg ra targets bb) =
    MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  rw[block_outpieces_def, map_mapi, mapi_no_index] >> simp[ETA_AX]
QED

(* ao_resolve_phis_block (the PHI post-pass in ao_transform_block) only
   rewrites PHI operands, so it preserves every instruction's outputs. *)
Triviality ao_resolve_phis_block_outputs[local]:
  MAP (\i. i.inst_outputs) (ao_resolve_phis_block targets bb).bb_instructions =
  MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  simp[ao_resolve_phis_block_def, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> rw[ao_resolve_iszero_inst_def]
QED

Triviality block_outpieces_snd_snd_flat[local]:
  !mid dfg ra targets bb.
    FLAT (MAP (\p. SND (SND p)) (block_outpieces mid dfg ra targets bb)) =
    FLAT (MAP (\i. i.inst_outputs)
      (ao_transform_block mid dfg ra targets bb).bb_instructions)
Proof
  rw[block_outpieces_def, ao_transform_block_def, map_mapi,
     flat_map_flat_mapi, ao_resolve_phis_block_outputs]
QED

Definition all_outpieces_def:
  all_outpieces mid dfg ra targets fn =
    FLAT (MAP (block_outpieces mid dfg ra targets) fn.fn_blocks)
End

Triviality all_outpieces_fst[local]:
  !mid dfg ra targets fn.
    MAP FST (all_outpieces mid dfg ra targets fn) =
    MAP (\i. i.inst_id) (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[all_outpieces_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def, block_outpieces_fst]
QED

Triviality all_outpieces_fst_snd[local]:
  !mid dfg ra targets fn.
    FLAT (MAP (\p. FST (SND p)) (all_outpieces mid dfg ra targets fn)) =
    FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))
Proof
  rpt gen_tac >>
  simp[all_outpieces_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[fn_insts_blocks_def, listTheory.FLAT_APPEND, block_outpieces_fst_snd]
QED

Triviality all_outpieces_snd_snd_flat[local]:
  !mid dfg ra targets fn.
    FLAT (MAP (\p. SND (SND p)) (all_outpieces mid dfg ra targets fn)) =
    FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
      (ao_transform_block mid dfg ra targets bb).bb_instructions))
      fn.fn_blocks)
Proof
  rpt gen_tac >>
  simp[all_outpieces_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[listTheory.FLAT_APPEND, block_outpieces_snd_snd_flat]
QED

(* mem_fn_insts_blocks shared from passSimulationProps *)

Triviality all_outpieces_outok[local]:
  !mid dfg ra targets fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    EVERY (\p. outok (ao_fn_fresh_vars fn) (FST p) (FST (SND p)) (SND (SND p)))
      (all_outpieces mid dfg ra targets fn)
Proof
  rw[all_outpieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_outpieces_def, indexedListsTheory.MEM_MAPi] >>
  qmatch_goalsub_abbrev_tac `ao_transform_inst _ _ _ _ _ _ inst` >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
     simp[listTheory.MEM_EL, Abbr`inst`] >> metis_tac[]) >>
  irule transform_inst_outok >>
  simp[listTheory.MEM_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> metis_tac[]
QED

(* ===== top-level ===== *)

Triviality map_inst_id_fn_insts[local]:
  !fn. MAP (\i. i.inst_id) (fn_insts fn) =
       FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)
Proof
  gen_tac >> simp[fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def]
QED

Triviality all_distinct_split_fv[local]:
  !(l:string list) fv.
    ALL_DISTINCT (FILTER (\v. v IN fv) l) /\
    ALL_DISTINCT (FILTER (\v. ~(v IN fv)) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h IN fv` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  qexists_tac `fv` >> simp[] >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

Triviality outpieces_all_distinct[local]:
  !fv pieces.
    ALL_DISTINCT (MAP FST pieces) /\
    ALL_DISTINCT (FLAT (MAP (\p. FST (SND p)) pieces)) /\
    EVERY (\p. outok fv (FST p) (FST (SND p)) (SND (SND p))) pieces ==>
    ALL_DISTINCT (FLAT (MAP (\p. SND (SND p)) pieces))
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FILTER (\v. v IN fv) (FLAT (MAP (\p. SND (SND p)) pieces)))`
    by metis_tac[pieces_fresh_distinct] >>
  `FILTER (\v. ~(v IN fv)) (FLAT (MAP (\p. SND (SND p)) pieces)) =
     FLAT (MAP (\p. FST (SND p)) pieces)`
    by metis_tac[pieces_clean] >>
  metis_tac[all_distinct_split_fv]
QED

Theorem ao_phase3_preserves_ssa:
  !mid dfg ra targets fn.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    ssa_form
      (function_map_transform (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt strip_tac >>
  simp[ssa_form_def] >>
  `FLAT (MAP (\i. i.inst_outputs)
     (fn_insts (function_map_transform
        (ao_transform_block mid dfg ra targets) fn))) =
   FLAT (MAP (\p. SND (SND p)) (all_outpieces mid dfg ra targets fn))` by
    (simp[Once function_map_transform_def] >>
     simp[fn_insts_def, listTheory.MAP_FLAT, listTheory.MAP_MAP_o,
          combinTheory.o_DEF, all_outpieces_snd_snd_flat] >>
     qspec_tac (`fn.fn_blocks`,`bbs`) >>
     Induct >>
     simp[fn_insts_blocks_def, listTheory.FLAT_APPEND, listTheory.MAP_FLAT,
          listTheory.MAP_MAP_o, combinTheory.o_DEF]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`ao_fn_fresh_vars fn`, `all_outpieces mid dfg ra targets fn`]
    mp_tac outpieces_all_distinct >>
  impl_tac
  >- (rpt conj_tac
      >- (simp[all_outpieces_fst, map_inst_id_fn_insts] >>
          fs[fn_inst_ids_distinct_def])
      >- (simp[all_outpieces_fst_snd] >> fs[ssa_form_def])
      >- (irule all_outpieces_outok >> rpt strip_tac >> metis_tac[])) >>
  simp[]
QED

(* ===== no_cmp_iz: phase-4's inserted fresh "iz" vars avoid phase-3 outputs ===== *)

(* The M2 PHI iszero-resolution post-pass only rewrites PHI operands, so it
   preserves opcode/id/outputs of every instruction.  These let the cmpiece
   plumbing carry the resolved instructions (= the actual transformed block)
   while the cmpok/outok reasoning reduces to the pre-resolution form. *)
Triviality resolve_phi_inst_opcode[local]:
  !targets i.
    (if i.inst_opcode = PHI then ao_resolve_iszero_inst targets i else i).inst_opcode =
    i.inst_opcode
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality resolve_phi_inst_id[local]:
  !targets i.
    (if i.inst_opcode = PHI then ao_resolve_iszero_inst targets i else i).inst_id =
    i.inst_id
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality resolve_phi_inst_outputs[local]:
  !targets i.
    (if i.inst_opcode = PHI then ao_resolve_iszero_inst targets i else i).inst_outputs =
    i.inst_outputs
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality map_resolve_phi_outputs[local]:
  !targets l.
    FLAT (MAP (\i. i.inst_outputs)
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)) =
    FLAT (MAP (\i. i.inst_outputs) l)
Proof
  Induct_on `l` >> simp[resolve_phi_inst_outputs]
QED

Triviality cmpok_map_resolve[local]:
  !targets fv base l.
    cmpok fv base l ==>
    cmpok fv base
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)
Proof
  rpt gen_tac >> simp[cmpok_def] >> strip_tac >> conj_tac
  >- (rw[listTheory.MEM_MAP] >>
      gvs[resolve_phi_inst_opcode, resolve_phi_inst_id] >>
      first_x_assum irule >> simp[])
  >> simp[map_resolve_phi_outputs] >> strip_tac >>
     first_x_assum irule >>
     gvs[listTheory.MEM_MAP, resolve_phi_inst_opcode] >>
     metis_tac[resolve_phi_inst_opcode]
QED

(* pieces carrying the transformed instruction list (not just outputs);
   PHI pieces carry the resolved instruction so the FLAT equals the actual
   transformed block (see block_cmppieces_snd_snd_flat). *)
Definition block_cmppieces_def:
  block_cmppieces mid dfg ra targets bb =
    MAPi (\idx inst.
      (inst.inst_id, inst.inst_outputs,
       MAP (\i. if i.inst_opcode = PHI
                then ao_resolve_iszero_inst targets i else i)
         (ao_transform_inst mid dfg ra bb.bb_label idx targets inst)))
      bb.bb_instructions
End

Triviality block_cmppieces_fst[local]:
  !mid dfg ra targets bb.
    MAP FST (block_cmppieces mid dfg ra targets bb) =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[block_cmppieces_def, map_mapi, mapi_no_index] >> simp[ETA_AX]
QED

Triviality block_cmppieces_snd_snd_flat[local]:
  !mid dfg ra targets bb.
    FLAT (MAP (\p. SND (SND p)) (block_cmppieces mid dfg ra targets bb)) =
    (ao_transform_block mid dfg ra targets bb).bb_instructions
Proof
  rw[block_cmppieces_def, ao_transform_block_def, ao_resolve_phis_block_def,
     map_mapi, listTheory.MAP_FLAT] >>
  simp[combinTheory.o_DEF]
QED

Definition all_cmppieces_def:
  all_cmppieces mid dfg ra targets fn =
    FLAT (MAP (block_cmppieces mid dfg ra targets) fn.fn_blocks)
End

Triviality all_cmppieces_fst[local]:
  !mid dfg ra targets fn.
    MAP FST (all_cmppieces mid dfg ra targets fn) =
    MAP (\i. i.inst_id) (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[all_cmppieces_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def, block_cmppieces_fst]
QED

Triviality all_cmppieces_insts[local]:
  !mid dfg ra targets fn.
    fn_insts (function_map_transform (ao_transform_block mid dfg ra targets) fn) =
    FLAT (MAP (\p. SND (SND p)) (all_cmppieces mid dfg ra targets fn))
Proof
  rpt gen_tac >>
  simp[all_cmppieces_def, function_map_transform_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[fn_insts_blocks_def, listTheory.FLAT_APPEND,
       block_cmppieces_snd_snd_flat]
QED

Triviality all_cmppieces_cmpok[local]:
  !mid dfg ra targets fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    EVERY (\p. cmpok (ao_fn_fresh_vars fn) (FST p) (SND (SND p)))
      (all_cmppieces mid dfg ra targets fn)
Proof
  rw[all_cmppieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_cmppieces_def, indexedListsTheory.MEM_MAPi] >>
  qmatch_goalsub_abbrev_tac `ao_transform_inst _ _ _ _ _ _ inst` >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
     simp[listTheory.MEM_EL, Abbr`inst`] >> metis_tac[]) >>
  irule cmpok_map_resolve >>
  irule transform_inst_cmpok >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >> metis_tac[]
QED

Triviality all_cmppieces_outok[local]:
  !mid dfg ra targets fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    EVERY (\p. outok (ao_fn_fresh_vars fn) (FST p) (FST (SND p))
                (FLAT (MAP (\q. q.inst_outputs) (SND (SND p)))))
      (all_cmppieces mid dfg ra targets fn)
Proof
  rw[all_cmppieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_cmppieces_def, indexedListsTheory.MEM_MAPi] >>
  simp[map_resolve_phi_outputs] >>
  qmatch_goalsub_abbrev_tac `ao_transform_inst _ _ _ _ _ _ inst` >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
     simp[listTheory.MEM_EL, Abbr`inst`] >> metis_tac[]) >>
  irule transform_inst_outok >>
  simp[listTheory.MEM_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> metis_tac[]
QED

Triviality all_distinct_fst_inj[local]:
  !l x y.
    ALL_DISTINCT (MAP FST l) /\ MEM x l /\ MEM y l /\ FST x = FST y ==> x = y
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  metis_tac[]
QED

Triviality flat_outputs_flat[local]:
  !pieces.
    FLAT (MAP (\q. q.inst_outputs) (FLAT (MAP (\p. SND (SND p)) pieces))) =
    FLAT (MAP (\p. FLAT (MAP (\q. q.inst_outputs) (SND (SND p)))) pieces)
Proof
  Induct >> simp[listTheory.FLAT_APPEND]
QED

(* core list lemma: a comparator piece's id-based "iz" var is not an output *)
Triviality cmppieces_no_cmp_iz[local]:
  !fv pieces i0.
    ALL_DISTINCT (MAP FST pieces) /\
    EVERY (\p. cmpok fv (FST p) (SND (SND p))) pieces /\
    EVERY (\p. outok fv (FST p) (FST (SND p))
                (FLAT (MAP (\q. q.inst_outputs) (SND (SND p))))) pieces /\
    (!p. MEM p pieces ==> ao_fresh_var (FST p) "iz" IN fv) /\
    MEM i0 (FLAT (MAP (\p. SND (SND p)) pieces)) /\
    is_comparator i0.inst_opcode ==>
    ~MEM (ao_fresh_var i0.inst_id "iz")
         (FLAT (MAP (\q. q.inst_outputs)
            (FLAT (MAP (\p. SND (SND p)) pieces))))
Proof
  rpt strip_tac >>
  `?p0. MEM p0 pieces /\ MEM i0 (SND (SND p0))` by
    (qpat_x_assum `MEM i0 (FLAT _)` mp_tac >>
     simp[listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  `cmpok fv (FST p0) (SND (SND p0))` by
    (qpat_x_assum `EVERY (\p. cmpok _ _ _) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `i0.inst_id = FST p0` by (fs[cmpok_def] >> metis_tac[]) >>
  `?p1. MEM p1 pieces /\
        MEM (ao_fresh_var i0.inst_id "iz")
            (FLAT (MAP (\q. q.inst_outputs) (SND (SND p1))))` by
    (qpat_x_assum `MEM (ao_fresh_var _ _) (FLAT _)` mp_tac >>
     simp[flat_outputs_flat, listTheory.MEM_FLAT, listTheory.MEM_MAP,
          PULL_EXISTS] >> metis_tac[]) >>
  `ao_fresh_var i0.inst_id "iz" IN fv` by metis_tac[] >>
  `outok fv (FST p1) (FST (SND p1))
     (FLAT (MAP (\q. q.inst_outputs) (SND (SND p1))))` by
    (qpat_x_assum `EVERY (\p. outok _ _ _ _) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?s. (s = "not" \/ s = "iz" \/ s = "xor") /\
       ao_fresh_var i0.inst_id "iz" = ao_fresh_var (FST p1) s` by
    (fs[outok_def] >> metis_tac[]) >>
  `FST p0 = FST p1` by metis_tac[ao_fresh_var_full_inj] >>
  `p0 = p1` by metis_tac[all_distinct_fst_inj] >>
  `cmpok fv (FST p1) (SND (SND p1))` by
    (qpat_x_assum `EVERY (\p. cmpok _ _ _) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\v. v NOTIN fv)
     (FLAT (MAP (\q. q.inst_outputs) (SND (SND p1))))` by
    (fs[cmpok_def] >> first_x_assum irule >>
     qexists_tac `i0` >> metis_tac[]) >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ao_phase3_no_cmp_iz:
  !mid dfg ra targets fn c.
    fn_inst_ids_distinct fn /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (?i. MEM i (fn_insts (function_map_transform
                  (ao_transform_block mid dfg ra targets) fn)) /\
         i.inst_id = c /\ is_comparator i.inst_opcode) ==>
    ~MEM (ao_fresh_var c "iz")
       (FLAT (MAP (\i. i.inst_outputs)
         (fn_insts (function_map_transform
            (ao_transform_block mid dfg ra targets) fn))))
Proof
  rpt strip_tac >>
  qabbrev_tac `pieces = all_cmppieces mid dfg ra targets fn` >>
  `fn_insts (function_map_transform (ao_transform_block mid dfg ra targets) fn) =
   FLAT (MAP (\p. SND (SND p)) pieces)` by
    simp[Abbr `pieces`, all_cmppieces_insts] >>
  qpat_x_assum `i.inst_id = c` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `fn_insts _ = FLAT _` SUBST_ALL_TAC >>
  qspecl_then [`ao_fn_fresh_vars fn`, `pieces`, `i`]
    mp_tac cmppieces_no_cmp_iz >>
  impl_tac
  >- (rpt conj_tac
      >- (simp[Abbr `pieces`, all_cmppieces_fst, map_inst_id_fn_insts] >>
          fs[fn_inst_ids_distinct_def])
      >- (simp[Abbr `pieces`] >> irule all_cmppieces_cmpok >>
          rpt strip_tac >> metis_tac[])
      >- (simp[Abbr `pieces`] >> irule all_cmppieces_outok >>
          rpt strip_tac >> metis_tac[])
      >- (rpt strip_tac >>
          `MEM (FST p) (MAP FST pieces)` by
            (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
          `MAP FST pieces = MAP (\i. i.inst_id) (fn_insts fn)` by
            simp[Abbr `pieces`, all_cmppieces_fst] >>
          irule fresh_mem >> gvs[])
      >> gvs[]) >>
  simp[]
QED

(* ===== no_cmp_operand_iz: phase-3 never references, as an OPERAND, a fresh
   "iz" var named after a comparator that survives in fn1.  Operand-dual of
   ao_phase3_no_cmp_iz.  Needs the targets-chain entries to be clean because
   ao_resolve_iszero_op can substitute a chain entry for an operand. ===== *)

(* inok: every fresh-var OPERAND in the pieces is ao_fresh_var id s. *)
Definition inok_def:
  inok fv id (pieces:instruction list) <=>
    !q w. MEM q pieces /\ MEM (Var w) q.inst_operands /\ w IN fv ==>
          ?s. (s = "not" \/ s = "iz" \/ s = "xor") /\ w = ao_fresh_var id s
End

(* cmpinok: if the expansion contains a comparator, ALL its operands are clean.
   Mirrors cmpok (output side): a surviving comparator forces the whole piece to
   be a clean unchanged original, since phase 3 only keeps a comparator in the
   [inst] fall-through branch (every rewrite changes the opcode to ISZERO/etc). *)
Definition cmpinok_def:
  cmpinok fv (pieces:instruction list) <=>
    (?p. MEM p pieces /\ is_comparator p.inst_opcode) ==>
    !q w. MEM q pieces /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
End

(* ===== inok / cmpinok builders ===== *)

Triviality inok_clean[local]:
  !fv id l.
    (!q w. MEM q l /\ MEM (Var w) q.inst_operands ==> w NOTIN fv) ==>
    inok fv id l
Proof
  rw[inok_def] >> metis_tac[]
QED

Triviality cmpinok_no_comp[local]:
  !fv l. (!p. MEM p l ==> ~is_comparator p.inst_opcode) ==> cmpinok fv l
Proof
  rw[cmpinok_def] >> metis_tac[]
QED

Triviality cmpinok_clean[local]:
  !fv l.
    (!q w. MEM q l /\ MEM (Var w) q.inst_operands ==> w NOTIN fv) ==>
    cmpinok fv l
Proof
  rw[cmpinok_def] >> metis_tac[]
QED

(* A single instruction with clean operands satisfies both. *)

(* targets chain entries are operands/outputs of the source instructions. *)
Triviality iszero_step_acc[local]:
  !acc h (P:string->bool).
    (!ch w. MEM ch (MAP SND acc) /\ MEM (Var w) ch ==> P w) /\
    (!w. MEM (Var w) h.inst_operands ==> P w) /\
    (!w. MEM w h.inst_outputs ==> P w) ==>
    !ch w. MEM ch (MAP SND (ao_compute_iszero_step acc h)) /\
           MEM (Var w) ch ==> P w
Proof
  rw[ao_compute_iszero_step_def] >> every_case_tac >>
  gvs[listTheory.MEM_SNOC] >> TRY (metis_tac[]) >>
  rename1 `ALOOKUP acc vv = SOME chain` >>
  `MEM (vv, chain) acc` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `MEM chain (MAP SND acc)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `(vv, chain)` >> simp[]) >>
  metis_tac[]
QED

Triviality iszero_step_entries[local]:
  !insts acc (P:string->bool).
    (!ch w. MEM ch (MAP SND acc) /\ MEM (Var w) ch ==> P w) /\
    (!inst w. MEM inst insts /\
       (MEM (Var w) inst.inst_operands \/ MEM w inst.inst_outputs) ==> P w) ==>
    !ch w. MEM ch (MAP SND (FOLDL ao_compute_iszero_step acc insts)) /\
           MEM (Var w) ch ==> P w
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`ao_compute_iszero_step acc h`, `P`] mp_tac) >>
  impl_tac >- (
    conj_tac
    >- (qspecl_then [`acc`, `h`, `P`] mp_tac iszero_step_acc >>
        impl_tac >- (rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
        simp[])
    >- (rpt strip_tac >> metis_tac[])) >>
  simp[]
QED

(* resolve substitutes either the original operand or a chain entry. *)
Triviality resolve_op_cases[local]:
  !targets opc op.
    ao_resolve_iszero_op targets opc op = op \/
    ?vv chain. op = Var vv /\ ALOOKUP targets vv = SOME chain /\
               MEM (ao_resolve_iszero_op targets opc op) chain
Proof
  rpt gen_tac >> Cases_on `op` >>
  PURE_REWRITE_TAC[ao_resolve_iszero_op_def] >> simp[] >>
  Cases_on `ALOOKUP targets s` >> simp[] >>
  rename1 `ALOOKUP targets s = SOME chain` >>
  IF_CASES_TAC >> simp[] >>
  simp[LET_THM] >>
  IF_CASES_TAC
  >- (DISJ2_TAC >> irule listTheory.EL_MEM >> fs[]) >>
  simp[]
QED

Triviality resolve_op_clean[local]:
  !targets opc op fv.
    (!w. op = Var w ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    !w. ao_resolve_iszero_op targets opc op = Var w ==> w NOTIN fv
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  qspecl_then [`targets`, `opc`, `op`] strip_assume_tac resolve_op_cases
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `MEM chain (MAP SND targets)` by
    (drule alistTheory.ALOOKUP_MEM >> rw[listTheory.MEM_MAP] >>
     qexists_tac `(vv, chain)` >> simp[]) >>
  metis_tac[]
QED

Triviality resolve_inst_opnds_clean[local]:
  !targets inst fv.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    !w. MEM (Var w) (ao_resolve_iszero_inst targets inst).inst_operands ==>
        w NOTIN fv
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_resolve_iszero_inst_def, listTheory.MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `Var w = ao_resolve_iszero_op targets inst.inst_opcode op` >>
  qspecl_then [`targets`, `inst.inst_opcode`, `op`, `fv`] mp_tac
    resolve_op_clean >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> gvs[] >> metis_tac[])
      >- first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

(* ===== flip operand membership / map preservation ===== *)

Triviality pre_flip_operand_mem[local]:
  !x inst. MEM x (ao_pre_flip_inst inst).inst_operands ==> MEM x inst.inst_operands
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality inok_post_flip_last[local]:
  !fv id l. inok fv id l ==> inok fv id (ao_post_flip_last l)
Proof
  rw[inok_def] >>
  drule post_flip_last_mem >> strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Triviality cmpinok_post_flip_last[local]:
  !fv l. cmpinok fv l ==> cmpinok fv (ao_post_flip_last l)
Proof
  rw[cmpinok_def] >>
  imp_res_tac post_flip_last_mem >> metis_tac[]
QED

(* ===== per-opt operand cleanliness (simple opts) ===== *)

Triviality opt_shift_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_shift inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_shift_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_signextend_opnds_clean[local]:
  !fv ra lbl idx inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_signextend ra lbl idx inst) /\
          MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_signextend_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_exp_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_exp inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_exp_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_addsub_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_addsub inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_addsub_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_and_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_and inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_and_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_muldiv_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_muldiv inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_muldiv_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_or_opnds_clean[local]:
  !fv dfg inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_or dfg inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_or_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

(* ===== eq / comparator inok & cmpinok ===== *)

Triviality cmp_range_lit[local]:
  !ra lbl idx inst is_gt signed r.
    ao_opt_cmp_range ra lbl idx inst is_gt signed = SOME r ==> ?w. r = Lit w
Proof
  rw[ao_opt_cmp_range_def, LET_THM] >> every_case_tac >> gvs[]
QED

(* structural: every Var-operand of the eq expansion is either an original
   operand or one of the named fresh helpers ("not"/"xor"). *)
Triviality opt_eq_opnds[local]:
  !mid dfg inst q w.
    MEM q (ao_opt_eq mid dfg inst) /\ MEM (Var w) q.inst_operands ==>
    MEM (Var w) inst.inst_operands \/
    w = ao_fresh_var inst.inst_id "not" \/
    w = ao_fresh_var inst.inst_id "xor"
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_eq_inok[local]:
  !fv mid dfg inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    inok fv inst.inst_id (ao_opt_eq mid dfg inst)
Proof
  rw[inok_def] >>
  `MEM (Var w) inst.inst_operands \/
   w = ao_fresh_var inst.inst_id "not" \/
   w = ao_fresh_var inst.inst_id "xor"` by
    (irule opt_eq_opnds >> metis_tac[]) >>
  pop_assum strip_assume_tac
  >- metis_tac[]
  >- (qexists_tac `"not"` >> simp[])
  >- (qexists_tac `"xor"` >> simp[])
QED

Triviality opt_eq_cmpinok[local]:
  !fv mid dfg inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    cmpinok fv (ao_opt_eq mid dfg inst)
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >> gvs[] >>
  TRY (irule cmpinok_no_comp >> rw[] >> gvs[is_comparator_def] >> NO_TAC) >>
  irule cmpinok_clean >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Triviality cmp_prefer_iz_zero_cmpinok[local]:
  !fv mid id op1 inst. cmpinok fv (ao_cmp_prefer_iz_zero mid id op1 inst)
Proof
  rw[ao_cmp_prefer_iz_zero_def] >> irule cmpinok_no_comp >> rw[] >>
  gvs[is_comparator_def]
QED

Triviality cmp_prefer_iz_max_cmpinok[local]:
  !fv mid id op1 inst. cmpinok fv (ao_cmp_prefer_iz_max mid id op1 inst)
Proof
  rw[ao_cmp_prefer_iz_max_def] >> irule cmpinok_no_comp >> rw[] >>
  gvs[is_comparator_def]
QED

Triviality cmp_prefer_iz_general_cmpinok[local]:
  !fv mid id op1 op2 inst.
    cmpinok fv (ao_cmp_prefer_iz_general mid id op1 op2 inst)
Proof
  rw[ao_cmp_prefer_iz_general_def] >> irule cmpinok_no_comp >> rw[] >>
  gvs[is_comparator_def]
QED

(* inok builder: every Var-operand is clean or one of the named fresh helpers. *)
Triviality inok_named[local]:
  !fv id l.
    (!q w. MEM q l /\ MEM (Var w) q.inst_operands ==>
       w NOTIN fv \/ w = ao_fresh_var id "not" \/
       w = ao_fresh_var id "iz" \/ w = ao_fresh_var id "xor") ==>
    inok fv id l
Proof
  rw[inok_def] >>
  `w NOTIN fv \/ w = ao_fresh_var id "not" \/ w = ao_fresh_var id "iz" \/
   w = ao_fresh_var id "xor"` by metis_tac[] >>
  pop_assum strip_assume_tac >> gvs[] >> metis_tac[]
QED

Triviality cmp_prefer_iz_zero_inok[local]:
  !fv mid id op1 inst.
    (!w. op1 = Var w ==> w NOTIN fv) ==>
    inok fv id (ao_cmp_prefer_iz_zero mid id op1 inst)
Proof
  rw[ao_cmp_prefer_iz_zero_def, inok_def] >>
  qpat_x_assum `MEM q _` (strip_assume_tac o SIMP_RULE (srw_ss())[listTheory.MEM]) >>
  gvs[] >> metis_tac[]
QED

Triviality cmp_prefer_iz_max_inok[local]:
  !fv mid id op1 inst.
    (!w. op1 = Var w ==> w NOTIN fv) ==>
    inok fv id (ao_cmp_prefer_iz_max mid id op1 inst)
Proof
  rw[ao_cmp_prefer_iz_max_def, inok_def] >>
  qpat_x_assum `MEM q _` (strip_assume_tac o SIMP_RULE (srw_ss())[listTheory.MEM]) >>
  gvs[] >> metis_tac[]
QED

Triviality cmp_prefer_iz_general_inok[local]:
  !fv mid id op1 op2 inst.
    (!w. op1 = Var w ==> w NOTIN fv) /\ (!w. op2 = Var w ==> w NOTIN fv) ==>
    inok fv id (ao_cmp_prefer_iz_general mid id op1 op2 inst)
Proof
  rw[ao_cmp_prefer_iz_general_def, inok_def] >>
  qpat_x_assum `MEM q _` (strip_assume_tac o SIMP_RULE (srw_ss())[listTheory.MEM]) >>
  gvs[] >> metis_tac[]
QED

Triviality opt_comparator_inok[local]:
  !fv mid dfg ra lbl idx inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    inok fv inst.inst_id (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  TRY (drule cmp_range_lit >> strip_tac >> gvs[]) >>
  FIRST [
    (irule cmp_prefer_iz_zero_inok >> rw[] >> gvs[listTheory.MEM] >> metis_tac[]),
    (irule cmp_prefer_iz_max_inok >> rw[] >> gvs[listTheory.MEM] >> metis_tac[]),
    (irule cmp_prefer_iz_general_inok >> rw[] >> gvs[listTheory.MEM] >> metis_tac[]),
    (irule inok_named >> rpt strip_tac >>
     qpat_x_assum `MEM q _`
       (strip_assume_tac o SIMP_RULE (srw_ss())[listTheory.MEM]) >>
     gvs[listTheory.MEM] >> metis_tac[])
  ]
QED

Triviality opt_comparator_cmpinok[local]:
  !fv mid dfg ra lbl idx inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    cmpinok fv (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  FIRST [
    (irule cmp_prefer_iz_zero_cmpinok),
    (irule cmp_prefer_iz_max_cmpinok),
    (irule cmp_prefer_iz_general_cmpinok),
    (irule cmpinok_no_comp >> rw[] >> gvs[is_comparator_def] >> NO_TAC),
    (irule cmpinok_clean >> rpt strip_tac >> gvs[] >> metis_tac[])
  ]
QED

(* ===== peephole / producer / transform ===== *)

Triviality peephole_inok[local]:
  !fv mid dfg ra lbl idx inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    inok fv inst.inst_id (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >> rw[ao_peephole_inst_def] >>
  FIRST [
    (irule opt_eq_inok >> fs[]),
    (irule opt_comparator_inok >> fs[]),
    (irule inok_clean >>
     FIRST [match_mp_tac opt_shift_opnds_clean,
            match_mp_tac opt_signextend_opnds_clean,
            match_mp_tac opt_exp_opnds_clean,
            match_mp_tac opt_addsub_opnds_clean,
            match_mp_tac opt_and_opnds_clean,
            match_mp_tac opt_muldiv_opnds_clean,
            match_mp_tac opt_or_opnds_clean] >> fs[]),
    (irule inok_clean >> rpt strip_tac >> gvs[] >> metis_tac[])
  ]
QED

Triviality peephole_cmpinok[local]:
  !fv mid dfg ra lbl idx inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    cmpinok fv (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >> rw[ao_peephole_inst_def] >>
  FIRST [
    (irule opt_eq_cmpinok >> fs[]),
    (irule opt_comparator_cmpinok >> fs[]),
    (irule cmpinok_clean >>
     FIRST [match_mp_tac opt_shift_opnds_clean,
            match_mp_tac opt_signextend_opnds_clean,
            match_mp_tac opt_exp_opnds_clean,
            match_mp_tac opt_addsub_opnds_clean,
            match_mp_tac opt_and_opnds_clean,
            match_mp_tac opt_muldiv_opnds_clean,
            match_mp_tac opt_or_opnds_clean] >> fs[]),
    (irule cmpinok_clean >> rpt strip_tac >> gvs[] >> metis_tac[])
  ]
QED

Triviality producer_opnds[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r ==>
    !q w. MEM q r /\ MEM (Var w) q.inst_operands ==>
          MEM (Var w) inst.inst_operands
Proof
  rw[ao_opt_producer_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality transform_inst_inok[local]:
  !fv mid dfg ra lbl idx targets inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    inok fv inst.inst_id (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  `!w. MEM (Var w) (ao_resolve_iszero_inst targets inst).inst_operands ==>
       w NOTIN fv` by
    (match_mp_tac resolve_inst_opnds_clean >> conj_tac >> metis_tac[]) >>
  simp[ao_transform_inst_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >> simp[]) >>
  TRY (irule inok_clean >> rpt strip_tac >> gvs[] >> metis_tac[] >> NO_TAC) >>
  FIRST [
    (irule inok_post_flip_last >> irule inok_clean >> rpt strip_tac >>
     drule_all producer_opnds >> metis_tac[]),
    (irule inok_post_flip_last >>
     qspecl_then [`fv`, `mid`, `dfg`, `ra`, `lbl`, `idx`,
       `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
       mp_tac peephole_inok >>
     impl_tac
     >- (rpt strip_tac >> drule pre_flip_operand_mem >> metis_tac[])
     >- simp[pre_flip_id, resolve_id])
  ]
QED

Triviality transform_inst_cmpinok[local]:
  !fv mid dfg ra lbl idx targets inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    cmpinok fv (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  `!w. MEM (Var w) (ao_resolve_iszero_inst targets inst).inst_operands ==>
       w NOTIN fv` by
    (match_mp_tac resolve_inst_opnds_clean >> conj_tac >> metis_tac[]) >>
  simp[ao_transform_inst_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >> simp[]) >>
  TRY (irule cmpinok_clean >> rpt strip_tac >> gvs[] >> metis_tac[] >> NO_TAC) >>
  FIRST [
    (irule cmpinok_post_flip_last >> irule cmpinok_no_comp >> rpt strip_tac >>
     drule producer_no_comp >> strip_tac >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]),
    (irule cmpinok_post_flip_last >>
     qspecl_then [`fv`, `mid`, `dfg`, `ra`, `lbl`, `idx`,
       `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
       mp_tac peephole_cmpinok >>
     impl_tac
     >- (rpt strip_tac >> drule pre_flip_operand_mem >> metis_tac[])
     >- simp[])
  ]
QED

(* ===== resolve post-pass preserves inok / cmpinok ===== *)

(* The M2 PHI resolution rewrites a PHI operand to an earlier iszero-chain
   entry.  Chain entries are clean (chain-vars-not-fresh hypothesis), so a
   fresh operand of a resolved instruction must have come from the original
   operand list, where inok already constrains it. *)
Triviality inok_map_resolve[local]:
  !targets fv id l.
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) /\
    inok fv id l ==>
    inok fv id
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)
Proof
  rw[inok_def, listTheory.MEM_MAP] >>
  rename1 `MEM xx l` >>
  reverse (Cases_on `xx.inst_opcode = PHI`) >> gvs[]
  >- metis_tac[] >>
  qpat_x_assum `MEM (Var w) (ao_resolve_iszero_inst _ _).inst_operands` mp_tac >>
  simp[ao_resolve_iszero_inst_def, listTheory.MEM_MAP] >> rpt strip_tac >>
  qmatch_asmsub_rename_tac `Var w = ao_resolve_iszero_op targets PHI op` >>
  qspecl_then [`targets`, `PHI`, `op`] strip_assume_tac resolve_op_cases
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `?yy. chain = SND yy /\ MEM yy targets` by
    (qexists_tac `(vv, chain)` >> simp[] >> metis_tac[alistTheory.ALOOKUP_MEM]) >>
  `w NOTIN fv` by metis_tac[] >> gvs[]
QED

Triviality cmpinok_map_resolve[local]:
  !targets fv l.
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) /\
    cmpinok fv l ==>
    cmpinok fv
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)
Proof
  rw[cmpinok_def] >>
  `?p. MEM p l /\ is_comparator p.inst_opcode` by
    (gvs[listTheory.MEM_MAP] >> metis_tac[resolve_phi_inst_opcode]) >>
  `!q w. MEM q l /\ MEM (Var w) q.inst_operands ==> w NOTIN fv` by metis_tac[] >>
  gvs[listTheory.MEM_MAP] >>
  qmatch_asmsub_rename_tac
    `MEM (Var _) (if zz.inst_opcode = PHI
                  then ao_resolve_iszero_inst targets zz else zz).inst_operands` >>
  reverse (Cases_on `zz.inst_opcode = PHI`) >> gvs[]
  >- metis_tac[] >>
  qspecl_then [`targets`, `zz`, `fv`] mp_tac resolve_inst_opnds_clean >>
  impl_tac
  >- (conj_tac >- metis_tac[] >> rw[listTheory.MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

(* ===== all_cmppieces operand invariants ===== *)

Triviality all_cmppieces_inok[local]:
  !mid dfg ra targets fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==>
            w NOTIN ao_fn_fresh_vars fn) ==>
    EVERY (\p. inok (ao_fn_fresh_vars fn) (FST p) (SND (SND p)))
      (all_cmppieces mid dfg ra targets fn)
Proof
  rw[all_cmppieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_cmppieces_def, indexedListsTheory.MEM_MAPi] >>
  qmatch_goalsub_abbrev_tac `ao_transform_inst _ _ _ _ _ _ inst` >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
     simp[listTheory.MEM_EL, Abbr`inst`] >> metis_tac[]) >>
  irule inok_map_resolve >> conj_tac
  >- (rpt strip_tac >> metis_tac[listTheory.MEM_MAP]) >>
  irule transform_inst_inok >>
  simp[listTheory.MEM_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> metis_tac[]
QED

Triviality all_cmppieces_cmpinok[local]:
  !mid dfg ra targets fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==>
            w NOTIN ao_fn_fresh_vars fn) ==>
    EVERY (\p. cmpinok (ao_fn_fresh_vars fn) (SND (SND p)))
      (all_cmppieces mid dfg ra targets fn)
Proof
  rw[all_cmppieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_cmppieces_def, indexedListsTheory.MEM_MAPi] >>
  qmatch_goalsub_abbrev_tac `ao_transform_inst _ _ _ _ _ _ inst` >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
     simp[listTheory.MEM_EL, Abbr`inst`] >> metis_tac[]) >>
  irule cmpinok_map_resolve >> conj_tac
  >- (rpt strip_tac >> metis_tac[listTheory.MEM_MAP]) >>
  irule transform_inst_cmpinok >>
  simp[listTheory.MEM_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> metis_tac[]
QED

(* ===== core list lemma + top-level ===== *)

Triviality flat_operands_flat[local]:
  !pieces.
    FLAT (MAP (\q. q.inst_operands) (FLAT (MAP (\p. SND (SND p)) pieces))) =
    FLAT (MAP (\p. FLAT (MAP (\q. q.inst_operands) (SND (SND p)))) pieces)
Proof
  Induct >> simp[listTheory.FLAT_APPEND]
QED

Triviality cmppieces_no_cmp_operand_iz[local]:
  !fv pieces i0.
    ALL_DISTINCT (MAP FST pieces) /\
    EVERY (\p. cmpok fv (FST p) (SND (SND p))) pieces /\
    EVERY (\p. cmpinok fv (SND (SND p))) pieces /\
    EVERY (\p. inok fv (FST p) (SND (SND p))) pieces /\
    (!p. MEM p pieces ==> ao_fresh_var (FST p) "iz" IN fv) /\
    MEM i0 (FLAT (MAP (\p. SND (SND p)) pieces)) /\
    is_comparator i0.inst_opcode ==>
    ~MEM (Var (ao_fresh_var i0.inst_id "iz"))
         (FLAT (MAP (\q. q.inst_operands)
            (FLAT (MAP (\p. SND (SND p)) pieces))))
Proof
  rpt strip_tac >>
  `?p0. MEM p0 pieces /\ MEM i0 (SND (SND p0))` by
    (qpat_x_assum `MEM i0 (FLAT _)` mp_tac >>
     simp[listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  `cmpok fv (FST p0) (SND (SND p0))` by
    (qpat_x_assum `EVERY (\p. cmpok _ _ _) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `i0.inst_id = FST p0` by (fs[cmpok_def] >> metis_tac[]) >>
  `?p1 q1. MEM p1 pieces /\ MEM q1 (SND (SND p1)) /\
           MEM (Var (ao_fresh_var i0.inst_id "iz")) q1.inst_operands` by
    (qpat_x_assum `MEM (Var _) (FLAT _)` mp_tac >>
     simp[flat_operands_flat, listTheory.MEM_FLAT, listTheory.MEM_MAP,
          PULL_EXISTS] >> metis_tac[]) >>
  `ao_fresh_var i0.inst_id "iz" IN fv` by metis_tac[] >>
  `inok fv (FST p1) (SND (SND p1))` by
    (qpat_x_assum `EVERY (\p. inok _ _ _) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?s. (s = "not" \/ s = "iz" \/ s = "xor") /\
       ao_fresh_var i0.inst_id "iz" = ao_fresh_var (FST p1) s` by
    (fs[inok_def] >> metis_tac[]) >>
  `FST p0 = FST p1` by metis_tac[ao_fresh_var_full_inj] >>
  `p0 = p1` by metis_tac[all_distinct_fst_inj] >>
  `cmpinok fv (SND (SND p1))` by
    (qpat_x_assum `EVERY (\p. cmpinok _ _) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?p. MEM p (SND (SND p1)) /\ is_comparator p.inst_opcode` by
    (qexists_tac `i0` >> gvs[]) >>
  fs[cmpinok_def] >>
  `ao_fresh_var i0.inst_id "iz" NOTIN fv` by metis_tac[] >>
  metis_tac[]
QED

Theorem ao_phase3_no_cmp_operand_iz:
  !mid dfg ra targets fn c.
    fn_inst_ids_distinct fn /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==>
            w NOTIN ao_fn_fresh_vars fn) /\
    (?i. MEM i (fn_insts (function_map_transform
                  (ao_transform_block mid dfg ra targets) fn)) /\
         i.inst_id = c /\ is_comparator i.inst_opcode) ==>
    ~MEM (Var (ao_fresh_var c "iz"))
       (FLAT (MAP (\i. i.inst_operands)
         (fn_insts (function_map_transform
            (ao_transform_block mid dfg ra targets) fn))))
Proof
  rpt strip_tac >>
  qabbrev_tac `pieces = all_cmppieces mid dfg ra targets fn` >>
  `fn_insts (function_map_transform (ao_transform_block mid dfg ra targets) fn) =
   FLAT (MAP (\p. SND (SND p)) pieces)` by
    simp[Abbr `pieces`, all_cmppieces_insts] >>
  qpat_x_assum `i.inst_id = c` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `fn_insts _ = FLAT _` SUBST_ALL_TAC >>
  qspecl_then [`ao_fn_fresh_vars fn`, `pieces`, `i`]
    mp_tac cmppieces_no_cmp_operand_iz >>
  impl_tac
  >- (rpt conj_tac
      >- (simp[Abbr `pieces`, all_cmppieces_fst, map_inst_id_fn_insts] >>
          fs[fn_inst_ids_distinct_def])
      >- (simp[Abbr `pieces`] >> irule all_cmppieces_cmpok >>
          rpt strip_tac >> metis_tac[])
      >- (simp[Abbr `pieces`] >> irule all_cmppieces_cmpinok >>
          rpt strip_tac >> metis_tac[])
      >- (simp[Abbr `pieces`] >> irule all_cmppieces_inok >>
          rpt strip_tac >> metis_tac[])
      >- (rpt strip_tac >>
          `MEM (FST p) (MAP FST pieces)` by
            (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
          `MAP FST pieces = MAP (\i. i.inst_id) (fn_insts fn)` by
            simp[Abbr `pieces`, all_cmppieces_fst] >>
          irule fresh_mem >> gvs[])
      >> gvs[]) >>
  simp[]
QED

(* chains of the iszero targets only reference operands/outputs of source insts *)
Theorem ao_fn_iszero_targets_clean:
  !fn P.
    (!inst w. MEM inst (fn_insts fn) /\
       (MEM (Var w) inst.inst_operands \/ MEM w inst.inst_outputs) ==> P w) ==>
    !ch w. MEM ch (MAP SND (ao_compute_fn_iszero_targets fn)) /\
           MEM (Var w) ch ==> P w
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  qspecl_then [`fn_insts fn`, `[]`, `P`] mp_tac iszero_step_entries >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  simp[]
QED

val _ = export_theory();
