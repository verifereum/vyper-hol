(* Obligation: OR-truthy rewrite preserves block execution up to dead vars.
 *
 * The OR-truthy mini-pass rewrites `or x, n` (n <> 0, all uses truthy) to
 * `assign 1`.  Since `x | n` is always nonzero when n <> 0, and the only
 * users of the output observe its zero-ness (iszero/jnz/assert/
 * assert_unreachable), the rewrite preserves observable behaviour.
 *
 * The output variable's *value* changes (x|n -> 1), so the simulation is up
 * to a set of "dead" variables, using the two-state invariant or_truthy_inv:
 * dead-var definedness agrees across the two executions, and dead vars are
 * nonzero on each side.
 *
 * TOP-LEVEL: ao_or_truthy_block_sim, ao_or_truthy_block_ok_inv
 *)
Theory aoOrTruthySim
Ancestors
  algebraicOptDefs
  dfgDefs dfgAnalysisProps
  aoStrictDomObligation
  stateEquiv stateEquivProps stateEquivProofs execEquivProps passSimulationProps
  passSharedDefs venomInstProps
  venomExecSemantics venomExecProofs venomState venomInst venomWf
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_or_truthy_dead_vars_def",
                  "ao_or_truthy_scan_def",
                  "ao_or_truthy_apply_inst_def"]

(* ===== Basic word fact ===== *)

Triviality word_or_nonzero[local]:
  !(n:bytes32) x. n <> 0w ==> word_or n x <> 0w
Proof
  rw[wordsTheory.word_or_def, wordsTheory.word_0,
     fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >> metis_tac[]
QED

(* ===== operand_vars membership ===== *)

(* operand_vars is duplicated in venomInst and dfgDefs; pin to the dfgDefs
   constant, matching dfg_build_function_uses_complete. *)
Triviality MEM_operand_vars_iff[local]:
  !ops v. MEM v (dfgDefs$operand_vars ops) <=> MEM (Var v) ops
Proof
  Induct_on `ops` >> simp[dfgDefsTheory.operand_vars_def] >>
  Cases_on `h` >>
  simp[dfgDefsTheory.operand_var_def, dfgDefsTheory.operand_vars_def] >>
  metis_tac[]
QED

(* ===== Distinct-id helpers ===== *)

Triviality all_distinct_id_unique[local]:
  !insts x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    MEM x insts /\ MEM y insts /\ x.inst_id = y.inst_id ==>
    x = y
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum irule >> gvs[] >> NO_TAC) >>
  fs[listTheory.MEM_MAP] >> metis_tac[]
QED

Triviality fn_insts_ids_all_distinct[local]:
  !fn. fn_inst_ids_distinct fn ==>
       ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def] >> gen_tac >>
  `FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks) =
   MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)` suffices_by simp[] >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def]
QED

(* ===== Scan characterization ===== *)

(* Every scanned id belongs to an eligible OR instruction in the list. *)
Triviality scan_mem_imp[local]:
  !dfg insts id.
    MEM id (ao_or_truthy_scan dfg insts) ==>
    ?inst. MEM inst insts /\ inst.inst_id = id /\
           inst.inst_opcode = OR /\
           (?op1 n. inst.inst_operands = [Lit n; op1] /\ n <> 0w) /\
           ao_all_truthy dfg inst
Proof
  Induct_on `insts` >- simp[ao_or_truthy_scan_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  simp[ao_or_truthy_scan_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[]
      >- (qexists_tac `h` >> gvs[] >> every_case_tac >> gvs[])
      >> last_x_assum drule >> strip_tac >> metis_tac[])
  >> strip_tac >> last_x_assum drule >> strip_tac >> metis_tac[]
QED

(* ===== Invariant ===== *)

(* Two-state invariant for the OR-truthy rewrite.
   For every scanned-OR output `out`:
     - definedness agrees between s1 and s2;
     - whenever defined, the value is nonzero on each side. *)
Definition or_truthy_inv_def:
  or_truthy_inv ids all_insts s1 s2 <=>
    !inst out.
      MEM inst all_insts /\ MEM inst.inst_id ids /\ MEM out inst.inst_outputs ==>
      (IS_SOME (lookup_var out s1) <=> IS_SOME (lookup_var out s2)) /\
      (!v. lookup_var out s1 = SOME v ==> v <> 0w) /\
      (!v. lookup_var out s2 = SOME v ==> v <> 0w)
End

(* ===== DFG truthy bridge ===== *)

(* A scanned OR has a single output, and every actual use of that output is
   a truthy instruction. *)
Triviality scan_output_uses_truthy[local]:
  !fn oinst out use.
    fn_inst_ids_distinct fn /\
    MEM oinst (fn_insts fn) /\
    MEM oinst.inst_id (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
    MEM out oinst.inst_outputs /\
    MEM use (fn_insts fn) /\
    MEM (Var out) use.inst_operands ==>
    is_truthy_inst use.inst_opcode
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  drule scan_mem_imp >> strip_tac >>
  rename1 `MEM oinst2 (fn_insts fn)` >>
  `oinst2 = oinst` by (irule all_distinct_id_unique >> metis_tac[]) >>
  gvs[] >>
  `oinst.inst_outputs = [out] /\
   EVERY (\u. is_truthy_inst u.inst_opcode)
     (dfg_get_uses (dfg_build_function fn) out)` by
    (qpat_x_assum `ao_all_truthy _ oinst` mp_tac >>
     simp[ao_all_truthy_def] >>
     Cases_on `oinst.inst_outputs` >> simp[] >>
     Cases_on `t` >> simp[] >> strip_tac >> gvs[]) >>
  `MEM use (dfg_get_uses (dfg_build_function fn) out)` by
    (irule dfg_build_function_uses_complete >> simp[MEM_operand_vars_iff]) >>
  gvs[listTheory.EVERY_MEM]
QED

(* A non-truthy instruction never reads a dead variable. *)
Triviality nontruthy_operand_not_dead[local]:
  !fn use x.
    fn_inst_ids_distinct fn /\
    MEM use (fn_insts fn) /\
    ~is_truthy_inst use.inst_opcode /\
    MEM (Var x) use.inst_operands ==>
    x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn
Proof
  rpt strip_tac >>
  gvs[ao_or_truthy_dead_vars_def, pred_setTheory.GSPECIFICATION] >>
  `is_truthy_inst use.inst_opcode` by
    (irule scan_output_uses_truthy >> metis_tac[]) >>
  gvs[]
QED

(* ===== State-equivalence update helpers ===== *)

(* Updating a dead var (possibly to different values) preserves state_equiv. *)
Triviality update_dead_var_state_equiv[local]:
  !dead x v1 v2 s1 s2.
    state_equiv dead s1 s2 /\ x IN dead ==>
    state_equiv dead (update_var x v1 s1) (update_var x v2 s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* Updating any var to the SAME value preserves state_equiv. *)
Triviality update_same_state_equiv[local]:
  !dead x v s1 s2.
    state_equiv dead s1 s2 ==>
    state_equiv dead (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* ===== INVOKE result equivalence (operands avoid dead) ===== *)

Triviality eval_operands_equiv[local]:
  !ops dead s1 s2.
    state_equiv dead s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN dead) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_equiv >> qexists_tac `dead` >> simp[] >>
     Cases_on `h` >> simp[] >> metis_tac[]) >>
  gvs[] >> Cases_on `eval_operand h s2` >> gvs[] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> qexists_tac `dead` >> simp[]) >>
  gvs[]
QED

Triviality merge_callee_state_equiv[local]:
  !dead s1 s2 cs.
    state_equiv dead s1 s2 ==>
    state_equiv dead (merge_callee_state s1 cs) (merge_callee_state s2 cs)
Proof
  rw[merge_callee_state_def, state_equiv_def, execution_equiv_def,
     lookup_var_def]
QED

Triviality foldl_update_var_state_equiv[local]:
  !pairs dead s1 s2.
    state_equiv dead s1 s2 ==>
    state_equiv dead
      (FOLDL (\s' (out, val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out, val). update_var out val s') s2 pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >>
  first_x_assum irule >>
  gvs[state_equiv_def, execution_equiv_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Triviality bind_outputs_state_equiv[local]:
  !outs vals dead s1 s2.
    state_equiv dead s1 s2 ==>
    case (bind_outputs outs vals s1, bind_outputs outs vals s2) of
      (SOME s1', SOME s2') => state_equiv dead s1' s2'
    | (NONE, NONE) => T
    | _ => F
Proof
  rpt strip_tac >> simp[bind_outputs_def] >>
  IF_CASES_TAC >> simp[] >>
  irule foldl_update_var_state_equiv >> simp[]
QED

Triviality step_inst_invoke_result_equiv[local]:
  !fuel ctx dead inst s1 s2.
    state_equiv dead s1 s2 /\
    inst.inst_opcode = INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN dead) ==>
    result_equiv dead (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  simp_tac std_ss [Once step_inst_def] >>
  simp_tac std_ss [Once step_inst_def] >>
  Cases_on `decode_invoke inst`
  >- simp[result_equiv_def] >>
  PairCases_on `x` >>
  rename1 `SOME (cname, arg_ops)` >>
  `inst.inst_operands = Label cname :: arg_ops` by
    (qpat_x_assum `decode_invoke _ = _` mp_tac >>
     simp[decode_invoke_def, AllCaseEqs()] >>
     Cases_on `inst.inst_operands` >> simp[]) >>
  simp[] >>
  Cases_on `lookup_function cname ctx.ctx_functions`
  >- simp[result_equiv_def] >>
  rename1 `SOME callee_fn` >>
  `eval_operands arg_ops s1 = eval_operands arg_ops s2` by
    (irule eval_operands_equiv >> qexists_tac `dead` >> simp[]) >>
  simp[] >>
  Cases_on `eval_operands arg_ops s2`
  >- simp[result_equiv_def] >>
  rename1 `SOME args` >> simp[] >>
  `setup_callee callee_fn args s1 = setup_callee callee_fn args s2` by
    (simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
     simp[venomStateTheory.venom_state_component_equality] >>
     fs[state_equiv_def, execution_equiv_def]) >>
  simp[] >>
  Cases_on `setup_callee callee_fn args s2`
  >- simp[result_equiv_def] >>
  rename1 `SOME callee_s` >> simp[] >>
  Cases_on `run_blocks fuel ctx callee_fn callee_s` >>
  simp[result_equiv_def] >>
  `state_equiv dead (merge_callee_state s1 v) (merge_callee_state s2 v)` by
    (irule merge_callee_state_equiv >> simp[]) >>
  `case (bind_outputs inst.inst_outputs l (merge_callee_state s1 v),
         bind_outputs inst.inst_outputs l (merge_callee_state s2 v)) of
     (SOME s1', SOME s2') => state_equiv dead s1' s2'
   | (NONE, NONE) => T
   | _ => F` by
    (irule bind_outputs_state_equiv >> simp[]) >>
  Cases_on `bind_outputs inst.inst_outputs l (merge_callee_state s1 v)` >>
  Cases_on `bind_outputs inst.inst_outputs l (merge_callee_state s2 v)` >>
  gvs[result_equiv_def, state_equiv_def, execution_equiv_def]
QED

(* ===== Scanned-instruction shape and dead-output bridges ===== *)

(* A scanned (rewritten) instruction is an eligible OR with a single output. *)
Triviality scanned_inst_shape[local]:
  !fn inst.
    fn_inst_ids_distinct fn /\
    MEM inst (fn_insts fn) /\
    MEM inst.inst_id (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) ==>
    inst.inst_opcode = OR /\
    (?op1 n. inst.inst_operands = [Lit n; op1] /\ n <> 0w) /\
    (?out. inst.inst_outputs = [out])
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  drule scan_mem_imp >> strip_tac >>
  rename1 `MEM inst2 (fn_insts fn)` >>
  `inst2 = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `ao_all_truthy _ _` mp_tac >> simp[ao_all_truthy_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >> Cases_on `t` >> simp[]
QED

(* The output of a scanned instruction is a dead variable. *)
Triviality scanned_output_dead[local]:
  !fn inst out.
    MEM inst (fn_insts fn) /\
    MEM inst.inst_id (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
    MEM out inst.inst_outputs ==>
    out IN ao_or_truthy_dead_vars (dfg_build_function fn) fn
Proof
  rpt strip_tac >>
  simp[ao_or_truthy_dead_vars_def, pred_setTheory.GSPECIFICATION] >>
  metis_tac[]
QED

(* An UNCHANGED instruction never writes a dead variable. *)
Triviality unchanged_no_dead_output[local]:
  !fn inst outv.
    ssa_form fn /\
    MEM inst (fn_insts fn) /\
    ~MEM inst.inst_id (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
    MEM outv inst.inst_outputs ==>
    outv NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn
Proof
  rpt strip_tac >>
  gvs[ao_or_truthy_dead_vars_def, pred_setTheory.GSPECIFICATION] >>
  rename1 `MEM jinst (fn_insts fn)` >>
  `inst = jinst` by (irule ssa_output_unique >> metis_tac[]) >>
  gvs[]
QED

(* A terminator that yields OK only does a jump, preserving variables. *)
Triviality ok_terminator_preserves_lookup[local]:
  !fuel ctx inst s s' v.
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `is_terminator _` mp_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def, step_inst_base_def] >>
  every_case_tac >> rw[] >> gvs[jump_to_def, lookup_var_def]
QED

(* ===== Truthy instruction reading a dead operand ===== *)

(* A truthy instruction (iszero/jnz/assert/assert_unreachable) reading a dead
   variable: the dead var is nonzero (or undefined) on each side, so the zero/
   abort branch never fires and the two executions agree up to dead vars. *)
Triviality truthy_dead_step[local]:
  !fn fuel ctx inst s1 s2 x.
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 /\
    is_truthy_inst inst.inst_opcode /\
    MEM (Var x) inst.inst_operands /\
    x IN ao_or_truthy_dead_vars (dfg_build_function fn) fn ==>
    result_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  qabbrev_tac `dead = ao_or_truthy_dead_vars (dfg_build_function fn) fn` >>
  `?jinst. MEM jinst (fn_insts fn) /\
           MEM jinst.inst_id
             (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
           MEM x jinst.inst_outputs` by
    (qunabbrev_tac `dead` >>
     gvs[ao_or_truthy_dead_vars_def, pred_setTheory.GSPECIFICATION] >>
     metis_tac[]) >>
  `(IS_SOME (lookup_var x s1) <=> IS_SOME (lookup_var x s2)) /\
   (!a. lookup_var x s1 = SOME a ==> a <> 0w) /\
   (!b. lookup_var x s2 = SOME b ==> b <> 0w)` by
    (qpat_x_assum `or_truthy_inv _ _ _ _` mp_tac >> simp[or_truthy_inv_def] >>
     disch_then (qspecl_then [`jinst`,`x`] mp_tac) >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by gvs[is_truthy_inst_def] >>
  qpat_x_assum `is_truthy_inst _` mp_tac >> simp[is_truthy_inst_def] >>
  strip_tac >> pop_assum strip_assume_tac >> gvs[step_inst_non_invoke]
  >| [
    (* ISZERO *)
    (qpat_x_assum `inst.inst_opcode = ISZERO`
       (fn th => simp[step_inst_base_def, exec_pure1_def, th]) >>
     Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
     rename1 `(arg1:operand)::args` >>
     Cases_on `args` >> simp[result_equiv_def] >>
     `arg1 = Var x` by (fs[] >> metis_tac[]) >>
     gvs[] >> simp[eval_operand_def] >>
     Cases_on `lookup_var x s1` >> Cases_on `lookup_var x s2` >> fs[] >| [
       simp[result_equiv_def],
       (Cases_on `inst.inst_outputs` >> simp[result_equiv_def] >>
        rename1 `(outv:string)::outs` >>
        Cases_on `outs` >> simp[result_equiv_def] >>
        gvs[result_equiv_def, bool_to_word_def] >>
        irule update_same_state_equiv >> simp[])
     ]),
    (* JNZ *)
    (qpat_x_assum `inst.inst_opcode = JNZ`
       (fn th => simp[step_inst_base_def, th]) >>
     rpt (TOP_CASE_TAC >> gvs[result_equiv_def, eval_operand_def]) >>
     irule jump_to_preserves >> simp[]),
    (* ASSERT *)
    (qpat_x_assum `inst.inst_opcode = ASSERT`
       (fn th => simp[step_inst_base_def, th]) >>
     Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
     rename1 `(arg1:operand)::args` >>
     Cases_on `args` >> simp[result_equiv_def] >>
     `arg1 = Var x` by (fs[] >> metis_tac[]) >>
     gvs[] >> simp[eval_operand_def] >>
     Cases_on `lookup_var x s1` >> Cases_on `lookup_var x s2` >> fs[] >| [
       simp[result_equiv_def],
       gvs[result_equiv_def]
     ]),
    (* ASSERT_UNREACHABLE *)
    (qpat_x_assum `inst.inst_opcode = ASSERT_UNREACHABLE`
       (fn th => simp[step_inst_base_def, th]) >>
     Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
     rename1 `(arg1:operand)::args` >>
     Cases_on `args` >> simp[result_equiv_def] >>
     `arg1 = Var x` by (fs[] >> metis_tac[]) >>
     gvs[] >> simp[eval_operand_def] >>
     Cases_on `lookup_var x s1` >> Cases_on `lookup_var x s2` >> fs[] >| [
       simp[result_equiv_def],
       gvs[result_equiv_def]
     ])
  ]
QED

(* ===== Dead-var lookup preservation ===== *)

(* An unchanged (non-scanned) instruction preserves the lookup of any dead
   variable: terminators preserve all lookups, others write only their own
   outputs which (under SSA) are never dead. *)
Triviality step_preserves_dead_lookup[local]:
  !fn fuel ctx inst s s' out.
    ssa_form fn /\ MEM inst (fn_insts fn) /\
    ~MEM inst.inst_id
       (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
    step_inst fuel ctx inst s = OK s' /\
    out IN ao_or_truthy_dead_vars (dfg_build_function fn) fn ==>
    lookup_var out s' = lookup_var out s
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[ok_terminator_preserves_lookup] >>
  `~MEM out inst.inst_outputs` by
    (strip_tac >>
     `out NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn` by
       (irule unchanged_no_dead_output >> metis_tac[]) >>
     gvs[]) >>
  metis_tac[venomInstPropsTheory.step_preserves_non_output_vars]
QED

(* or_truthy_inv is preserved when an unchanged instruction steps OK on both
   sides (dead-var lookups are untouched). *)
Triviality or_truthy_inv_step_unchanged[local]:
  !fn fuel ctx inst s1 s2 s1' s2'.
    ssa_form fn /\ fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
    ~MEM inst.inst_id
       (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 /\
    step_inst fuel ctx inst s1 = OK s1' /\
    step_inst fuel ctx inst s2 = OK s2' ==>
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1' s2'
Proof
  rpt strip_tac >> simp[or_truthy_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM jinst (fn_insts fn)` >>
  `out IN ao_or_truthy_dead_vars (dfg_build_function fn) fn` by
    (irule scanned_output_dead >> metis_tac[]) >>
  `lookup_var out s1' = lookup_var out s1` by
    (irule step_preserves_dead_lookup >> metis_tac[]) >>
  `lookup_var out s2' = lookup_var out s2` by
    (irule step_preserves_dead_lookup >> metis_tac[]) >>
  qpat_x_assum `or_truthy_inv _ _ s1 s2` mp_tac >> simp[or_truthy_inv_def] >>
  disch_then (qspecl_then [`jinst`,`out`] mp_tac) >> simp[]
QED

(* ===== Scanned OR rewrite step ===== *)

(* A scanned OR `or x, n` (n <> 0) steps to OK with a nonzero output, while the
   transformed `assign 1` always steps to OK with output 1.  The output is dead,
   so the states stay equivalent, and or_truthy_inv is re-established (output
   nonzero on both sides). The original may error if its operand is undefined. *)
Triviality scanned_or_step[local]:
  !fn fuel ctx inst s1 s2.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM inst (fn_insts fn) /\
    MEM inst.inst_id
       (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) /\
    inst.inst_opcode = OR /\
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 ==>
    (?e. step_inst fuel ctx inst s1 = Error e) \/
    ?s1' s2'.
      step_inst fuel ctx inst s1 = OK s1' /\
      step_inst fuel ctx
        (ao_or_truthy_apply_inst
           (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) inst) s2 =
        OK s2' /\
      state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1' s2' /\
      or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                    (fn_insts fn) s1' s2'
Proof
  rpt strip_tac >>
  qabbrev_tac `dead = ao_or_truthy_dead_vars (dfg_build_function fn) fn` >>
  `?op1 n. inst.inst_operands = [Lit n; op1] /\ n <> 0w` by
    metis_tac[scanned_inst_shape] >>
  `?out. inst.inst_outputs = [out]` by metis_tac[scanned_inst_shape] >>
  `out IN dead` by (qunabbrev_tac `dead` >> irule scanned_output_dead >>
                    qexists_tac `inst` >> simp[]) >>
  `ao_or_truthy_apply_inst
     (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) inst =
     inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>` by
    simp[ao_or_truthy_apply_inst_def] >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       eval_operand_def] >>
  Cases_on `eval_operand op1 s1`
  >- (DISJ1_TAC >> simp[]) >>
  rename1 `eval_operand op1 s1 = SOME v` >> simp[] >>
  `state_equiv dead (update_var out (word_or n v) s1) (update_var out 1w s2)` by
    (irule update_dead_var_state_equiv >> simp[]) >>
  simp[] >>
  simp[or_truthy_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM jinst (fn_insts fn)` >>
  `out' IN dead` by (qunabbrev_tac `dead` >> irule scanned_output_dead >>
                     qexists_tac `jinst` >> simp[]) >>
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `out' = out`
  >- gvs[word_or_nonzero] >>
  simp[] >>
  qpat_x_assum `or_truthy_inv _ _ s1 s2` mp_tac >> simp[or_truthy_inv_def] >>
  disch_then (qspecl_then [`jinst`,`out'`] mp_tac) >> simp[lookup_var_def]
QED

(* ===== Unchanged instruction step ===== *)

(* An instruction left unchanged by the rewrite preserves result_equiv: if it
   reads a dead var it is truthy (truthy_dead_step), otherwise its operands all
   avoid dead vars (step_inst_result_equiv / INVOKE variant). *)
Triviality unchanged_result_equiv[local]:
  !fn fuel ctx inst s1 s2.
    fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 ==>
    result_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `?x. MEM (Var x) inst.inst_operands /\
                x IN ao_or_truthy_dead_vars (dfg_build_function fn) fn`
  >- (fs[] >>
      `is_truthy_inst inst.inst_opcode` by
        (CCONTR_TAC >>
         `x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn` by
           (irule nontruthy_operand_not_dead >> metis_tac[]) >>
         gvs[]) >>
      irule truthy_dead_step >> metis_tac[]) >>
  `!x. MEM (Var x) inst.inst_operands ==>
       x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn` by metis_tac[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule step_inst_invoke_result_equiv >> simp[]) >>
  irule step_inst_result_equiv >> simp[]
QED

(* ===== Per-instruction two-state step ===== *)

(* Either the original errors, or both step OK (lifted) and or_truthy_inv is
   preserved. Covers the scanned-OR rewrite and every unchanged instruction. *)
Triviality or_truthy_inst_step[local]:
  !fn fuel ctx inst s1 s2.
    ssa_form fn /\ fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 ==>
    (?e. step_inst fuel ctx inst s1 = Error e) \/
    (lift_result
       (state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
       (execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
       (execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
       (step_inst fuel ctx inst s1)
       (step_inst fuel ctx
          (ao_or_truthy_apply_inst
             (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) inst) s2) /\
     (!s1'. step_inst fuel ctx inst s1 = OK s1' ==>
        ?s2'. step_inst fuel ctx
                (ao_or_truthy_apply_inst
                   (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) inst)
                s2 = OK s2' /\
              or_truthy_inv
                (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                (fn_insts fn) s1' s2'))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = OR /\
            MEM inst.inst_id
              (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))`
  >- (fs[] >>
      drule_all scanned_or_step >>
      disch_then (qspecl_then [`fuel`,`ctx`] strip_assume_tac)
      >- (DISJ1_TAC >> metis_tac[]) >>
      DISJ2_TAC >> conj_tac
      >- gvs[lift_result_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s2'` >> simp[]) >>
  `~MEM inst.inst_id
      (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))` by
    (CCONTR_TAC >> `inst.inst_opcode = OR` by metis_tac[scanned_inst_shape] >>
     gvs[]) >>
  `ao_or_truthy_apply_inst
     (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) inst = inst` by
    simp[ao_or_truthy_apply_inst_def] >>
  simp[] >> DISJ2_TAC >>
  `result_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn)
     (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)` by
    (irule unchanged_result_equiv >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `result_equiv _ _ _` mp_tac >>
      simp[result_equiv_is_lift_result]) >>
  rpt strip_tac >>
  qpat_x_assum `result_equiv _ _ _` mp_tac >>
  simp[result_equiv_is_lift_result] >> strip_tac >>
  `?s2'. step_inst fuel ctx inst s2 = OK s2'` by
    (Cases_on `step_inst fuel ctx inst s2` >> gvs[lift_result_def]) >>
  qexists_tac `s2'` >> simp[] >>
  irule or_truthy_inv_step_unchanged >> metis_tac[]
QED

(* ===== exec_block structural helpers ===== *)

(* The rewrite leaves terminators unchanged (terminators are never ORs). *)
Triviality apply_terminator_id[local]:
  !ids inst. is_terminator inst.inst_opcode ==>
    ao_or_truthy_apply_inst ids inst = inst
Proof
  rw[ao_or_truthy_apply_inst_def] >> gvs[is_terminator_def]
QED

(* The rewrite preserves non-terminatorness (ASSIGN is not a terminator). *)
Triviality apply_nonterm[local]:
  !ids inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (ao_or_truthy_apply_inst ids inst).inst_opcode
Proof
  rw[ao_or_truthy_apply_inst_def] >> gvs[is_terminator_def]
QED

(* Updating vs_inst_idx on both sides preserves state_equiv. *)
Triviality state_equiv_idx_update[local]:
  !dead s1 s2 k.
    state_equiv dead s1 s2 ==>
    state_equiv dead (s1 with vs_inst_idx := k) (s2 with vs_inst_idx := k)
Proof
  rw[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* or_truthy_inv ignores vs_inst_idx (only reads vs_vars). *)
Triviality or_truthy_inv_idx_irrel[local]:
  !ids insts s1 s2 k m.
    or_truthy_inv ids insts (s1 with vs_inst_idx := k)
                            (s2 with vs_inst_idx := m) <=>
    or_truthy_inv ids insts s1 s2
Proof
  rw[or_truthy_inv_def, lookup_var_def]
QED

(* exec_block passes non-OK step results through unchanged. *)
Triviality exec_block_nonOK_passthrough[local]:
  !fuel ctx bb st r.
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = r /\
    (!s. r <> OK s) ==>
    exec_block fuel ctx bb st = r
Proof
  rpt strip_tac >> simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `r` >> gvs[]
QED

(* exec_block on a terminator that steps OK halts or returns OK. *)
Triviality exec_block_terminator_OK[local]:
  !fuel ctx bb st s1.
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    exec_block fuel ctx bb st = if s1.vs_halted then Halt s1 else OK s1
Proof
  rpt strip_tac >> simp[Once exec_block_def, get_instruction_def]
QED

(* exec_block on a non-terminator that steps OK continues at the next index. *)
Triviality exec_block_nonterm_OK[local]:
  !fuel ctx bb st s1.
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    ~is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    exec_block fuel ctx bb st =
      exec_block fuel ctx bb (s1 with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  rpt strip_tac >> simp[Once exec_block_def, get_instruction_def]
QED

(* Two-state non-OK lift: if the (matching) step results are lifted and the
   original is non-OK, both exec_blocks pass through and remain lifted. *)
Triviality nonOK_exec_block_lift2[local]:
  !fuel ctx bb1 bb2 st1 st2 R_ok R_term.
    st1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    st2.vs_inst_idx < LENGTH bb2.bb_instructions /\
    (!s. step_inst fuel ctx (EL st1.vs_inst_idx bb1.bb_instructions) st1 <> OK s) /\
    lift_result R_ok R_term R_term
      (step_inst fuel ctx (EL st1.vs_inst_idx bb1.bb_instructions) st1)
      (step_inst fuel ctx (EL st2.vs_inst_idx bb2.bb_instructions) st2) ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb1 st1) (exec_block fuel ctx bb2 st2) /\
    (!s. exec_block fuel ctx bb1 st1 <> OK s)
Proof
  rpt gen_tac >> strip_tac >>
  `exec_block fuel ctx bb1 st1 =
     step_inst fuel ctx (EL st1.vs_inst_idx bb1.bb_instructions) st1` by
    (irule exec_block_nonOK_passthrough >> simp[]) >>
  `!s. step_inst fuel ctx (EL st2.vs_inst_idx bb2.bb_instructions) st2 <> OK s` by
    (rpt strip_tac >>
     Cases_on `step_inst fuel ctx (EL st1.vs_inst_idx bb1.bb_instructions) st1` >>
     gvs[lift_result_def]) >>
  `exec_block fuel ctx bb2 st2 =
     step_inst fuel ctx (EL st2.vs_inst_idx bb2.bb_instructions) st2` by
    (irule exec_block_nonOK_passthrough >> simp[]) >>
  gvs[]
QED

(* ===== exec_block two-state simulation (measure induction) ===== *)

(* Walking a block and its rewritten image in lockstep: either the original
   errors, or the two exec_block results are lifted and or_truthy_inv is
   preserved on OK. The transform is a length-preserving 1:1 MAP so the two
   walks stay at the same index. *)
Triviality ao_or_truthy_exec_block_sim[local]:
  !fn bb bb2 n fuel ctx st1 st2.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    bb2.bb_instructions =
      MAP (ao_or_truthy_apply_inst
             (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))
          bb.bb_instructions /\
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) st1 st2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) st1 st2 /\
    n = LENGTH bb.bb_instructions - st1.vs_inst_idx ==>
    (?e. exec_block fuel ctx bb st1 = Error e) \/
    (lift_result
       (state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
       (execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
       (execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
       (exec_block fuel ctx bb st1)
       (exec_block fuel ctx bb2 st2) /\
     (!s1'. exec_block fuel ctx bb st1 = OK s1' ==>
        ?s2'. exec_block fuel ctx bb2 st2 = OK s2' /\
              or_truthy_inv
                (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                (fn_insts fn) s1' s2'))
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `st1.vs_inst_idx = st2.vs_inst_idx` by fs[state_equiv_def] >>
  `LENGTH bb2.bb_instructions = LENGTH bb.bb_instructions` by simp[] >>
  reverse (Cases_on `st1.vs_inst_idx < LENGTH bb.bb_instructions`)
  >- (DISJ1_TAC >> simp[Once exec_block_def, get_instruction_def]) >>
  qabbrev_tac `dinst = EL st1.vs_inst_idx bb.bb_instructions` >>
  `MEM dinst (fn_insts fn)` by
    (simp[Abbr `dinst`, fn_insts_def] >> irule mem_fn_insts_blocks >>
     qexists_tac `bb` >> simp[listTheory.EL_MEM]) >>
  `EL st1.vs_inst_idx bb2.bb_instructions =
     ao_or_truthy_apply_inst
       (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) dinst` by
    simp[Abbr `dinst`, listTheory.EL_MAP] >>
  qabbrev_tac `tinst = ao_or_truthy_apply_inst
                 (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) dinst` >>
  `st2.vs_inst_idx < LENGTH bb2.bb_instructions` by gvs[] >>
  `EL st2.vs_inst_idx bb2.bb_instructions = tinst` by metis_tac[] >>
  qspecl_then [`fn`,`fuel`,`ctx`,`dinst`,`st1`,`st2`] mp_tac or_truthy_inst_step >>
  impl_tac >- simp[] >>
  strip_tac >> pop_assum strip_assume_tac
  >- ((* original step errors *)
      DISJ1_TAC >>
      `exec_block fuel ctx bb st1 = step_inst fuel ctx dinst st1` by
        (irule exec_block_nonOK_passthrough >> simp[Abbr `dinst`]) >>
      gvs[]) >>
  reverse (Cases_on `?s1. step_inst fuel ctx dinst st1 = OK s1`)
  >- ((* non-OK: both pass through, lifted; OK clause vacuous *)
      `!s. step_inst fuel ctx dinst st1 <> OK s` by metis_tac[] >>
      `exec_block fuel ctx bb st1 = step_inst fuel ctx dinst st1` by
        (irule exec_block_nonOK_passthrough >> simp[Abbr `dinst`]) >>
      `!s. step_inst fuel ctx tinst st2 <> OK s` by
        (rpt strip_tac >> qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
         Cases_on `step_inst fuel ctx dinst st1` >> gvs[lift_result_def]) >>
      `exec_block fuel ctx bb2 st2 = step_inst fuel ctx tinst st2` by
        (irule exec_block_nonOK_passthrough >> gvs[]) >>
      DISJ2_TAC >> conj_tac
      >- gvs[Abbr `tinst`] >>
      rpt strip_tac >> gvs[]) >>
  fs[] >>
  rename1 `step_inst fuel ctx dinst st1 = OK s1` >>
  `?s2. step_inst fuel ctx tinst st2 = OK s2 /\
        or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                      (fn_insts fn) s1 s2` by metis_tac[] >>
  `state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2` by
    (qpat_x_assum `lift_result _ _ _ _ _` mp_tac >> gvs[lift_result_def]) >>
  `execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2` by
    metis_tac[state_equiv_implies_execution_equiv] >>
  `s1.vs_halted = s2.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
  reverse (Cases_on `is_terminator dinst.inst_opcode`)
  >- ((* non-terminator: continue at next index *)
      `~is_terminator tinst.inst_opcode` by metis_tac[apply_nonterm] >>
      `exec_block fuel ctx bb st1 =
         exec_block fuel ctx bb (s1 with vs_inst_idx := SUC st1.vs_inst_idx)` by
        (irule exec_block_nonterm_OK >> simp[Abbr `dinst`]) >>
      `exec_block fuel ctx bb2 st2 =
         exec_block fuel ctx bb2 (s2 with vs_inst_idx := SUC st2.vs_inst_idx)` by
        (irule exec_block_nonterm_OK >> gvs[]) >>
      ntac 2 (pop_assum (fn th => REWRITE_TAC[th])) >>
      last_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC st1.vs_inst_idx` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`fn`,`bb`,`bb2`,`fuel`,`ctx`,
        `s1 with vs_inst_idx := SUC st1.vs_inst_idx`,
        `s2 with vs_inst_idx := SUC st2.vs_inst_idx`] mp_tac) >>
      impl_tac
      >- (simp[] >> rpt conj_tac
          >- (irule state_equiv_idx_update >> simp[])
          >- simp[or_truthy_inv_idx_irrel]) >>
      simp[]) >>
  (* terminator: halt or OK, both sides agree *)
  `tinst = dinst` by metis_tac[apply_terminator_id] >>
  `exec_block fuel ctx bb st1 = if s1.vs_halted then Halt s1 else OK s1` by
    (irule exec_block_terminator_OK >> simp[Abbr `dinst`]) >>
  `exec_block fuel ctx bb2 st2 = if s2.vs_halted then Halt s2 else OK s2` by
    (irule exec_block_terminator_OK >> gvs[]) >>
  DISJ2_TAC >> gvs[] >>
  Cases_on `s1.vs_halted` >> gvs[lift_result_def]
QED

(* ===== eval_phis / run_block bridge ===== *)

(* The rewrite leaves PHI instructions untouched (OR <> PHI). *)
Triviality or_truthy_apply_phi_id[local]:
  !ids inst. inst.inst_opcode = PHI ==> ao_or_truthy_apply_inst ids inst = inst
Proof
  rw[ao_or_truthy_apply_inst_def]
QED

(* The rewrite preserves PHI-ness of the opcode. *)
Triviality or_truthy_apply_preserves_phi[local]:
  !ids inst.
    ((ao_or_truthy_apply_inst ids inst).inst_opcode = PHI) <=>
    (inst.inst_opcode = PHI)
Proof
  rw[ao_or_truthy_apply_inst_def]
QED

(* The MAP transform leaves the PHI prefix untouched, so eval_phis agrees on
   the original and mapped instruction lists. *)
Triviality or_truthy_eval_phis_eq[local]:
  !ids L s. eval_phis s (MAP (ao_or_truthy_apply_inst ids) L) = eval_phis s L
Proof
  gen_tac >> Induct >> simp[eval_phis_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[or_truthy_apply_phi_id, or_truthy_apply_preserves_phi, eval_phis_def] >>
  Cases_on `eval_one_phi s h` >> gvs[] >> PairCases_on `x` >> gvs[]
QED

Triviality or_truthy_phi_prefix_eq[local]:
  !ids L. phi_prefix_length (MAP (ao_or_truthy_apply_inst ids) L) =
          phi_prefix_length L
Proof
  gen_tac >> Induct >> rw[phi_prefix_length_def, or_truthy_apply_preserves_phi]
QED

(* eval_phis writes only PHI outputs, which are never scanned-OR outputs under
   SSA, so the OR-truthy invariant survives PHI evaluation. *)
Triviality or_truthy_inv_eval_phis[local]:
  !fn s1 s2 sp1 sp2 insts.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    (!inst. MEM inst insts ==> MEM inst (fn_insts fn)) /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 /\
    eval_phis s1 insts = OK sp1 /\
    eval_phis s2 insts = OK sp2 ==>
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) sp1 sp2
Proof
  rpt strip_tac >>
  simp[or_truthy_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM oinst (fn_insts fn)` >>
  `!phi. MEM phi insts /\ phi.inst_opcode = PHI ==> ~MEM out phi.inst_outputs` by
    (rpt strip_tac >>
     `MEM phi (fn_insts fn)` by metis_tac[] >>
     `oinst = phi` by metis_tac[ssa_output_unique] >>
     `oinst.inst_opcode = OR` by metis_tac[scanned_inst_shape] >>
     gvs[]) >>
  `FLOOKUP sp1.vs_vars out = FLOOKUP s1.vs_vars out` by
    (qspecl_then [`s1`, `insts`, `out`, `sp1`] mp_tac
       eval_phis_flookup_not_phi_output >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `FLOOKUP sp2.vs_vars out = FLOOKUP s2.vs_vars out` by
    (qspecl_then [`s2`, `insts`, `out`, `sp2`] mp_tac
       eval_phis_flookup_not_phi_output >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `lookup_var out sp1 = lookup_var out s1 /\
   lookup_var out sp2 = lookup_var out s2` by simp[lookup_var_def] >>
  qpat_x_assum `or_truthy_inv _ _ s1 s2` mp_tac >> simp[or_truthy_inv_def] >>
  metis_tac[]
QED

(* PHI operands are never dead vars (PHI is not a truthy instruction). *)
Triviality phi_operands_not_dead[local]:
  !fn bb.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks ==>
    EVERY (\inst. inst.inst_opcode = PHI ==>
             !x. MEM (Var x) inst.inst_operands ==>
               x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn)
          bb.bb_instructions
Proof
  rpt strip_tac >> simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qexists_tac `bb` >> simp[]) >>
  `x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn` suffices_by gvs[] >>
  irule nontruthy_operand_not_dead >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `inst` >> gvs[is_truthy_inst_def]
QED

(* ===== run_block-level simulation ===== *)

(* TOP-LEVEL: run_block simulation up to dead vars under or_truthy_inv. *)
Theorem ao_or_truthy_block_sim:
  !fn bb bb2 fuel ctx s1 s2.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    bb2.bb_instructions =
      MAP (ao_or_truthy_apply_inst
             (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))
          bb.bb_instructions /\
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 ==>
    (?e. run_block fuel ctx bb s1 = Error e) \/
    lift_result
      (state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
      (execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
      (execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn))
      (run_block fuel ctx bb s1) (run_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  `!s. eval_phis s bb2.bb_instructions = eval_phis s bb.bb_instructions` by
    simp[or_truthy_eval_phis_eq] >>
  `phi_prefix_length bb2.bb_instructions = phi_prefix_length bb.bb_instructions` by
    simp[or_truthy_phi_prefix_eq] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==>
              x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn)
          bb.bb_instructions` by (irule phi_operands_not_dead >> simp[]) >>
  simp[run_block_def] >>
  qpat_x_assum `!s. eval_phis s bb2.bb_instructions = _` (fn th => simp[th]) >>
  qpat_x_assum `phi_prefix_length bb2.bb_instructions = _` (fn th => simp[th]) >>
  `(?sp1. eval_phis s1 bb.bb_instructions = OK sp1) \/
   (?e. eval_phis s1 bb.bb_instructions = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  pop_assum strip_assume_tac
  >- (rename1 `eval_phis s1 bb.bb_instructions = OK sp1` >>
      qspecl_then [`s1`, `s2`,
                   `ao_or_truthy_dead_vars (dfg_build_function fn) fn`,
                   `bb.bb_instructions`, `sp1`]
        mp_tac eval_phis_state_equiv >>
      impl_tac >- simp[] >> strip_tac >>
      rename1 `eval_phis s2 bb.bb_instructions = OK sp2` >>
      `or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                     (fn_insts fn) sp1 sp2` by
        (qspecl_then [`fn`, `s1`, `s2`, `sp1`, `sp2`, `bb.bb_instructions`]
           mp_tac or_truthy_inv_eval_phis >>
         impl_tac
         >- (simp[] >> rpt strip_tac >> simp[fn_insts_def] >>
             irule mem_fn_insts_blocks >> qexists_tac `bb` >> simp[])
         >> simp[]) >>
      qpat_x_assum `eval_phis s1 bb.bb_instructions = OK sp1`
        (fn th => simp[th]) >>
      qpat_x_assum `eval_phis s2 bb.bb_instructions = OK sp2`
        (fn th => simp[th]) >>
      qspecl_then [`fn`, `bb`, `bb2`,
        `LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions`,
        `fuel`, `ctx`,
        `sp1 with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
        `sp2 with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
        mp_tac ao_or_truthy_exec_block_sim >>
      impl_tac
      >- (simp[] >> rpt conj_tac
          >- (irule state_equiv_idx_update >> simp[])
          >- gvs[or_truthy_inv_idx_irrel]) >>
      strip_tac >> pop_assum strip_assume_tac
      >- (DISJ1_TAC >> metis_tac[])
      >> (DISJ2_TAC >> first_assum ACCEPT_TAC))
  >> simp[]
QED

(* TOP-LEVEL: or_truthy_inv preserved across OK run_block. *)
Theorem ao_or_truthy_block_ok_inv:
  !fn bb bb2 fuel ctx s1 s2 s1' s2'.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    bb2.bb_instructions =
      MAP (ao_or_truthy_apply_inst
             (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))
          bb.bb_instructions /\
    state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn) fn) s1 s2 /\
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1 s2 /\
    run_block fuel ctx bb s1 = OK s1' /\
    run_block fuel ctx bb2 s2 = OK s2' ==>
    or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                  (fn_insts fn) s1' s2'
Proof
  rpt strip_tac >>
  `!s. eval_phis s bb2.bb_instructions = eval_phis s bb.bb_instructions` by
    simp[or_truthy_eval_phis_eq] >>
  `phi_prefix_length bb2.bb_instructions = phi_prefix_length bb.bb_instructions` by
    simp[or_truthy_phi_prefix_eq] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==>
              x NOTIN ao_or_truthy_dead_vars (dfg_build_function fn) fn)
          bb.bb_instructions` by (irule phi_operands_not_dead >> simp[]) >>
  `(?sp1. eval_phis s1 bb.bb_instructions = OK sp1) \/
   (?e. eval_phis s1 bb.bb_instructions = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  pop_assum strip_assume_tac
  >| [ALL_TAC,
      qpat_x_assum `run_block fuel ctx bb s1 = OK s1'` mp_tac >>
      simp[run_block_def]] >>
  rename1 `eval_phis s1 bb.bb_instructions = OK sp1` >>
  qspecl_then [`s1`, `s2`,
               `ao_or_truthy_dead_vars (dfg_build_function fn) fn`,
               `bb.bb_instructions`, `sp1`]
    mp_tac eval_phis_state_equiv >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `eval_phis s2 bb.bb_instructions = OK sp2` >>
  `or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))
                 (fn_insts fn) sp1 sp2` by
    (qspecl_then [`fn`, `s1`, `s2`, `sp1`, `sp2`, `bb.bb_instructions`]
       mp_tac or_truthy_inv_eval_phis >>
     impl_tac
     >- (simp[] >> rpt strip_tac >> simp[fn_insts_def] >>
         irule mem_fn_insts_blocks >> qexists_tac `bb` >> simp[])
     >> simp[]) >>
  `exec_block fuel ctx bb
     (sp1 with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s1'` by
    (qpat_x_assum `run_block fuel ctx bb s1 = OK s1'` mp_tac >>
     simp[run_block_def] >>
     qpat_assum `eval_phis s1 bb.bb_instructions = OK sp1`
       (fn th => simp[th])) >>
  `exec_block fuel ctx bb2
     (sp2 with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s2'` by
    (qpat_x_assum `run_block fuel ctx bb2 s2 = OK s2'` mp_tac >>
     simp[run_block_def] >>
     qpat_x_assum `!s. eval_phis s bb2.bb_instructions = _` (fn th => simp[th]) >>
     qpat_x_assum `phi_prefix_length bb2.bb_instructions = _`
       (fn th => simp[th]) >>
     qpat_assum `eval_phis s2 bb.bb_instructions = OK sp2`
       (fn th => simp[th])) >>
  qspecl_then [`fn`, `bb`, `bb2`,
    `LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions`,
    `fuel`, `ctx`,
    `sp1 with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `sp2 with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
    mp_tac ao_or_truthy_exec_block_sim >>
  impl_tac
  >- (simp[] >> rpt conj_tac
      >- (irule state_equiv_idx_update >> simp[])
      >- gvs[or_truthy_inv_idx_irrel]) >>
  strip_tac >> pop_assum strip_assume_tac
  >- gvs[] >>
  qpat_x_assum `!t. exec_block fuel ctx bb _ = OK t ==> _`
    (qspec_then `s1'` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[]
QED

val _ = export_theory();
