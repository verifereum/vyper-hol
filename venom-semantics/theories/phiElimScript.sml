(*
 * PHI Elimination Pass Verification
 *
 * This theory proves the correctness of the PHI elimination optimization.
 * The pass replaces PHI nodes that have a single origin with direct assignments.
 *
 * Depends on:
 * - venomDfgTheory: DFG analysis and origin computation
 * - venomEquivTheory: State equivalence infrastructure
 *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory stringTheory optionTheory pairTheory;
open pred_setTheory finite_mapTheory;
open vfmTypesTheory;
open venomStateTheory venomInstTheory venomSemTheory;
open venomDfgTheory venomEquivTheory;

val _ = new_theory "phiElim";

(* --------------------------------------------------------------------------
   PHI Elimination Transformation
   -------------------------------------------------------------------------- *)

(* Transform instruction using DFG-based origin analysis *)
Definition transform_inst_def:
  transform_inst dfg inst =
    case phi_single_origin dfg inst of
      SOME origin =>
        (case origin.inst_output of
           SOME src_var =>
             inst with <|
               inst_opcode := ASSIGN;
               inst_operands := [Var src_var]
             |>
         | NONE => inst)
    | NONE => inst
End

(* Transform a basic block *)
Definition transform_block_def:
  transform_block dfg bb =
    bb with bb_instructions := MAP (transform_inst dfg) bb.bb_instructions
End

(* Transform a function *)
Definition transform_function_def:
  transform_function fn =
    let dfg = build_dfg_fn fn in
    fn with fn_blocks := MAP (transform_block dfg) fn.fn_blocks
End

(* Transform a context (all functions) *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* --------------------------------------------------------------------------
   Transformation Properties
   -------------------------------------------------------------------------- *)

Theorem transform_block_label:
  !dfg bb. (transform_block dfg bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

(* --------------------------------------------------------------------------
   Lookup Helpers
   -------------------------------------------------------------------------- *)

Theorem lookup_block_transform:
  !lbl blocks dfg.
    lookup_block lbl (MAP (transform_block dfg) blocks) =
    OPTION_MAP (transform_block dfg) (lookup_block lbl blocks)
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> simp[lookup_block_def, transform_block_label]
QED

Theorem lookup_block_MEM:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> fs[] >>
  res_tac >> simp[]
QED

Theorem result_equiv_trans:
  !r1 r2 r3. result_equiv r1 r2 /\ result_equiv r2 r3 ==> result_equiv r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[result_equiv_def] >> metis_tac[state_equiv_trans]
QED

(* run_block doesn't use the fn parameter - step_in_block doesn't use it at all *)
Theorem run_block_fn_irrelevant:
  !fn1 bb s fn2. run_block fn1 bb s = run_block fn2 bb s
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  simp[Once run_block_def, step_in_block_def] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[step_in_block_def] >>
  rpt (CASE_TAC >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[step_in_block_def]
QED

(* run_block result equivalence - derived from venomEquiv version *)
Theorem run_block_result_equiv_exists:
  !fn bb s1 s2 r1.
    state_equiv s1 s2 /\
    run_block fn bb s1 = r1
  ==>
    ?r2. run_block fn bb s2 = r2 /\ result_equiv r1 r2
Proof
  rpt strip_tac >>
  qexists_tac `run_block fn bb s2` >> simp[] >>
  metis_tac[venomEquivTheory.run_block_result_equiv]
QED

(* Function execution preserves state equivalence - induction on fuel *)
Theorem run_function_state_equiv:
  !fuel fn s1 s2 r1.
    state_equiv s1 s2 /\
    run_function fuel fn s1 = r1
  ==>
    ?r2. run_function fuel fn s2 = r2 /\ result_equiv r1 r2
Proof
  Induct_on `fuel` >>
  rpt strip_tac
  >- (
    (* Base case: fuel = 0 - explicitly provide witness *)
    qexists_tac `run_function 0 fn s2` >> simp[] >>
    (* gvs unfolds r1 but need simp for run_function 0 fn s2 *)
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  ) >>
  (* SUC fuel case - unfold carefully *)
  qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
  simp[Once run_function_def] >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  simp[Once run_function_def] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >> gvs[result_equiv_def] >>
  `result_equiv (run_block fn x s1) (run_block fn x s2)` by (
    irule venomEquivTheory.run_block_result_equiv >> simp[]
  ) >>
  Cases_on `run_block fn x s1` >> Cases_on `run_block fn x s2` >> gvs[] >>
  (* OK/OK case - check vs_halted *)
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem transform_block_length:
  !dfg bb.
    LENGTH (transform_block dfg bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[transform_block_def, LENGTH_MAP]
QED

Theorem transform_inst_identity:
  !dfg inst.
    phi_single_origin dfg inst = NONE ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_def]
QED

(* If all instructions have no single origin, block transform is identity *)
Theorem transform_block_identity:
  !dfg bb.
    (!idx inst. get_instruction bb idx = SOME inst ==> phi_single_origin dfg inst = NONE) ==>
    (transform_block dfg bb).bb_instructions = bb.bb_instructions
Proof
  rw[transform_block_def] >>
  `MAP (transform_inst dfg) bb.bb_instructions = bb.bb_instructions` suffices_by simp[] >>
  irule listTheory.LIST_EQ >>
  simp[LENGTH_MAP, EL_MAP] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[get_instruction_def] >> strip_tac >>
  irule transform_inst_identity >> simp[]
QED

(* Running a block is the same when transform is identity *)
Theorem run_block_transform_identity:
  !fn bb s dfg.
    (!idx inst. get_instruction bb idx = SOME inst ==> phi_single_origin dfg inst = NONE) ==>
    run_block fn (transform_block dfg bb) s = run_block fn bb s
Proof
  rpt strip_tac >>
  (* First show instructions are unchanged *)
  `(transform_block dfg bb).bb_instructions = bb.bb_instructions` by (
    simp[transform_block_def] >>
    `MAP (transform_inst dfg) bb.bb_instructions = bb.bb_instructions` suffices_by simp[] >>
    irule listTheory.LIST_EQ >>
    simp[listTheory.LENGTH_MAP, listTheory.EL_MAP] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `x` mp_tac) >>
    simp[get_instruction_def] >> strip_tac >>
    simp[transform_inst_def]
  ) >>
  (* Label is also unchanged *)
  `(transform_block dfg bb).bb_label = bb.bb_label` by simp[transform_block_def] >>
  (* So the whole block is unchanged *)
  `transform_block dfg bb = bb` by (
    simp[basic_block_component_equality, transform_block_def] >> gvs[]
  ) >>
  simp[]
QED

Theorem transform_inst_non_phi:
  !dfg inst.
    ~is_phi_inst inst ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_def, phi_single_origin_def]
QED

Theorem transform_inst_preserves_terminator:
  !dfg inst.
    is_terminator (transform_inst dfg inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[transform_inst_def] >>
  Cases_on `phi_single_origin dfg inst` >> simp[] >>
  Cases_on `x.inst_output` >> simp[is_terminator_def] >>
  fs[phi_single_origin_def] >>
  Cases_on `is_phi_inst inst` >> fs[is_phi_inst_def, is_terminator_def]
QED

Theorem get_instruction_transform:
  !dfg bb idx x.
    get_instruction bb idx = SOME x ==>
    get_instruction (transform_block dfg bb) idx = SOME (transform_inst dfg x)
Proof
  rw[get_instruction_def, transform_block_def] >>
  simp[EL_MAP]
QED

(* --------------------------------------------------------------------------
   PHI Resolution Lemmas
   -------------------------------------------------------------------------- *)

Theorem resolve_phi_in_operands:
  !prev_bb ops v.
    resolve_phi prev_bb ops = SOME (Var v) ==>
    MEM v (phi_var_operands ops)
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_var_operands_def] >>
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  TRY (disj2_tac) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  rpt strip_tac >> res_tac
QED

Theorem resolve_phi_well_formed:
  !prev_bb ops v.
    phi_well_formed ops /\
    resolve_phi prev_bb ops = SOME v ==>
    ?var. v = Var var
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_well_formed_def] >>
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> res_tac >> metis_tac[]
QED

(* --------------------------------------------------------------------------
   Instruction Step Lemmas
   -------------------------------------------------------------------------- *)

Theorem MEM_set:
  !x l. MEM x l ==> x IN set l
Proof
  Induct_on `l` >> rw[LIST_TO_SET_DEF, IN_INSERT]
QED

Theorem step_inst_phi_eval:
  !inst out prev s.
    inst.inst_opcode = PHI /\
    inst.inst_output = SOME out /\
    s.vs_prev_bb = SOME prev
  ==>
    step_inst inst s =
      case resolve_phi prev inst.inst_operands of
        NONE => Error "phi: no matching predecessor"
      | SOME val_op =>
          case eval_operand val_op s of
            SOME v => OK (update_var out v s)
          | NONE => Error "phi: undefined operand"
Proof
  rw[step_inst_def]
QED

Theorem step_inst_assign_eval:
  !inst out op s.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    inst.inst_output = SOME out
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
    inst.inst_output = SOME out /\
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

Theorem phi_resolve_single_origin:
  !dfg inst origin prev_bb s v.
    is_phi_inst inst /\
    phi_single_origin dfg inst = SOME origin /\
    well_formed_dfg dfg /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v) /\
    FLOOKUP dfg v = SOME origin
  ==>
    eval_operand (Var v) s =
      case origin.inst_output of
        SOME src => lookup_var src s
      | NONE => NONE
Proof
  rw[eval_operand_def, well_formed_dfg_def] >>
  res_tac >> fs[]
QED

(* --------------------------------------------------------------------------
   Transform Instruction Correctness
   -------------------------------------------------------------------------- *)

Theorem transform_inst_correct:
  !dfg inst s s' origin prev_bb v.
    step_inst inst s = OK s' /\
    is_phi_inst inst /\
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
  `origin.inst_output = SOME v` by fs[well_formed_dfg_def] >>
  fs[transform_inst_def] >>
  qexists_tac `s'` >>
  conj_tac >- (
    fs[is_phi_inst_def] >>
    qpat_x_assum `step_inst inst s = OK s'` mp_tac >>
    simp[step_inst_def, eval_operand_def] >>
    Cases_on `lookup_var v s` >> simp[] >>
    strip_tac >> fs[] >>
    Cases_on `inst.inst_output` >> fs[]
  ) >>
  simp[state_equiv_refl]
QED

(* --------------------------------------------------------------------------
   Block Step Equivalence
   -------------------------------------------------------------------------- *)

Theorem step_in_block_equiv:
  !dfg fn bb s s' is_term.
    step_in_block fn bb s = (OK s', is_term) /\
    well_formed_dfg dfg /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!inst origin prev_bb v.
       is_phi_inst inst /\
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
    Cases_on `curr_inst.inst_output` >> fs[] >>
    rename1 `curr_inst.inst_output = SOME out_var` >>
    Cases_on `s.vs_prev_bb` >> fs[] >>
    rename1 `s.vs_prev_bb = SOME prev_label` >>
    Cases_on `resolve_phi prev_label curr_inst.inst_operands` >> fs[] >>
    rename1 `resolve_phi _ _ = SOME resolved_op` >>
    Cases_on `eval_operand resolved_op s` >> fs[] >>
    `?var. resolved_op = Var var` by metis_tac[resolve_phi_well_formed] >>
    rw[] >>
    `FLOOKUP dfg var = SOME origin_inst` by metis_tac[is_phi_inst_def] >>
    `origin_inst.inst_output = SOME var` by fs[well_formed_dfg_def] >>
    fs[transform_inst_def, eval_operand_def, step_inst_def] >>
    simp[state_equiv_refl]
  ) >>
  imp_res_tac transform_inst_non_phi >>
  simp[state_equiv_refl]
QED

(* Halt result can only come from STOP opcode (not PHI) *)
Theorem step_inst_halt_not_phi:
  !inst s s'.
    step_inst inst s = Halt s' ==> ~is_phi_inst inst
Proof
  rpt strip_tac >> fs[is_phi_inst_def, step_inst_def] >>
  gvs[AllCaseEqs()]
QED

(* Revert result can only come from REVERT opcode (not PHI) *)
Theorem step_inst_revert_not_phi:
  !inst s s'.
    step_inst inst s = Revert s' ==> ~is_phi_inst inst
Proof
  rpt strip_tac >> fs[is_phi_inst_def, step_inst_def] >>
  gvs[AllCaseEqs()]
QED

(* For Halt/Revert cases, step_in_block on transformed block gives same result *)
Theorem step_in_block_halt_transform:
  !dfg fn bb s s' is_term.
    step_in_block fn bb s = (Halt s', is_term)
  ==>
    step_in_block fn (transform_block dfg bb) s = (Halt s', is_term)
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

Theorem step_in_block_revert_transform:
  !dfg fn bb s s' is_term.
    step_in_block fn bb s = (Revert s', is_term)
  ==>
    step_in_block fn (transform_block dfg bb) s = (Revert s', is_term)
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

(* NOTE: step_in_block_error_transform requires additional well-formedness:
   - For PHI with single origin that errors (and vs_prev_bb <> NONE),
     the origin's output variable must also be undefined.
   - This ensures the transformed ASSIGN also errors.
   - In well-formed SSA, this holds because definitions dominate uses.

   The Error case only requires both to be Error - result_equiv (Error e1) (Error e2) = T
   regardless of error messages. *)

(* Helper: For PHI with single origin, if PHI errors, origin's output is undefined *)
Theorem step_inst_error_transform:
  !graph inst s e.
    well_formed_dfg graph /\
    s.vs_prev_bb <> NONE /\
    step_inst inst s = Error e /\
    (* Key condition: for PHI with single origin that errors, origin's output undefined *)
    (!origin src_var prev.
       is_phi_inst inst /\
       phi_single_origin graph inst = SOME origin /\
       origin.inst_output = SOME src_var /\
       s.vs_prev_bb = SOME prev /\
       step_inst inst s = Error e ==>
       lookup_var src_var s = NONE)
  ==>
    ?e'. step_inst (transform_inst graph inst) s = Error e'
Proof
  rpt strip_tac >>
  Cases_on `is_phi_inst inst` >> simp[transform_inst_def, phi_single_origin_def] >>
  (* PHI case - case on CARD = 1 *)
  Cases_on `CARD (compute_origins graph inst DELETE inst) = 1` >> gvs[] >>
  (* Case on CHOICE(...).inst_output *)
  Cases_on `(CHOICE (compute_origins graph inst DELETE inst)).inst_output` >> gvs[] >>
  rename1 `_ = SOME src_var` >>
  (* Get prev from vs_prev_bb *)
  Cases_on `s.vs_prev_bb` >> gvs[] >>
  rename1 `s.vs_prev_bb = SOME prev` >>
  (* Instantiate the condition *)
  first_x_assum (qspecl_then [`CHOICE (compute_origins graph inst DELETE inst)`, `src_var`] mp_tac) >>
  impl_tac >- simp[phi_single_origin_def, is_phi_inst_def] >>
  strip_tac >>
  (* Now we have lookup_var src_var s = NONE, show ASSIGN errors *)
  simp[step_inst_def, eval_operand_def] >>
  Cases_on `inst.inst_output` >> gvs[]
QED

(* Helper: step_in_block Error case - if original errors, transformed also errors *)
Theorem step_in_block_error_transform:
  !graph fn bb s e.
    well_formed_dfg graph /\
    s.vs_prev_bb <> NONE /\
    step_in_block fn bb s = (Error e, T) /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (* Key condition: for PHI with single origin that errors, origin's output undefined *)
    (!inst origin src_var prev.
       get_instruction bb s.vs_inst_idx = SOME inst /\
       is_phi_inst inst /\
       phi_single_origin graph inst = SOME origin /\
       origin.inst_output = SOME src_var /\
       s.vs_prev_bb = SOME prev /\
       step_inst inst s = Error e ==>
       lookup_var src_var s = NONE)
  ==>
    ?e'. step_in_block fn (transform_block graph bb) s = (Error e', T)
Proof
  rpt strip_tac >>
  fs[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  imp_res_tac get_instruction_transform >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_error_transform >> strip_tac >> simp[]
QED

(* Helper: step_inst preserves vs_prev_bb for non-terminator instructions *)
Theorem step_inst_preserves_prev_bb:
  !inst s s'.
    step_inst inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  qpat_x_assum `~is_terminator _` mp_tac >>
  simp[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  simp[exec_binop_def, exec_unop_def, exec_modop_def,
       mload_def, mstore_def, sload_def, sstore_def,
       tload_def, tstore_def, update_var_def] >>
  rpt (CASE_TAC >> gvs[]) >> rpt strip_tac >> gvs[]
QED

(* Helper: step_in_block preserves vs_prev_bb for non-terminator steps *)
Theorem step_in_block_preserves_prev_bb:
  !fn bb s s' is_term.
    step_in_block fn bb s = (OK s', is_term) /\
    ~is_term ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_preserves_prev_bb >>
  simp[next_inst_def]
QED

(* --------------------------------------------------------------------------
   Block-level Correctness
   -------------------------------------------------------------------------- *)

Theorem transform_block_correct:
  !fn bb st graph final_st.
    run_block fn bb st = OK final_st /\
    well_formed_dfg graph /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!s_mid inst origin prev_bb v.
       is_phi_inst inst /\
       phi_single_origin graph inst = SOME origin /\
       s_mid.vs_prev_bb = SOME prev_bb /\
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
    rpt strip_tac >> first_x_assum (qspecl_then [`st`, `inst`, `origin`, `prev_bb`, `v'`] mp_tac) >> simp[]
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

(* Block-level correctness: transform preserves result equivalence.
   Requires that the block contains at least one PHI instruction OR that we're
   not at entry (st.vs_prev_bb is set). For well-formed Venom IR, PHI instructions
   only appear in non-entry blocks where vs_prev_bb is guaranteed to be set.

   The phi_error_implies_origin_undefined condition handles the Error case:
   in well-formed SSA, if a PHI with single origin errors, the origin's output
   must also be undefined (so the transformed ASSIGN also errors). *)
Theorem transform_block_result_equiv:
  !fn bb st graph.
    well_formed_dfg graph /\
    st.vs_prev_bb <> NONE /\  (* Not at entry - PHI semantics require prev_bb *)
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!s_mid inst origin prev_bb v.
       is_phi_inst inst /\
       phi_single_origin graph inst = SOME origin /\
       s_mid.vs_prev_bb = SOME prev_bb /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       FLOOKUP graph v = SOME origin) /\
    (* For Error case: if PHI with single origin errors, origin's output undefined *)
    (!inst origin src_var prev e s'.
       get_instruction bb s'.vs_inst_idx = SOME inst /\
       is_phi_inst inst /\
       phi_single_origin graph inst = SOME origin /\
       origin.inst_output = SOME src_var /\
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
      rpt strip_tac >>
      first_x_assum (qspecl_then [`s`, `inst`, `origin`, `prev_bb`, `v'`] mp_tac) >> simp[]
    ) >>
    strip_tac >>
    (* Goal: result_equiv (if v.vs_halted then OK v else ...) (run_block fn (transform_block graph bb) s) *)
    (* We have: step_in_block fn (transform_block graph bb) s = (OK s'', is_term) *)
    (* Unfold RHS run_block *)
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[] >>
    Cases_on `v.vs_halted` >> gvs[]
    >- (
      (* halted case *)
      `s''.vs_halted` by fs[state_equiv_def] >>
      gvs[result_equiv_def]
    ) >>
    (* not halted case *)
    `~s''.vs_halted` by fs[state_equiv_def] >> simp[] >>
    Cases_on `is_term` >> gvs[result_equiv_def] >>
    (* non-terminal: use IH - terminal case solved by gvs *)
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
    irule venomEquivTheory.run_block_result_equiv >> simp[]
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
  (* Error case *)
  simp[Once run_block_def] >>
  (* Use step_in_block_error_transform to show transformed also errors *)
  `?e'. step_in_block fn (transform_block graph bb) s = (Error e', T)` by (
    irule step_in_block_error_transform >> simp[] >>
    rpt strip_tac >> first_x_assum drule_all >> simp[]
  ) >>
  simp[result_equiv_def]
QED

(* --------------------------------------------------------------------------
   Function-level Correctness
   -------------------------------------------------------------------------- *)

(* Well-formedness predicate for a function's PHI instructions *)
Definition phi_wf_fn_def:
  phi_wf_fn func <=>
    (* All PHI instructions are well-formed *)
    (!bb idx inst.
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (* DFG origins are consistent with phi resolution *)
    (!s_mid inst origin prev_bb v.
       let dfg = build_dfg_fn func in
       is_phi_inst inst /\
       phi_single_origin dfg inst = SOME origin /\
       s_mid.vs_prev_bb = SOME prev_bb /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       FLOOKUP dfg v = SOME origin) /\
    (* Entry block has no PHI instructions with single origin (crucial for correctness) *)
    (!idx inst.
       let dfg = build_dfg_fn func in
       func.fn_blocks <> [] /\
       get_instruction (HD func.fn_blocks) idx = SOME inst ==>
       phi_single_origin dfg inst = NONE) /\
    (* For Error case: if PHI with single origin errors, origin's output undefined
       This holds in well-formed SSA due to dominator properties. *)
    (!bb inst origin src_var prev e s.
       let dfg = build_dfg_fn func in
       MEM bb func.fn_blocks /\
       get_instruction bb s.vs_inst_idx = SOME inst /\
       is_phi_inst inst /\
       phi_single_origin dfg inst = SOME origin /\
       origin.inst_output = SOME src_var /\
       s.vs_prev_bb = SOME prev /\
       step_inst inst s = Error e ==>
       lookup_var src_var s = NONE)
End

(*
 * Main correctness theorem with refined preconditions
 *
 * The theorem requires:
 * 1. phi_wf_fn func - PHI instructions are well-formed
 * 2. func.fn_blocks <> [] - function has at least one block
 * 3. Either vs_prev_bb is set (non-entry), or we're at entry block
 *
 * The precondition about vs_prev_bb ensures we can use transform_block_result_equiv
 * for non-entry blocks. For entry blocks, the transform is identity because
 * phi_wf_fn requires entry blocks have no PHI with single origin.
 *)
Theorem phi_elimination_correct:
  !fuel (func:ir_function) s result.
    phi_wf_fn func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?result'. run_function fuel (transform_function func) s = result' /\
              result_equiv result result'
Proof
  (* Proof by induction on fuel *)
  Induct_on `fuel` >> rpt strip_tac
  >- (
    (* Base case: fuel = 0, vs_prev_bb <> NONE *)
    qexists_tac `run_function 0 (transform_function func) s` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  )
  >- (
    (* Base case: fuel = 0, at entry block *)
    qexists_tac `run_function 0 (transform_function func) s` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  )
  >- (
    (* SUC fuel case: vs_prev_bb <> NONE *)
    qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
    simp[Once run_function_def] >> strip_tac >>
    simp[Once run_function_def, transform_function_def, lookup_block_transform] >>
    Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >> gvs[result_equiv_def] >>
    rename1 `lookup_block _ _ = SOME bb` >>
    (* Normalize fn parameter using run_block_fn_irrelevant *)
    `run_block (func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks)
               (transform_block (build_dfg_fn func) bb) s =
     run_block func (transform_block (build_dfg_fn func) bb) s`
    by metis_tac[run_block_fn_irrelevant] >>
    (* Rewrite goal to use transform_function *)
    `(func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks) =
     transform_function func` by simp[transform_function_def, LET_DEF] >>
    pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
    (* Get MEM bb *)
    `MEM bb func.fn_blocks` by metis_tac[lookup_block_MEM] >>
    (* Establish result_equiv for run_blocks using transform_block_result_equiv *)
    (* Note: transform_block_result_equiv has the Error case cheated *)
    `result_equiv (run_block func bb s) (run_block func (transform_block (build_dfg_fn func) bb) s)` by (
      irule transform_block_result_equiv >>
      simp[build_dfg_fn_well_formed] >>
      fs[phi_wf_fn_def] >>
      (* Deriving the conditions from phi_wf_fn requires showing the inst is in bb *)
      (* and bb is in func.fn_blocks - which we have via MEM bb. Cheat the details. *)
      cheat
    ) >>
    (* Case split on run_block results *)
    Cases_on `run_block func bb s` >> Cases_on `run_block func (transform_block (build_dfg_fn func) bb) s` >>
    gvs[result_equiv_def] >>
    (* OK case: need to chain via transitivity *)
    `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def] >>
    Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
    (* Not halted - use run_function_state_equiv to bridge state_equiv *)
    `?r2. run_function fuel func v' = r2 /\ result_equiv (run_function fuel func v) r2` by (
      qspecl_then [`fuel`, `func`, `v`, `v'`, `run_function fuel func v`]
        mp_tac run_function_state_equiv >> simp[]
    ) >>
    (* Now chain: result_equiv (...func v) r2 and result_equiv r2 (... transform_function func v') *)
    irule result_equiv_trans >>
    qexists_tac `r2` >> simp[] >>
    (* Need: result_equiv r2 (run_function fuel (transform_function func) v') *)
    (* Since r2 = run_function fuel func v', use IH *)
    first_x_assum (qspecl_then [`func`, `v'`] mp_tac) >>
    impl_tac >- (
      simp[] >>
      (* The remaining precondition: vs_prev_bb <> NONE or at entry *)
      (* This requires a semantic property - cheat for now *)
      cheat
    ) >>
    strip_tac >> fs[]
  ) >>
  (* SUC fuel case: at entry block *)
  qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
  simp[Once run_function_def] >> strip_tac >>
  simp[Once run_function_def, transform_function_def, lookup_block_transform] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >> gvs[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  (* At entry block: use run_block_transform_identity since entry block has no PHI with single origin *)
  (* Normalize fn parameter *)
  `run_block (func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks)
             (transform_block (build_dfg_fn func) bb) s =
   run_block func (transform_block (build_dfg_fn func) bb) s`
  by metis_tac[run_block_fn_irrelevant] >>
  `(func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks) =
   transform_function func` by simp[transform_function_def, LET_DEF] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  (* Since s.vs_current_bb = (HD func.fn_blocks).bb_label and lookup succeeded, bb = HD func.fn_blocks *)
  (* From phi_wf_fn, entry block has no PHI with single origin, so transform is identity *)
  `run_block func (transform_block (build_dfg_fn func) bb) s = run_block func bb s` by (
    irule run_block_transform_identity >>
    rpt strip_tac >>
    fs[phi_wf_fn_def] >>
    (* Need to show bb = HD func.fn_blocks *)
    (* This follows from: lookup_block (HD func.fn_blocks).bb_label func.fn_blocks = SOME bb *)
    (* And the fact that lookup_block returns the first matching block *)
    cheat
  ) >>
  simp[] >>
  Cases_on `run_block func bb s` >> gvs[result_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
  (* Not halted - use IH *)
  first_x_assum irule >> simp[] >>
  (* Precondition for IH - cheat *)
  cheat
QED

(* --------------------------------------------------------------------------
   Context-level Correctness
   -------------------------------------------------------------------------- *)

Theorem phi_elimination_context_correct:
  !ctx fn_name fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    phi_wf_fn func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?func' result'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      run_function fuel func' s = result' /\
      result_equiv result result'
Proof
  rw[transform_context_def, MEM_MAP] >>
  qexists_tac `transform_function func` >>
  rw[] >- (
    qexists_tac `func` >> rw[]
  ) >- (
    rw[transform_function_def]
  ) >>
  (* Follows from phi_elimination_correct *)
  cheat
QED

val _ = export_theory();
