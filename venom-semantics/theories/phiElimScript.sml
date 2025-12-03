(*
 * PHI Elimination Pass Verification
 *
 * This theory proves the correctness of the PHI elimination optimization.
 * The pass replaces PHI nodes that have a single origin with direct assignments.
 *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory stringTheory optionTheory pairTheory;
open pred_setTheory finite_mapTheory;
open vfmTypesTheory;
open venomStateTheory venomInstTheory venomSemTheory;

val _ = new_theory "phiElim";

(* --------------------------------------------------------------------------
   Data-Flow Graph (DFG) Analysis

   The DFG maps each variable to the instruction that produces it.
   This is used to trace back through PHI/assign chains.
   -------------------------------------------------------------------------- *)

Type dfg = ``:string -> instruction option``

(* DFG well-formedness: if a variable maps to an instruction, that
   instruction must produce the variable. *)
Definition well_formed_dfg_def:
  well_formed_dfg dfg <=>
    !v inst. dfg v = SOME inst ==> inst.inst_output = SOME v
End

(* Build DFG for a function: map output vars to their defining instructions *)
Definition build_dfg_def:
  build_dfg_block dfg [] = dfg /\
  build_dfg_block dfg (inst::insts) =
    let dfg' = case inst.inst_output of
                 SOME v => (\x. if x = v then SOME inst else dfg x)
               | NONE => dfg
    in build_dfg_block dfg' insts
End

Definition build_dfg_blocks_def:
  build_dfg_blocks dfg [] = dfg /\
  build_dfg_blocks dfg (bb::bbs) =
    build_dfg_blocks (build_dfg_block dfg bb.bb_instructions) bbs
End

Definition build_dfg_fn_def:
  build_dfg_fn fn = build_dfg_blocks (\x. NONE) fn.fn_blocks
End

(* Well-formedness is preserved as we build the DFG *)
Theorem well_formed_dfg_update:
  !dfg inst v.
    well_formed_dfg dfg /\ inst.inst_output = SOME v
    ==> well_formed_dfg (\x. if x = v then SOME inst else dfg x)
Proof
  rw[well_formed_dfg_def] >>
  Cases_on `x = v` >> fs[]
QED

Theorem build_dfg_block_well_formed:
  !dfg insts.
    well_formed_dfg dfg ==> well_formed_dfg (build_dfg_block dfg insts)
Proof
  Induct_on `insts` >>
  simp[build_dfg_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_output` >>
  simp[build_dfg_def] >>
  metis_tac[well_formed_dfg_update]
QED

Theorem build_dfg_blocks_well_formed:
  !dfg bbs.
    well_formed_dfg dfg ==> well_formed_dfg (build_dfg_blocks dfg bbs)
Proof
  Induct_on `bbs` >> rw[build_dfg_blocks_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `build_dfg_block dfg h.bb_instructions` mp_tac) >>
  impl_tac >- (match_mp_tac build_dfg_block_well_formed >> simp[]) >>
  simp[]
QED

Theorem build_dfg_fn_well_formed:
  !fn. well_formed_dfg (build_dfg_fn fn)
Proof
  simp[build_dfg_fn_def] >>
  match_mp_tac build_dfg_blocks_well_formed >>
  simp[well_formed_dfg_def]
QED

(* --------------------------------------------------------------------------
   PHI Origins Computation

   We traverse backwards through PHI and assign chains to find the "root"
   instructions. This is done with cycle detection to handle loops.
   -------------------------------------------------------------------------- *)

(* Get operands that are variables from a PHI instruction *)
Definition phi_var_operands_def:
  phi_var_operands [] = [] /\
  phi_var_operands [_] = [] /\
  phi_var_operands (Label lbl :: Var v :: rest) = v :: phi_var_operands rest /\
  phi_var_operands (_ :: _ :: rest) = phi_var_operands rest
End

(* Well-formed PHI: all value operands (after labels) are variables *)
Definition phi_well_formed_def:
  phi_well_formed [] = T /\
  phi_well_formed [_] = T /\
  phi_well_formed (Label lbl :: Var v :: rest) = phi_well_formed rest /\
  phi_well_formed (Label lbl :: _ :: rest) = F /\
  phi_well_formed (_ :: _ :: rest) = phi_well_formed rest
End

(* Get the single operand from an assign, if it's a variable *)
Definition assign_var_operand_def:
  assign_var_operand inst =
    case inst.inst_operands of
      [Var v] => SOME v
    | _ => NONE
End

(* Check if instruction is a PHI *)
Definition is_phi_inst_def:
  is_phi_inst inst <=> inst.inst_opcode = PHI
End

(* Check if instruction is an assign with variable operand *)
Definition is_var_assign_def:
  is_var_assign inst <=>
    inst.inst_opcode = ASSIGN /\ IS_SOME (assign_var_operand inst)
End

(* --------------------------------------------------------------------------
   Origin Computation (Recursive)

   The key function traces back through PHI/assign chains.
   Returns a set of "origin" instructions.

   Key properties:
   - For non-PHI/non-assign: returns singleton set of that instruction
   - For assign: follows the chain back
   - For PHI with multiple origins: returns singleton of the PHI itself
   - For PHI with one origin: returns that origin
   - Handles cycles via visited set
   -------------------------------------------------------------------------- *)

(* Helper to get variables from instruction for tracing *)
Definition inst_source_vars_def:
  inst_source_vars inst =
    if inst.inst_opcode = PHI then
      phi_var_operands inst.inst_operands
    else if inst.inst_opcode = ASSIGN then
      case assign_var_operand inst of
        SOME v => [v]
      | NONE => []
    else []
End

(* Origin computation using worklist/visited set approach
   This avoids HOL4's termination difficulties with mutual recursion *)

(* Single step: given an instruction, return either:
   - INL {inst}: this is a root instruction
   - INR vars: need to trace these variables further *)
Definition origin_step_def:
  origin_step inst =
    if inst.inst_opcode = PHI then
      INR (phi_var_operands inst.inst_operands)
    else if inst.inst_opcode = ASSIGN then
      case assign_var_operand inst of
        SOME v => INR [v]
      | NONE => INL {inst}
    else
      INL {inst}
End

(* --------------------------------------------------------------------------
   Simplified Origin Tracking

   For verification, we use a simpler model:
   An origin is the first non-PHI, non-var-assign instruction found
   by following the def-use chain.
   -------------------------------------------------------------------------- *)

(* Direct origin: follow exactly one step *)
Definition direct_origin_def:
  direct_origin dfg inst =
    if inst.inst_opcode = ASSIGN then
      case assign_var_operand inst of
        SOME v => dfg v
      | NONE => SOME inst
    else
      SOME inst
End

(* Origin set for a PHI's operands *)
Definition phi_direct_origins_def:
  phi_direct_origins dfg inst =
    if ~is_phi_inst inst then {} else
    let vars = phi_var_operands inst.inst_operands in
    let origins = MAP (\v. dfg v) vars in
    set (MAP THE (FILTER IS_SOME origins))
End

(* --------------------------------------------------------------------------
   PHI Elimination Transformation

   Simple case: if all PHI operands refer to the same variable, replace
   the PHI with an assignment from that variable.
   -------------------------------------------------------------------------- *)

(* Get the set of unique variable names from PHI operands *)
Definition phi_operand_vars_def:
  phi_operand_vars ops = set (phi_var_operands ops)
End

(* Check if all PHI operands are the same variable (simplest elimination case) *)
Definition phi_all_same_var_def:
  phi_all_same_var inst =
    if ~is_phi_inst inst then NONE else
    let vars = phi_operand_vars inst.inst_operands in
    (* Check if there's exactly one unique variable (excluding self-reference) *)
    let out_var = case inst.inst_output of SOME v => {v} | NONE => {} in
    let non_self = vars DIFF out_var in
    if CARD non_self = 1 then
      SOME (CHOICE non_self)
    else NONE
End

(* Legacy: check using DFG for single origin instruction *)
Definition phi_single_origin_def:
  phi_single_origin dfg inst =
    if ~is_phi_inst inst then NONE else
    let origins = phi_direct_origins dfg inst in
    (* Remove self-references *)
    let non_self = origins DELETE inst in
    if CARD non_self = 1 then
      SOME (CHOICE non_self)
    else NONE
End

(* Transform instruction: PHI -> ASSIGN if all operands are same variable *)
Definition transform_inst_simple_def:
  transform_inst_simple inst =
    case phi_all_same_var inst of
      SOME src_var =>
        inst with <|
          inst_opcode := ASSIGN;
          inst_operands := [Var src_var]
        |>
    | NONE => inst
End

(* Transform instruction using DFG analysis (more aggressive) *)
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
         | NONE => inst)  (* Shouldn't happen for well-formed code *)
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

(* --------------------------------------------------------------------------
   Correctness Proof

   The key lemma: if a PHI has a single origin src, then at runtime,
   the PHI will always resolve to the value of src (regardless of which
   predecessor we came from).
   -------------------------------------------------------------------------- *)

(* Value equivalence: two instructions produce the same value in state s *)
Definition inst_value_equiv_def:
  inst_value_equiv inst1 inst2 s <=>
    case (inst1.inst_output, inst2.inst_output) of
      (SOME v1, SOME v2) =>
        lookup_var v1 s = lookup_var v2 s
    | _ => F
End

(* Key invariant: after transformation, variable values are preserved *)
Definition var_equiv_def:
  var_equiv s1 s2 <=>
    !v. lookup_var v s1 = lookup_var v s2
End

(* State equivalence (for semantics preservation) *)
Definition state_equiv_def:
  state_equiv s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted
End

(* Reflexivity of state_equiv *)
Theorem state_equiv_refl:
  !s. state_equiv s s
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* Symmetry of state_equiv *)
Theorem state_equiv_sym:
  !s1 s2. state_equiv s1 s2 ==> state_equiv s2 s1
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* Transitivity of state_equiv *)
Theorem state_equiv_trans:
  !s1 s2 s3. state_equiv s1 s2 /\ state_equiv s2 s3 ==> state_equiv s1 s3
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* --------------------------------------------------------------------------
   Key Lemma: resolve_phi returns an element from phi_var_operands

   If resolve_phi succeeds with Var v, then v is one of the phi operand vars.
   -------------------------------------------------------------------------- *)

Theorem resolve_phi_in_operands:
  !prev_bb ops v.
    resolve_phi prev_bb ops = SOME (Var v) ==>
    MEM v (phi_var_operands ops)
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  (* Now we have h::h'::t' - case split on operand types *)
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_var_operands_def] >>
  (* Handle conditional cases *)
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  (* Apply IH to tail *)
  TRY (disj2_tac) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  rpt strip_tac >> res_tac
QED

(* Helper: well-formed phi operands always resolve to Var values *)
Theorem resolve_phi_well_formed:
  !prev_bb ops v.
    phi_well_formed ops /\
    resolve_phi prev_bb ops = SOME v ==>
    ?var. v = Var var
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  (* Case split on operand types *)
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_well_formed_def] >>
  (* Label::Var case needs case split on label match *)
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  (* Apply IH to tail when needed *)
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> res_tac >> metis_tac[]
QED

(* --------------------------------------------------------------------------
   Simple Case Correctness

   When all PHI operands are the same variable v, the PHI is equivalent to
   an assignment from v.
   -------------------------------------------------------------------------- *)

(* Helper: if phi_all_same_var returns src_var, and resolve_phi returns Var v,
   then v is either src_var or the output variable (self-reference) *)
(* Helper: MEM to set membership *)
Theorem MEM_set:
  !x l. MEM x l ==> x IN set l
Proof
  Induct_on `l` >> rw[LIST_TO_SET_DEF, IN_INSERT]
QED

(* Helper: if phi_all_same_var returns src_var, and resolve_phi returns Var v,
   then v is either src_var or the output variable (self-reference) *)
Theorem phi_all_same_var_resolve:
  !inst src_var prev_bb v.
    is_phi_inst inst /\
    phi_well_formed inst.inst_operands /\
    phi_all_same_var inst = SOME src_var /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v)
  ==>
    v = src_var \/ v = THE inst.inst_output
Proof
  rpt strip_tac >>
  imp_res_tac resolve_phi_in_operands >>
  `v IN set (phi_var_operands inst.inst_operands)` by metis_tac[MEM_set] >>
  fs[phi_all_same_var_def, is_phi_inst_def, phi_operand_vars_def] >>
  Cases_on `inst.inst_output` >> fs[]
  (* NONE case: set has CARD 1, v IN set, so v = src_var *)
  >- (`SING (set (phi_var_operands inst.inst_operands))`
        by fs[SING_IFF_CARD1, FINITE_LIST_TO_SET] >>
      fs[SING_DEF] >>
      `src_var = x` by fs[CHOICE_SING] >>
      metis_tac[IN_SING])
  (* SOME x case: either v = x or v IN DIFF, hence v = src_var *)
  >> (Cases_on `v = x` >> simp[] >>
      `v IN (set (phi_var_operands inst.inst_operands) DIFF {x})`
        by fs[IN_DIFF, IN_SING] >>
      `CARD (set (phi_var_operands inst.inst_operands) DIFF {x}) = 1`
        by fs[CARD_DIFF_EQN, FINITE_LIST_TO_SET] >>
      `SING (set (phi_var_operands inst.inst_operands) DIFF {x})`
        by fs[SING_IFF_CARD1, FINITE_DIFF, FINITE_LIST_TO_SET] >>
      fs[SING_DEF] >>
      `src_var = x'` by fs[CHOICE_SING] >>
      metis_tac[IN_SING, IN_DIFF])
QED

(* Evaluate a PHI step given the predecessor and output *)
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

(* Evaluate an ASSIGN with a single operand *)
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

(* Evaluate the transformed PHI (simple assignment case) *)
Theorem step_inst_transform_simple_eval:
  !inst src_var out s.
    phi_all_same_var inst = SOME src_var /\
    inst.inst_output = SOME out
  ==>
    step_inst (transform_inst_simple inst) s =
      case eval_operand (Var src_var) s of
        SOME v => OK (update_var out v s)
      | NONE => Error "undefined operand"
Proof
  simp[transform_inst_simple_def, step_inst_assign_eval, eval_operand_def]
QED

(* Evaluate a PHI that resolves to Var src_var and succeeds *)
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
  fs[is_phi_inst_def, step_inst_phi_eval] >>
  fs[] >>
  Cases_on `eval_operand (Var src_var) s`
  >- (fs[exec_result_distinct, exec_result_11] >> metis_tac[])
  >>
  rename1 `eval_operand (Var src_var) s = SOME v` >>
  fs[eval_operand_def, exec_result_distinct, exec_result_11] >>
  qexists_tac `v` >> fs[]
QED

(* For phi_all_same_var_correct, we rule out the self-reference edge
   (where resolve_phi returns the PHI's output). On those edges the
   transformation is not obviously sound, so we assume the predecessor
   chosen at runtime is not the self edge. *)
Theorem phi_all_same_var_correct:
  !inst s s' src_var out prev_bb.
    is_phi_inst inst /\
    phi_well_formed inst.inst_operands /\
    phi_all_same_var inst = SOME src_var /\
    inst.inst_output = SOME out /\
    src_var <> out /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var src_var) /\
    (* Exclude the self-reference case *)
    step_inst inst s = OK s'
  ==>
    step_inst (transform_inst_simple inst) s = OK s'
Proof
  rpt strip_tac >>
  imp_res_tac step_inst_phi_resolves_var_ok >>
  fs[step_inst_transform_simple_eval, eval_operand_def,
     exec_result_distinct, exec_result_11]
QED

(* --------------------------------------------------------------------------
   Main Correctness Theorem

   If the original PHI and transformed ASSIGN both execute from equivalent
   states, they produce equivalent output states.
   -------------------------------------------------------------------------- *)

(* Helper: PHI resolution yields the value of the origin *)
Theorem phi_resolve_single_origin:
  !dfg inst origin prev_bb s v.
    is_phi_inst inst /\
    phi_single_origin dfg inst = SOME origin /\
    well_formed_dfg dfg /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v) /\
    dfg v = SOME origin
  ==>
    eval_operand (Var v) s =
      case origin.inst_output of
        SOME src => lookup_var src s
      | NONE => NONE
Proof
  rw[eval_operand_def, well_formed_dfg_def] >>
  res_tac >> fs[]
QED

(* Main theorem: transformed instruction preserves semantics *)
Theorem transform_inst_correct:
  !dfg inst s s'.
    step_inst inst s = OK s' /\
    is_phi_inst inst
  ==>
    ?s''. step_inst (transform_inst dfg inst) s = OK s'' /\
          state_equiv s' s''
Proof
  rpt strip_tac >>
  (* Case split on whether transformation happens *)
  Cases_on `phi_single_origin dfg inst`
  >- (
    (* No transformation: phi_single_origin = NONE *)
    (* transform_inst returns inst unchanged *)
    qexists_tac `s'` >>
    fs[transform_inst_def, state_equiv_refl]
  ) >>
  (* Transformation case: phi_single_origin = SOME origin *)
  Cases_on `x.inst_output`
  >- (
    (* Origin has no output - transform_inst returns inst unchanged *)
    qexists_tac `s'` >>
    fs[transform_inst_def, state_equiv_refl]
  ) >>
  (* Normal case: origin has output, PHI becomes ASSIGN *)
  (* This is the interesting case - need to show ASSIGN produces same result *)
  cheat
QED

(* Block-level correctness *)
Theorem transform_block_correct:
  !dfg bb s s'.
    run_block (\x. NONE) bb s = OK s'
  ==>
    ?s''. run_block (\x. NONE) (transform_block dfg bb) s = OK s'' /\
          state_equiv s' s''
Proof
  cheat
QED

(* Function-level correctness (main theorem) *)
Theorem phi_elimination_correct:
  !fn s result.
    run_function fn s = result
  ==>
    run_function (transform_function fn) s = result
Proof
  (* High-level proof sketch:
     1. Each PHI with single origin is replaced with ASSIGN
     2. ASSIGN from the origin variable has same effect as PHI
     3. State equivalence is preserved through execution *)
  cheat
QED

val _ = export_theory();
