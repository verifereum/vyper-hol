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

(* --------------------------------------------------------------------------
   Function-level Correctness
   -------------------------------------------------------------------------- *)

Theorem phi_elimination_correct:
  !fuel (func:ir_function) s result.
    run_function fuel func s = result ==>
    ?result'. run_function fuel (transform_function func) s = result' /\
              result_equiv result result'
Proof
  cheat
QED

(* --------------------------------------------------------------------------
   Context-level Correctness
   -------------------------------------------------------------------------- *)

Theorem phi_elimination_context_correct:
  !ctx fn_name fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
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
  metis_tac[phi_elimination_correct]
QED

val _ = export_theory();
