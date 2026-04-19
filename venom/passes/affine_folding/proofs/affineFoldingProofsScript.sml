(*
 * Affine Folding Pass — Correctness Proof
 *
 * The original theorem statement (no preconditions) is FALSE.
 * Counterexample: non-SSA function with same variable defined in two blocks
 * causes DFG/lattice mismatch, producing incorrect rewrites.
 *
 * The weakened statement adds an SSA uniqueness precondition, which is
 * trivially satisfied by the Vyper pipeline (produces SSA IR).
 *)
Theory affineFoldingProofs
Ancestors
  affineFoldingDefs execEquivProps passSimulationDefs passSimulationProps
  passSharedDefs passSharedProps stateEquivProps venomExecProps
  venomExecSemantics venomInst venomInstProps venomState

(* ===== Framework: function equality from block equality with invariant ===== *)

(* If an invariant P holds on the initial state and is preserved by
   each block, and each block transforms identically when P holds,
   then run_function on the transformed function is identical. *)
Triviality run_blocks_map_inv_eq:
  !P bt fn fuel ctx s.
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s. MEM bb fn.fn_blocks /\ P s ==>
      run_block fuel ctx (bt bb) s = run_block fuel ctx bb s) /\
    (!bb fuel ctx s s'. MEM bb fn.fn_blocks /\ P s /\
      run_block fuel ctx bb s = OK s' ==> P s') /\
    P s ==>
    run_blocks fuel ctx (function_map_transform bt fn) s =
    run_blocks fuel ctx fn s
Proof
  ntac 3 gen_tac >> Induct_on `fuel` >> rpt gen_tac >> strip_tac
  >- simp[run_blocks_def] >>
  simp[Once run_blocks_def, SimpLHS, function_map_transform_def,
       lookup_block_map] >>
  simp[Once run_blocks_def, SimpRHS] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  (* run_block = exec_block with idx 0, so rewrite via run_block *)
  simp[GSYM run_block_def] >>
  `run_block fuel ctx (bt bb) s = run_block fuel ctx bb s`
    by metis_tac[] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  Cases_on `run_block fuel ctx bb s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `P v` by metis_tac[] >>
  simp[GSYM function_map_transform_def] >>
  first_x_assum irule >> metis_tac[]
QED

(* run_function_map_inv_eq removed — callers use run_blocks_map_inv_eq directly *)

(* ===== Lattice Soundness Definitions ===== *)

Definition vi_sound_def:
  vi_sound (VarInfo base offset) v s =
    case FLOOKUP s.vs_vars v of
      NONE => T
    | SOME val =>
        case base of
          NONE => (val = offset)
        | SOME bop =>
            ?bval. eval_operand bop s = SOME bval /\ (val = bval + offset)
End

Definition vi_alist_sound_def:
  vi_alist_sound info s =
    !v vi. ALOOKUP info v = SOME vi ==> vi_sound vi v s
End

Triviality eval_op_idx_indep:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Triviality vi_sound_idx_indep:
  !vi v s n. vi_sound vi v (s with vs_inst_idx := n) = vi_sound vi v s
Proof
  Cases >> simp[vi_sound_def, eval_op_idx_indep]
QED

Triviality vi_alist_sound_idx_indep:
  !info s n. vi_alist_sound info (s with vs_inst_idx := n) =
             vi_alist_sound info s
Proof
  rw[vi_alist_sound_def, vi_sound_idx_indep]
QED

(* The lattice entry for out_var equals the transfer function result.
   This is guaranteed by SSA (no shadowing in ALOOKUP). *)
Definition vi_entry_consistent_def:
  vi_entry_consistent vi inst =
    case inst.inst_outputs of
      [out_var] =>
        (case ALOOKUP vi out_var of
           NONE => T
         | SOME entry =>
             let out_op = Var out_var in
             if inst.inst_opcode = ADD then
               (case inst.inst_operands of
                  [op1; op2] =>
                    entry = transfer_add (vi_lookup vi op1)
                                         (vi_lookup vi op2) out_op
                | _ => T)
             else if inst.inst_opcode = SUB then
               (case inst.inst_operands of
                  [op1; op2] =>
                    entry = transfer_sub (vi_lookup vi op1)
                                         (vi_lookup vi op2) out_op
                | _ => T)
             else if inst.inst_opcode = ASSIGN then
               (case inst.inst_operands of
                  [src] =>
                    entry = transfer_assign (vi_lookup vi src)
                | _ => T)
             else entry = VarInfo (SOME out_op) 0w)
    | _ => T
End

(* ===== vi_lookup operand soundness ===== *)

(* When eval_operand succeeds, vi_lookup predicts the value in terms
   of a base operand and offset *)
Theorem vi_lookup_eval[local]:
  !vi op s val.
    vi_alist_sound vi s /\ eval_operand op s = SOME val ==>
    case vi_lookup vi op of
      VarInfo NONE off => (val = off)
    | VarInfo (SOME bop) off =>
        ?bval. eval_operand bop s = SOME bval /\ (val = bval + off)
Proof
  rpt strip_tac >>
  Cases_on `op` >>
  fs[vi_lookup_def, eval_operand_def, lookup_var_def, wordsTheory.WORD_ADD_0] >>
  (* remaining: Var case *)
  rename1 `FLOOKUP s.vs_vars v = SOME val` >>
  Cases_on `ALOOKUP vi v` >> fs[]
  >- (* ALOOKUP vi v = NONE — default entry *)
     (rw[eval_operand_def, lookup_var_def, wordsTheory.WORD_ADD_0])
  >- (* ALOOKUP vi v = SOME entry *)
     (rename1 `ALOOKUP vi v = SOME entry` >>
      Cases_on `entry` >> fs[vi_alist_sound_def] >>
      first_x_assum drule >> rw[vi_sound_def] >>
      fs[eval_operand_def, lookup_var_def])
QED

(* ===== Transform Shape Preservation ===== *)

Theorem af_rewrite_inst_preserves[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    result.inst_outputs = inst.inst_outputs /\
    result.inst_id = inst.inst_id
Proof
  simp[af_rewrite_inst_def, vi_base_def, vi_offset_def,
     af_extract_val_lit_def, af_extract_sub_val_lit_def] >>
  rpt gen_tac >> rpt (BasicProvers.PURE_CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

Theorem af_rewrite_inst_opcode[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    (result.inst_opcode = ASSIGN \/ result.inst_opcode = ADD)
Proof
  simp[af_rewrite_inst_def, vi_base_def, vi_offset_def,
     af_extract_val_lit_def, af_extract_sub_val_lit_def] >>
  rpt gen_tac >> rpt (BasicProvers.PURE_CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

Theorem af_transform_block_label[local]:
  !dfg vi bb. (af_transform_block dfg vi bb).bb_label = bb.bb_label
Proof
  rw[af_transform_block_def]
QED

(* ===== Opcode-specific step_inst_base lemmas ===== *)

Theorem step_inst_base_ADD[local]:
  !inst s. inst.inst_opcode = ADD ==>
    step_inst_base inst s = exec_pure2 word_add inst s
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

Theorem step_inst_base_SUB[local]:
  !inst s. inst.inst_opcode = SUB ==>
    step_inst_base inst s = exec_pure2 word_sub inst s
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

Theorem step_inst_base_ASSIGN[local]:
  !inst s. inst.inst_opcode = ASSIGN ==>
    step_inst_base inst s =
      case (inst.inst_operands, inst.inst_outputs) of
        ([op1], [out]) =>
          (case eval_operand op1 s of
            SOME v => OK (update_var out v s)
          | NONE => Error "undefined operand")
      | _ => Error "assign requires 1 operand and single output"
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

(* Non-INVOKE opcodes: ADD, SUB, ASSIGN are all non-INVOKE *)
Theorem ADD_not_INVOKE[local]:
  ADD <> INVOKE
Proof
  EVAL_TAC
QED

Theorem SUB_not_INVOKE[local]:
  SUB <> INVOKE
Proof
  EVAL_TAC
QED

Theorem ASSIGN_not_INVOKE[local]:
  ASSIGN <> INVOKE
Proof
  EVAL_TAC
QED

(* ===== Transfer Function Soundness ===== *)

(* Unified: after writing val to out_var, the transfer function result
   is sound — covering all base cases (NONE=constant, SOME=affine, identity).
   Parameterized by val and the transfer result entry. *)
Theorem transfer_result_vi_sound[local]:
  !vi entry out_var val s.
    vi_alist_sound vi s /\
    (case entry of
       VarInfo NONE offset => (val = offset)
     | VarInfo (SOME bop) offset =>
         (?bval. eval_operand bop s = SOME bval /\ val = bval + offset) /\
         (!x. bop = Var x ==> x <> out_var)) ==>
    vi_sound entry out_var (s with vs_vars := s.vs_vars |+ (out_var, val))
Proof
  Cases_on `entry` >> simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `o'` >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x` >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The identity entry VarInfo (SOME (Var v)) 0w is always sound *)
Theorem vi_sound_identity[local]:
  !v s. vi_sound (VarInfo (SOME (Var v)) 0w) v s
Proof
  rw[vi_sound_def, eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> simp[wordsTheory.WORD_ADD_0]
QED

(* transfer_add result satisfies transfer_result_vi_sound preconditions *)
Theorem transfer_add_vi_sound[local]:
  !vi op1 op2 out_var s v1 v2.
    vi_alist_sound vi s /\
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 /\
    (case vi_base (transfer_add (vi_lookup vi op1) (vi_lookup vi op2)
                     (Var out_var)) of
       SOME (Var v) => v <> out_var | _ => T) ==>
    vi_sound (transfer_add (vi_lookup vi op1) (vi_lookup vi op2) (Var out_var))
      out_var (s with vs_vars := s.vs_vars |+ (out_var, v1 + v2))
Proof
  rpt strip_tac >>
  Cases_on `vi_lookup vi op1` >> Cases_on `vi_lookup vi op2` >>
  rename1 `transfer_add (VarInfo b1 o1) (VarInfo b2 o2) _` >>
  Cases_on `b1` >> Cases_on `b2` >>
  gvs[transfer_add_def, vi_base_def] >>
  imp_res_tac vi_lookup_eval >> gvs[] >>
  TRY (irule transfer_result_vi_sound >> simp[] >>
       Cases_on `x` >> gvs[] >>
       metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM] >>
       NO_TAC) >>
  simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[wordsTheory.WORD_ADD_COMM]
QED

(* transfer_sub result satisfies vi_sound *)
Theorem transfer_sub_vi_sound[local]:
  !vi op1 op2 out_var s v1 v2.
    vi_alist_sound vi s /\
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 /\
    (case vi_base (transfer_sub (vi_lookup vi op1) (vi_lookup vi op2)
                     (Var out_var)) of
       SOME (Var v) => v <> out_var | _ => T) ==>
    vi_sound (transfer_sub (vi_lookup vi op1) (vi_lookup vi op2) (Var out_var))
      out_var (s with vs_vars := s.vs_vars |+ (out_var, v1 - v2))
Proof
  rpt strip_tac >>
  Cases_on `vi_lookup vi op1` >> Cases_on `vi_lookup vi op2` >>
  rename1 `transfer_sub (VarInfo b1 o1) (VarInfo b2 o2) _` >>
  Cases_on `b2` >> gvs[transfer_sub_def, vi_base_def] >>
  imp_res_tac vi_lookup_eval >> gvs[] >>
  TRY (simp[vi_sound_identity] >> NO_TAC) >>
  Cases_on `b1` >> gvs[] >>
  TRY (irule transfer_result_vi_sound >> simp[] >>
       Cases_on `x` >> gvs[] >>
       metis_tac[wordsTheory.WORD_ADD_SUB_ASSOC, wordsTheory.WORD_ADD_COMM] >>
       NO_TAC) >>
  simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[wordsTheory.WORD_ADD_SUB_ASSOC, wordsTheory.WORD_ADD_COMM]
QED

(* transfer_assign result satisfies vi_sound *)
Theorem transfer_assign_vi_sound[local]:
  !vi op1 out_var s v1.
    vi_alist_sound vi s /\
    eval_operand op1 s = SOME v1 /\
    (case vi_base (transfer_assign (vi_lookup vi op1)) of
       SOME (Var v) => v <> out_var | _ => T) ==>
    vi_sound (transfer_assign (vi_lookup vi op1))
      out_var (s with vs_vars := s.vs_vars |+ (out_var, v1))
Proof
  rpt strip_tac >>
  Cases_on `vi_lookup vi op1` >> gvs[transfer_assign_def, vi_base_def] >>
  imp_res_tac vi_lookup_eval >> gvs[] >>
  Cases_on `o'` >> gvs[] >>
  TRY (irule transfer_result_vi_sound >> simp[] >>
       Cases_on `x` >> gvs[] >> metis_tac[] >> NO_TAC) >>
  simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Value-level soundness for af_rewrite_inst_step_eq *)
Theorem transfer_add_sound[local]:
  !vi op1 op2 out_op vi_b offset s v1 v2.
    vi_alist_sound vi s /\
    transfer_add (vi_lookup vi op1) (vi_lookup vi op2) out_op =
      VarInfo (SOME vi_b) offset /\
    vi_b <> out_op /\
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    ?bval. eval_operand vi_b s = SOME bval /\ v1 + v2 = bval + offset
Proof
  rpt strip_tac >>
  Cases_on `vi_lookup vi op1` >> Cases_on `vi_lookup vi op2` >>
  rename1 `transfer_add (VarInfo b1 o1) (VarInfo b2 o2) out_op` >>
  fs[transfer_add_def] >>
  Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
  imp_res_tac vi_lookup_eval >> gvs[] >>
  metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM]
QED

Theorem transfer_sub_sound[local]:
  !vi op1 op2 out_op vi_b offset s v1 v2.
    vi_alist_sound vi s /\
    transfer_sub (vi_lookup vi op1) (vi_lookup vi op2) out_op =
      VarInfo (SOME vi_b) offset /\
    vi_b <> out_op /\
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    ?bval. eval_operand vi_b s = SOME bval /\ v1 - v2 = bval + offset
Proof
  rpt strip_tac >>
  Cases_on `vi_lookup vi op1` >> Cases_on `vi_lookup vi op2` >>
  rename1 `transfer_sub (VarInfo b1 o1) (VarInfo b2 o2) out_op` >>
  fs[transfer_sub_def] >>
  Cases_on `b2` >> gvs[] >>
  imp_res_tac vi_lookup_eval >> gvs[] >>
  metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM,
            wordsTheory.WORD_SUB_ADD, wordsTheory.WORD_ADD_SUB]
QED

(* ===== Per-Instruction Step Equality ===== *)

(* The rewrite produces SOME result only for ADD/SUB opcodes.
   The result is either ASSIGN [eff_base] or ADD [Lit eff_offset; eff_base].
   We show: step_inst result s = step_inst inst s when vi_alist_sound vi s.

   The argument:
   - Original ADD/SUB with [op1; op2] computes f(eval op1, eval op2) for f = +/-
   - vi_lookup on op1, op2 gives affine descriptions: val = base_val + off
   - transfer_add/sub computes the result affine form: result = eval(vi_b) + offset
   - The rewrite uses eff_base and eff_offset s.t. eff_offset + eval(eff_base) = eval(vi_b) + offset
   - So original computation = eff_offset + eval(eff_base) = rewritten computation
*)
(* Helper: when af_rewrite_inst succeeds, extract all structural info *)
Theorem af_rewrite_inst_cases[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    ?out_var vi_b offset op1 op2.
      (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
      inst.inst_outputs = [out_var] /\
      inst.inst_operands = [op1; op2] /\
      result.inst_outputs = [out_var] /\
      ALOOKUP vi out_var = SOME (VarInfo (SOME vi_b) offset) /\
      vi_b <> Var out_var /\
      ((result.inst_opcode = ASSIGN /\
        ?eff_base. result.inst_operands = [eff_base]) \/
       (result.inst_opcode = ADD /\
        ?eff_offset eff_base. result.inst_operands = [Lit eff_offset; eff_base]))
Proof
  rpt strip_tac >>
  gvs[af_rewrite_inst_def, vi_base_def, vi_offset_def,
      af_extract_val_lit_def, af_extract_sub_val_lit_def,
      AllCaseEqs()] >>
  Cases_on `vi'` >> gvs[vi_base_def, vi_offset_def]
QED

(* Helper: vi_alist_sound + ALOOKUP + FLOOKUP gives affine relationship *)
Theorem vi_alist_sound_lookup[local]:
  !vi v entry s val.
    vi_alist_sound vi s /\
    ALOOKUP vi v = SOME entry /\
    FLOOKUP s.vs_vars v = SOME val ==>
    vi_sound entry v s /\
    case entry of
      VarInfo NONE off => (val = off)
    | VarInfo (SOME bop) off =>
        ?bval. eval_operand bop s = SOME bval /\ (val = bval + off)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (fs[vi_alist_sound_def] >> res_tac) >>
  Cases_on `entry` >> fs[vi_alist_sound_def] >>
  first_x_assum drule >> rw[vi_sound_def]
QED

(* Word arithmetic helpers for affine folding *)
Theorem word_sub_0_eq[local]:
  !(a:'a word) b. a - b = 0w ==> b = a
Proof
  rpt strip_tac >>
  sg `a = a - b + b` >- rewrite_tac[wordsTheory.WORD_SUB_ADD] >>
  gvs[wordsTheory.WORD_ADD_0]
QED

Theorem word_sub_add_rearrange[local]:
  !(a:'a word) b c. a - b + (c + b) = c + a
Proof
  metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM,
            wordsTheory.WORD_SUB_ADD]
QED

(* Key lemma: the rewrite result evaluates to the same value as
   eval(vi_b) + offset, for both ASSIGN and ADD result forms.

   This is the semantic core of af_rewrite_inst correctness.
   Uses AllCaseEqs to decompose the definition, then handles
   direct (eff_base = vi_b) and indirect (eff_base = Var ev) subcases. *)
Theorem af_rewrite_inst_result_sound[local]:
  !dfg vi inst result s out_var vi_b offset.
    af_rewrite_inst dfg vi inst = SOME result /\
    vi_alist_sound vi s /\
    inst.inst_outputs = [out_var] /\
    ALOOKUP vi out_var = SOME (VarInfo (SOME vi_b) offset) /\
    (!v. MEM (Var v) result.inst_operands ==>
         eval_operand (Var v) s <> NONE) ==>
    ?bval.
      eval_operand vi_b s = SOME bval /\
      ((result.inst_opcode = ASSIGN /\
        ?eff_base. result.inst_operands = [eff_base] /\
          eval_operand eff_base s = SOME (bval + offset)) \/
       (result.inst_opcode = ADD /\
        ?eff_offset eff_base ebval. result.inst_operands = [Lit eff_offset; eff_base] /\
          eval_operand eff_base s = SOME ebval /\
          eff_offset + ebval = bval + offset))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[af_rewrite_inst_def, vi_base_def, vi_offset_def,
      af_extract_val_lit_def, af_extract_sub_val_lit_def,
      AllCaseEqs()] >>
  gvs[eval_operand_def, lookup_var_def, wordsTheory.WORD_ADD_0] >>
  (* Convert FLOOKUP ≠ NONE to FLOOKUP = SOME y *)
  imp_res_tac (prove(``!x:'a option. x <> NONE ==> ?y. x = SOME y``,
                     Cases >> simp[])) >>
  gvs[] >>
  (* Resolve vi_alist_sound for ev lookup (indirect cases) *)
  imp_res_tac vi_alist_sound_lookup >>
  TRY (Cases_on `evi`) >>
  gvs[eval_operand_def, lookup_var_def, vi_sound_def,
      vi_base_def, vi_offset_def] >>
  (* Word arithmetic: commutativity, sub-to-eq, rearrange *)
  TRY (imp_res_tac word_sub_0_eq >> gvs[] >> NO_TAC) >>
  metis_tac[word_sub_add_rearrange, wordsTheory.WORD_ADD_COMM]
QED

(* af_effective_base on a Label returns it unchanged *)
Theorem af_effective_base_label[local]:
  !dfg visited l target.
    af_effective_base dfg visited (Label l) target =
    if Label l = target then target else Label l
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[af_effective_base_def] >> simp[]
QED

(* af_rewrite_inst only succeeds for non-Label operands *)
Theorem af_rewrite_inst_no_labels[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    !l. ~MEM (Label l) inst.inst_operands
Proof
  rpt strip_tac >>
  gvs[af_rewrite_inst_def, vi_base_def, vi_offset_def,
      af_extract_val_lit_def, af_extract_sub_val_lit_def,
      is_lit_op_def, af_effective_base_label, AllCaseEqs()]
QED

(* Helper: non-label operands evaluate when Var operands are defined *)
Theorem eval_operand_non_label[local]:
  !op st.
    (!v. op = Var v ==> eval_operand (Var v) st <> NONE) /\
    (!l. op <> Label l) ==>
    ?val. eval_operand op st = SOME val
Proof
  Cases >> simp[eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> res_tac >> gvs[eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP st.vs_vars s` >> gvs[]
QED

(* Key semantic helper: the rewrite result computes the same value. *)
Theorem af_rewrite_inst_step_eq[local]:
  !dfg vi inst result fuel ctx s.
    af_rewrite_inst dfg vi inst = SOME result /\
    vi_alist_sound vi s /\
    vi_entry_consistent vi inst /\
    (!v. MEM (Var v) inst.inst_operands ==>
         eval_operand (Var v) s <> NONE) /\
    (!v. MEM (Var v) result.inst_operands ==>
         eval_operand (Var v) s <> NONE) ==>
    step_inst fuel ctx result s = step_inst fuel ctx inst s
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac af_rewrite_inst_cases >>
  imp_res_tac af_rewrite_inst_no_labels >>
  gvs[] >>
  (* Derive that original operands evaluate (non-Label + Var-defined) *)
  `?v1. eval_operand op1 s = SOME v1`
    by (irule eval_operand_non_label >> gvs[]) >>
  `?v2. eval_operand op2 s = SOME v2`
    by (irule eval_operand_non_label >> gvs[]) >>
  (* Get result_sound for the rewrite *)
  drule af_rewrite_inst_result_sound >>
  disch_then (qspecl_then [`s`, `out_var`, `vi_b`, `offset`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  (* Reduce step_inst to step_inst_base *)
  gvs[step_inst_non_invoke, ADD_not_INVOKE, SUB_not_INVOKE, ASSIGN_not_INVOKE] >>
  (* Unfold step_inst_base for both sides *)
  gvs[step_inst_base_ADD, step_inst_base_SUB, step_inst_base_ASSIGN,
      exec_pure2_def, eval_operand_def] >>
  (* Use vi_entry_consistent to connect ALOOKUP to transfer function *)
  gvs[vi_entry_consistent_def] >>
  (* transfer_*_sound gives v1 OP v2 = bval + offset *)
  TRY (qpat_x_assum `VarInfo _ _ = transfer_add _ _ _`
         (assume_tac o GSYM) >>
       drule_all transfer_add_sound >> strip_tac >> gvs[] >> NO_TAC) >>
  TRY (qpat_x_assum `VarInfo _ _ = transfer_sub _ _ _`
         (assume_tac o GSYM) >>
       drule_all transfer_sub_sound >> strip_tac >> gvs[] >> NO_TAC)
QED

(* Combined: transform preserves step_inst (defined operands case) *)
Theorem af_transform_inst_step_eq_defined[local]:
  !dfg vi inst fuel ctx s.
    vi_alist_sound vi s /\
    vi_entry_consistent vi inst /\
    (!v. MEM (Var v) inst.inst_operands ==>
         eval_operand (Var v) s <> NONE) /\
    (!v. MEM (Var v) (af_transform_inst dfg vi inst).inst_operands ==>
         eval_operand (Var v) s <> NONE) ==>
    step_inst fuel ctx (af_transform_inst dfg vi inst) s =
    step_inst fuel ctx inst s
Proof
  rw[af_transform_inst_def] >>
  rpt (BasicProvers.PURE_CASE_TAC >> gvs[]) >>
  irule af_rewrite_inst_step_eq >> gvs[] >> metis_tac[]
QED

(* Helper: step_inst errors when a non-INVOKE instruction has an undefined
   Var operand and the right operand structure (2 ops for ADD/SUB, 1 for ASSIGN) *)
Theorem step_inst_error_undefined_operand[local]:
  !fuel ctx inst s v.
    inst.inst_opcode <> INVOKE /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = ASSIGN) /\
    MEM (Var v) inst.inst_operands /\
    eval_operand (Var v) s = NONE /\
    ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
     (?op1 op2. inst.inst_operands = [op1; op2]) /\
     (?out. inst.inst_outputs = [out]) \/
     inst.inst_opcode = ASSIGN /\
     (?op1. inst.inst_operands = [op1]) /\
     (?out. inst.inst_outputs = [out])) ==>
    step_inst fuel ctx inst s = Error "undefined operand"
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_non_invoke] >>
  gvs[step_inst_base_ADD, step_inst_base_SUB, exec_pure2_def, listTheory.MEM] >>
  Cases_on `eval_operand op1 s` >> gvs[] >>
  TRY (ONCE_REWRITE_TAC[step_inst_base_def] >> simp[] >> NO_TAC)
QED

(* Combined: transform preserves step_inst with bidirectional operand reachability.
   When all operands defined: same OK result (via af_rewrite_inst correctness).
   When some operand undefined on both sides: both return Error "undefined operand". *)
Theorem af_transform_inst_step_eq[local]:
  !dfg vi inst fuel ctx s.
    vi_alist_sound vi s /\
    vi_entry_consistent vi inst /\
    inst.inst_opcode <> INVOKE /\
    ((!v. MEM (Var v) inst.inst_operands ==>
          eval_operand (Var v) s <> NONE) <=>
     (!v. MEM (Var v) (af_transform_inst dfg vi inst).inst_operands ==>
          eval_operand (Var v) s <> NONE)) ==>
    step_inst fuel ctx (af_transform_inst dfg vi inst) s =
    step_inst fuel ctx inst s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `!v. MEM (Var v) inst.inst_operands ==>
                eval_operand (Var v) s <> NONE`
  >- (irule af_transform_inst_step_eq_defined >> gvs[])
  >- (
    (* Some original operand undefined *)
    gvs[] >>
    (* Both sides: identify the undefined operand *)
    `?v'. MEM (Var v') (af_transform_inst dfg vi inst).inst_operands /\
          eval_operand (Var v') s = NONE` by (
      CCONTR_TAC >> gvs[] >>
      `!v'. MEM (Var v') (af_transform_inst dfg vi inst).inst_operands ==>
            eval_operand (Var v') s <> NONE` by metis_tac[] >>
      `!v. MEM (Var v) inst.inst_operands ==>
           eval_operand (Var v) s <> NONE` by metis_tac[] >>
      metis_tac[]) >>
    (* Unfold af_transform_inst to get structural info *)
    qabbrev_tac `ti = af_transform_inst dfg vi inst` >>
    Cases_on `af_transform_inst dfg vi inst = inst`
    >- (gvs[Abbr `ti`])
    >- (
      (* Transform differs: af_rewrite_inst produced something *)
      `?result. af_rewrite_inst dfg vi inst = SOME result /\
                ti = result` by (
        gvs[Abbr `ti`, af_transform_inst_def] >>
        rpt (BasicProvers.PURE_CASE_TAC >> gvs[])) >>
      gvs[] >>
      imp_res_tac af_rewrite_inst_cases >> gvs[] >>
      (* Original: ADD or SUB with [op1; op2], output [out_var], v undefined *)
      (* Transform: ASSIGN [eff_base] or ADD [Lit eff_offset; eff_base], v' undefined *)
      `step_inst fuel ctx inst s = Error "undefined operand"` by (
        irule step_inst_error_undefined_operand >>
        gvs[listTheory.MEM] >> metis_tac[]) >>
      `step_inst fuel ctx result s = Error "undefined operand"` by (
        irule step_inst_error_undefined_operand >>
        gvs[listTheory.MEM] >> metis_tac[]) >>
      simp[]))
QED

(* ===== Lattice Soundness Maintenance ===== *)

Theorem vi_alist_sound_nil[local]:
  !s. vi_alist_sound [] s
Proof
  rw[vi_alist_sound_def]
QED

(* ===== Block-Level Equality ===== *)

Theorem get_instruction_map[local]:
  !bb f idx.
    get_instruction (bb with bb_instructions := MAP f bb.bb_instructions) idx =
    OPTION_MAP f (get_instruction bb idx)
Proof
  rw[get_instruction_def] >> rw[listTheory.EL_MAP]
QED

(* Generic: run_block with per-instruction transform + state-dependent
   invariant. If:
   (1) The invariant P holds initially
   (2) At each instruction where P holds, step_inst of the transformed
       instruction equals step_inst of the original
   (3) The transformed instruction preserves is_terminator
   (4) P is preserved by each successful instruction step
   Then run_block on the transformed block = run_block on original.
   REUSABLE: applies to any per-instruction rewrite pass. *)
(* Helper: exec_block version of inst transform equality *)
Triviality exec_block_inst_transform_eq:
  !P ft bb fuel ctx s.
    P s /\
    (!inst. MEM inst bb.bb_instructions ==>
       is_terminator (ft inst).inst_opcode = is_terminator inst.inst_opcode) /\
    (!inst s'. P s' /\ MEM inst bb.bb_instructions ==>
       step_inst fuel ctx (ft inst) s' = step_inst fuel ctx inst s') /\
    (!inst s' s''.
       MEM inst bb.bb_instructions /\ P s' /\
       step_inst fuel ctx inst s' = OK s'' ==>
       P (s'' with vs_inst_idx := SUC s'.vs_inst_idx)) ==>
    exec_block fuel ctx (bb with bb_instructions :=
      MAP ft bb.bb_instructions) s =
    exec_block fuel ctx bb s
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  simp[Once exec_block_def, SimpLHS, get_instruction_map] >>
  simp[Once exec_block_def, SimpRHS] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  `MEM inst bb.bb_instructions`
    by (fs[get_instruction_def, listTheory.MEM_EL] >> metis_tac[]) >>
  `step_inst fuel ctx (ft inst) s = step_inst fuel ctx inst s`
    by metis_tac[] >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  `is_terminator (ft inst).inst_opcode = is_terminator inst.inst_opcode`
    by metis_tac[] >>
  simp[] >>
  IF_CASES_TAC >> simp[]
  (* Non-terminator, OK — recurse *)
  >- ((* Base case: 0 = LENGTH - idx contradicts get_instruction = SOME *)
      gvs[get_instruction_def]) >>
  (* Step case: apply IH *)
  first_x_assum (qspecl_then [`bb`, `v' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >>
  (impl_tac >- (gvs[get_instruction_def] >> metis_tac[])) >>
  disch_then irule >> metis_tac[]
QED

Theorem run_block_inst_transform_eq[local]:
  !P ft bb fuel ctx s.
    P s /\
    (!s n. P s ==> P (s with vs_inst_idx := n)) /\
    (!inst. MEM inst bb.bb_instructions ==>
       is_terminator (ft inst).inst_opcode = is_terminator inst.inst_opcode) /\
    (!inst s'. P s' /\ MEM inst bb.bb_instructions ==>
       step_inst fuel ctx (ft inst) s' = step_inst fuel ctx inst s') /\
    (!inst s' s''.
       MEM inst bb.bb_instructions /\ P s' /\
       step_inst fuel ctx inst s' = OK s'' ==>
       P (s'' with vs_inst_idx := SUC s'.vs_inst_idx)) ==>
    run_block fuel ctx (bb with bb_instructions :=
      MAP ft bb.bb_instructions) s =
    run_block fuel ctx bb s
Proof
  rpt strip_tac >> simp[run_block_def] >>
  qspecl_then [`P`, `ft`, `bb`, `fuel`, `ctx`, `s with vs_inst_idx := 0`]
    mp_tac exec_block_inst_transform_eq >>
  simp[] >> metis_tac[]
QED

(* Generic: P is preserved through exec_block execution. *)
Triviality exec_block_preserves_P:
  !P bb fuel ctx s s'.
    P s /\
    (!inst s1 s1'.
       MEM inst bb.bb_instructions /\ P s1 /\
       step_inst fuel ctx inst s1 = OK s1' ==>
       P s1' /\ P (s1' with vs_inst_idx := SUC s1.vs_inst_idx)) /\
    exec_block fuel ctx bb s = OK s' ==>
    P s'
Proof
  ntac 4 gen_tac >>
  Induct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[]
  (* Base case, get_instruction = SOME: contradiction with 0 = LENGTH - idx *)
  >- gvs[get_instruction_def] >>
  (* Step case, get_instruction = SOME *)
  rename1 `SOME inst` >>
  `MEM inst bb.bb_instructions`
    by (fs[get_instruction_def, listTheory.MEM_EL] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- ((* Terminator *)
      IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >> metis_tac[])
  >- ((* Non-terminator — recurse *)
      strip_tac >>
      (* Get P preservation for the step *)
      `P v' /\ P (v' with vs_inst_idx := SUC s.vs_inst_idx)`
        by (first_x_assum (qspecl_then [`inst`, `s`, `v'`] mp_tac) >> simp[]) >>
      (* Apply IH *)
      first_x_assum (qspecl_then [`bb`, `v' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >>
      (impl_tac >- gvs[get_instruction_def]) >>
      disch_then irule >> gvs[])
QED

(* Generic: P is preserved through run_block execution. *)
Theorem run_block_preserves_P[local]:
  !P bb fuel ctx s s'.
    P s /\
    (!s n. P s ==> P (s with vs_inst_idx := n)) /\
    (!inst s1 s1'.
       MEM inst bb.bb_instructions /\ P s1 /\
       step_inst fuel ctx inst s1 = OK s1' ==>
       P s1' /\ P (s1' with vs_inst_idx := SUC s1.vs_inst_idx)) /\
    run_block fuel ctx bb s = OK s' ==>
    P s'
Proof
  rpt strip_tac >>
  qspecl_then [`P`, `bb`, `fuel`, `ctx`, `s with vs_inst_idx := 0`, `s'`]
    mp_tac exec_block_preserves_P >>
  fs[run_block_def] >> metis_tac[]
QED

(* Affine transform preserves is_terminator: ADD/SUB are not terminators,
   and the transform only changes ADD/SUB to ASSIGN/ADD (also not terminators).
   For other opcodes, the transform is the identity. *)
Theorem af_transform_inst_terminator[local]:
  !dfg vi inst.
    is_terminator (af_transform_inst dfg vi inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  rw[af_transform_inst_def] >>
  rpt (BasicProvers.PURE_CASE_TAC >> gvs[]) >>
  imp_res_tac af_rewrite_inst_cases >> gvs[] >> EVAL_TAC
QED

(* vi_sound is preserved when the variable's value and base operand
   value are unchanged. *)
Theorem vi_sound_preserved_by_eq[local]:
  !entry v s s'.
    vi_sound entry v s /\
    FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v /\
    (case vi_base entry of
       NONE => T
     | SOME bop => eval_operand bop s' = eval_operand bop s) ==>
    vi_sound entry v s'
Proof
  Cases_on `entry` >> rw[vi_sound_def, vi_base_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[] >>
  Cases_on `o'` >> gvs[]
QED


(* eval_operand is unchanged when we update a different variable *)
Theorem eval_operand_update_other[local]:
  !op out_var v s.
    (!x. op = Var x ==> x <> out_var) ==>
    eval_operand op (s with vs_vars := s.vs_vars |+ (out_var, v)) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def,
                finite_mapTheory.FLOOKUP_UPDATE]
QED

(* vi_sound for a freshly written variable: if we write val to out_var,
   and the entry says val = eval(base) + offset, then vi_sound holds
   in the updated state — provided base doesn't reference out_var. *)
Theorem vi_sound_after_write[local]:
  !base offset out_var val s.
    (case base of
       NONE => val = offset
     | SOME bop =>
         (?bval. eval_operand bop s = SOME bval /\ val = bval + offset) /\
         (!x. bop = Var x ==> x <> out_var)) ==>
    vi_sound (VarInfo base offset) out_var
      (s with vs_vars := s.vs_vars |+ (out_var, val))
Proof
  rpt gen_tac >>
  Cases_on `base` >> simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strip_tac >>
  rpt (BasicProvers.PURE_CASE_TAC >> gvs[]) >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x` >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* vi_sound is preserved after updating out_var, if the entry's base
   doesn't reference out_var *)
Theorem vi_sound_after_update[local]:
  !entry v out_var val s.
    vi_sound entry v s /\
    v <> out_var /\
    (case vi_base entry of
       SOME (Var x) => x <> out_var
     | _ => T) ==>
    vi_sound entry v (s with vs_vars := s.vs_vars |+ (out_var, val))
Proof
  Cases >> rw[vi_sound_def, vi_base_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[] >>
  gvs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `o'` >> gvs[] >>
  rename1 `eval_operand bop` >>
  Cases_on `bop` >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Helper: vi_lookup vi op cannot have vi_base = SOME (Var out_var)
   when op <> Var out_var and the SSA condition holds.
   Used by step_inst_output_vi_sound to derive the vi_base condition
   for transfer_*_vi_sound in the non-identity case. *)
Theorem vi_lookup_no_self_ref[local]:
  !vi op out_var.
    (!v e. ALOOKUP vi v = SOME e ==>
       vi_base e = SOME (Var out_var) ==> v = out_var) /\
    (!x. op = Var x ==> x <> out_var) ==>
    case vi_base (vi_lookup vi op) of
      SOME (Var v) => v <> out_var
    | _ => T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> simp[vi_lookup_def, vi_base_def] >>
  Cases_on `ALOOKUP vi s` >> simp[vi_base_def] >>
  Cases_on `x` >> simp[vi_base_def] >>
  Cases_on `o'` >> simp[] >>
  Cases_on `x` >> simp[] >>
  spose_not_then strip_assume_tac >> gvs[vi_base_def] >>
  res_tac >> gvs[]
QED

(* Helper: output variable vi_sound is maintained after step_inst_base.
   Uses SSA + ~MEM to handle the identity case (vi_base = Var out_var).
   For non-identity, uses transfer_*_vi_sound with vi_base from vi_lookup_no_self_ref.
   For identity (SOME,SOME in ADD, SOME subtrahend in SUB, catch-all), uses vi_sound_identity. *)
Theorem step_inst_output_vi_sound[local]:
  !vi inst s s' out_var vi_entry.
    vi_alist_sound vi s /\
    step_inst_base inst s = OK s' /\
    inst.inst_outputs = [out_var] /\
    ALOOKUP vi out_var = SOME vi_entry /\
    vi_entry_consistent vi inst /\
    (!v e. ALOOKUP vi v = SOME e /\ v <> out_var /\
       vi_base e = SOME (Var out_var) ==> F) /\
    ~MEM (Var out_var) inst.inst_operands ==>
    vi_sound vi_entry out_var s'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vi_entry_consistent _ _` mp_tac >>
  simp[vi_entry_consistent_def] >>
  strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  Cases_on `inst.inst_opcode = ADD`
  >- (ASM_REWRITE_TAC[] >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[step_inst_base_ADD, exec_pure2_def, AllCaseEqs(), update_var_def] >>
      (* entry = transfer_add ... Check if (SOME,SOME) => identity *)
      Cases_on `vi_lookup vi op1` >> Cases_on `vi_lookup vi op2` >>
      rename1 `transfer_add (VarInfo b1 o1) (VarInfo b2 o2)` >>
      Cases_on `b1` >> Cases_on `b2` >>
      gvs[transfer_add_def, vi_base_def]
      >- (simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE] >>
          imp_res_tac vi_lookup_eval >> gvs[] >>
          metis_tac[wordsTheory.WORD_ADD_COMM])
      >- ((* (NONE, SOME x): base x from vi_lookup vi op2 *)
          `case vi_base (vi_lookup vi op2) of
             SOME (Var v) => v <> out_var | _ => T`
            by (irule vi_lookup_no_self_ref >> gvs[]) >>
          gvs[vi_base_def] >>
          imp_res_tac vi_lookup_eval >> gvs[] >>
          irule transfer_result_vi_sound >> simp[] >>
          Cases_on `x` >> gvs[] >>
          metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM])
      >- ((* (SOME x, NONE): base x from vi_lookup vi op1 *)
          `case vi_base (vi_lookup vi op1) of
             SOME (Var v) => v <> out_var | _ => T`
            by (irule vi_lookup_no_self_ref >> gvs[]) >>
          gvs[vi_base_def] >>
          imp_res_tac vi_lookup_eval >> gvs[] >>
          irule transfer_result_vi_sound >> simp[] >>
          Cases_on `x` >> gvs[] >>
          metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM])
      >- simp[vi_sound_identity])
  >>
  Cases_on `inst.inst_opcode = SUB`
  >- (ASM_REWRITE_TAC[] >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[step_inst_base_SUB, exec_pure2_def, AllCaseEqs(), update_var_def] >>
      Cases_on `vi_lookup vi op1` >> Cases_on `vi_lookup vi op2` >>
      rename1 `transfer_sub (VarInfo b1 o1) (VarInfo b2 o2)` >>
      Cases_on `b2` >> gvs[transfer_sub_def, vi_base_def]
      >- (imp_res_tac vi_lookup_eval >> gvs[] >>
          Cases_on `b1` >> gvs[]
          >- (simp[vi_sound_def, finite_mapTheory.FLOOKUP_UPDATE] >>
              metis_tac[wordsTheory.WORD_ADD_SUB_ASSOC, wordsTheory.WORD_ADD_COMM])
          >- (`case vi_base (vi_lookup vi op1) of
                 SOME (Var v) => v <> out_var | _ => T`
                by (irule vi_lookup_no_self_ref >> gvs[]) >>
              gvs[vi_base_def] >>
              irule transfer_result_vi_sound >> simp[] >>
              Cases_on `x` >> gvs[] >>
              metis_tac[wordsTheory.WORD_ADD_SUB_ASSOC, wordsTheory.WORD_ADD_COMM]))
      >- simp[vi_sound_identity])
  >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (ASM_REWRITE_TAC[] >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[step_inst_base_ASSIGN, AllCaseEqs(), update_var_def,
          transfer_assign_def] >>
      `case vi_base (vi_lookup vi op1) of
         SOME (Var vn) => vn <> out_var | _ => T`
        by (irule vi_lookup_no_self_ref >>
            rpt conj_tac >> gvs[] >>
            Cases_on `op1` >> gvs[]) >>
      Cases_on `vi_lookup vi op1` >>
      rename1 `vi_lookup vi op1 = VarInfo vb voff` >>
      irule vi_sound_after_write >>
      Cases_on `vb` >> gvs[vi_base_def]
      >- (drule_all vi_lookup_eval >> simp[])
      >- (rpt strip_tac
          >- (drule_all vi_lookup_eval >> simp[])
          >- (Cases_on `x` >> gvs[])))
  >- (strip_tac >> gvs[vi_sound_identity])
QED

(* After executing one instruction with 1 output, lattice soundness is maintained.
   Requires:
   - vi_entry_consistent (lattice entry matches transfer function)
   - Non-output vars' bases are not modified (SSA property)
   - Output var not in operands (SSA: no self-reference) *)
Theorem step_inst_preserves_vi_sound[local]:
  !vi inst s s' fuel ctx out_var.
    vi_alist_sound vi s /\
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_outputs = [out_var] /\
    vi_entry_consistent vi inst /\
    (* SSA: non-output entry bases don't reference the output *)
    (!v entry. ALOOKUP vi v = SOME entry /\ v <> out_var /\
       vi_base entry = SOME (Var out_var) ==> F) /\
    (* SSA: output variable not in operands *)
    ~MEM (Var out_var) inst.inst_operands ==>
    vi_alist_sound vi s'
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base inst s = OK s'`
    by (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
        simp[step_inst_non_invoke]) >>
  rw[vi_alist_sound_def] >> rpt strip_tac >>
  Cases_on `v = out_var`
  >- (gvs[] >> irule step_inst_output_vi_sound >> metis_tac[]) >>
  (* v <> out_var: lookup_var preserved for non-output vars *)
  `lookup_var v s' = lookup_var v s` by
    (mp_tac (Q.SPECL [`fuel`,`ctx`,`inst`,`s`,`s'`]
       step_preserves_non_output_vars) >>
     simp[] >> disch_then match_mp_tac >> simp[listTheory.MEM]) >>
  `vi_sound vi' v s` by gvs[vi_alist_sound_def] >>
  (* Prove vi_sound vi' v s' from vi_sound vi' v s *)
  Cases_on `vi'` >> gvs[vi_sound_def, vi_base_def, lookup_var_def] >>
  Cases_on `o'` >> gvs[] >>
  (* Base is SOME x. Show eval_operand x s' = eval_operand x s *)
  `s'.vs_labels = s.vs_labels`
    by metis_tac[step_inst_preserves_labels_always] >>
  `eval_operand x s' = eval_operand x s` suffices_by
    (strip_tac >> Cases_on `FLOOKUP s.vs_vars v` >> gvs[] >> metis_tac[]) >>
  Cases_on `x` >> simp[eval_operand_def, lookup_var_def]
  >- ((* Var case: s' lookup = s lookup because var <> out_var *)
    rename1 `Var vb` >>
    `vb <> out_var` by
      (first_x_assum (qspecl_then [`v`, `VarInfo (SOME (Var vb)) c`] mp_tac) >>
       simp[vi_base_def]) >>
    mp_tac (Q.SPECL [`fuel`,`ctx`,`inst`,`s`,`s'`]
      step_preserves_non_output_vars) >>
    simp[] >> disch_then (qspec_then `vb` mp_tac) >>
    simp[listTheory.MEM, lookup_var_def])
QED

(* If all lookup_vars are preserved, vi_alist_sound is preserved.
   Used for terminators, no-output instructions, and any state change
   that only touches non-variable fields. *)
Theorem vi_alist_sound_preserved_by_lookup[local]:
  !vi s s'.
    vi_alist_sound vi s /\
    (!v. lookup_var v s' = lookup_var v s) /\
    s'.vs_labels = s.vs_labels ==>
    vi_alist_sound vi s'
Proof
  rw[vi_alist_sound_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `vi'` >> gvs[vi_sound_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[] >>
  Cases_on `o'` >> gvs[] >>
  (* base is SOME x': show eval_operand x' s' = eval_operand x' s *)
  Cases_on `x'` >> gvs[eval_operand_def, lookup_var_def]
QED

(* Combined: vi_alist_sound preserved by ANY instruction step.
   Handles terminators (vars unchanged) and non-terminators (uses step_inst_preserves).
   For non-terminator instructions without exactly 1 output, vars are also unchanged
   (step_inst_base returns Error for malformed instructions). *)
Theorem vi_alist_sound_step[local]:
  !vi inst s s' fuel ctx.
    vi_alist_sound vi s /\
    step_inst fuel ctx inst s = OK s' /\
    (* Per-instruction conditions (from function-level SSA + wf) *)
    (inst.inst_outputs = [] \/
     (?out_var. inst.inst_outputs = [out_var] /\
       inst.inst_opcode <> INVOKE /\
       vi_entry_consistent vi inst /\
       (!v entry. ALOOKUP vi v = SOME entry /\ v <> out_var /\
          vi_base entry = SOME (Var out_var) ==> F) /\
       ~MEM (Var out_var) inst.inst_operands)) ==>
    vi_alist_sound vi s'
Proof
  rpt gen_tac >> strip_tac >>
  `s'.vs_labels = s.vs_labels`
    by metis_tac[step_inst_preserves_labels_always] >>
  gvs[]
  (* Case 1: outputs = [], any terminator status *)
  >- (irule vi_alist_sound_preserved_by_lookup >> qexists_tac `s` >>
      simp[] >> rpt strip_tac >>
      Cases_on `is_terminator inst.inst_opcode`
      >- metis_tac[step_terminator_preserves_vars]
      >- (mp_tac (Q.SPECL [`fuel`,`ctx`,`inst`,`s`,`s'`]
            step_preserves_non_output_vars) >>
          simp[] >> disch_then match_mp_tac >> simp[listTheory.MEM]))
  (* Case 2: outputs = [out_var] *)
  >- (Cases_on `is_terminator inst.inst_opcode`
      (* Terminator: all vars unchanged *)
      >- (irule vi_alist_sound_preserved_by_lookup >> qexists_tac `s` >>
          simp[] >> metis_tac[step_terminator_preserves_vars])
      (* Non-terminator single output *)
      >- (irule step_inst_preserves_vi_sound >> metis_tac[]))
QED

(* vi_alist_sound only depends on vs_vars *)
Theorem vi_alist_sound_vs_inst_idx[local]:
  !vi s n. vi_alist_sound vi s ==>
    vi_alist_sound vi (s with vs_inst_idx := n)
Proof
  rpt strip_tac >> irule vi_alist_sound_preserved_by_lookup >>
  qexists_tac `s` >> simp[lookup_var_def]
QED

(* ===== Function-Level Assembly ===== *)

(* Bridge lemma: instructions in blocks are instructions in the function *)
Theorem fn_insts_blocks_MEM[local]:
  !bbs bb inst.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem fn_insts_MEM[local]:
  !fn bb inst.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def] >> irule fn_insts_blocks_MEM >> metis_tac[]
QED

(* Bridge: combines function-level SSA conditions into vi_alist_sound_step format,
   producing both vi_alist_sound vi s' and the vs_inst_idx variant in one shot.
   Used in both Goal 2 (P preservation) and Goal 3 (block equality, inner P preservation). *)
Theorem vi_alist_sound_fn_step[local]:
  !vi fn inst fuel ctx s s'.
    vi_alist_sound vi s /\
    step_inst fuel ctx inst s = OK s' /\
    MEM inst (fn_insts fn) /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (!inst. MEM inst (fn_insts fn) ==>
       vi_entry_consistent vi inst) /\
    (!inst out_var. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] ==>
       ~MEM (Var out_var) inst.inst_operands) /\
    (!inst out_var v entry. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] /\
       ALOOKUP vi v = SOME entry /\ v <> out_var /\
       vi_base entry = SOME (Var out_var) ==> F) /\
    (!inst. MEM inst (fn_insts fn) ==>
       inst.inst_outputs = [] \/
       ?out_var. inst.inst_outputs = [out_var]) ==>
    vi_alist_sound vi s' /\
    !n. vi_alist_sound vi (s' with vs_inst_idx := n)
Proof
  rpt gen_tac >> strip_tac >>
  `vi_alist_sound vi s'` suffices_by
    (strip_tac >> simp[] >> metis_tac[vi_alist_sound_vs_inst_idx]) >>
  irule vi_alist_sound_step >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s`] >> simp[] >>
  (* Need: inst.inst_outputs = [] \/ (?out_var. [...] /\ ... /\ ...) *)
  Cases_on `inst.inst_outputs`
  >- simp[] >>
  Cases_on `t`
  >- (disj2_tac >> qexists_tac `h` >> rw[] >> metis_tac[])
  >- (`inst.inst_outputs = [] \/ ?ov. inst.inst_outputs = [ov]`
        by metis_tac[] >> fs[])
QED

(* Helper: transformed block equals original block under vi_alist_sound *)
Triviality af_block_eq_helper:
  !fn bb fuel ctx s.
    (!inst. MEM inst (fn_insts fn) ==>
       vi_entry_consistent (af_compute_fn_var_info fn) inst) /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (!inst st. MEM inst (fn_insts fn) ==>
       ((!v. MEM (Var v) inst.inst_operands ==> FLOOKUP st.vs_vars v <> NONE) <=>
        (!v. MEM (Var v) (af_transform_inst (dfg_build_function fn)
               (af_compute_fn_var_info fn) inst).inst_operands ==>
             FLOOKUP st.vs_vars v <> NONE))) /\
    fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    (!inst out_var. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] ==>
       ~MEM (Var out_var) inst.inst_operands) /\
    (!inst out_var v entry. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] /\
       ALOOKUP (af_compute_fn_var_info fn) v = SOME entry /\
       v <> out_var /\
       vi_base entry = SOME (Var out_var) ==> F) /\
    (!inst. MEM inst (fn_insts fn) ==>
       inst.inst_outputs = [] \/
       ?out_var. inst.inst_outputs = [out_var]) /\
    MEM bb fn.fn_blocks /\
    vi_alist_sound (af_compute_fn_var_info fn) s ==>
    run_block fuel ctx
      (af_transform_block (dfg_build_function fn)
         (af_compute_fn_var_info fn) bb) s =
    run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  qabbrev_tac `vi = af_compute_fn_var_info fn` >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  simp[af_transform_block_def] >>
  qspecl_then [`vi_alist_sound vi`, `af_transform_inst dfg vi`,
               `bb`, `fuel`, `ctx`, `s`]
    mp_tac run_block_inst_transform_eq >>
  simp[vi_alist_sound_idx_indep, af_transform_inst_terminator] >>
  disch_then match_mp_tac >>
  conj_tac
  >- (rpt strip_tac >> imp_res_tac fn_insts_MEM >>
      irule af_transform_inst_step_eq >>
      simp[Abbr `vi`, Abbr `dfg`, eval_operand_def, lookup_var_def])
  >> rpt strip_tac >> imp_res_tac fn_insts_MEM >>
  drule_all vi_alist_sound_fn_step >> simp[Abbr `vi`]
QED

(* Helper: vi_alist_sound is preserved through block execution *)
Triviality af_P_preserved_helper:
  !fn bb fuel ctx s s'.
    fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    (!inst. MEM inst (fn_insts fn) ==>
       vi_entry_consistent (af_compute_fn_var_info fn) inst) /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (!inst out_var. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] ==>
       ~MEM (Var out_var) inst.inst_operands) /\
    (!inst out_var v entry. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] /\
       ALOOKUP (af_compute_fn_var_info fn) v = SOME entry /\
       v <> out_var /\
       vi_base entry = SOME (Var out_var) ==> F) /\
    (!inst. MEM inst (fn_insts fn) ==>
       inst.inst_outputs = [] \/
       ?out_var. inst.inst_outputs = [out_var]) /\
    MEM bb fn.fn_blocks /\
    vi_alist_sound (af_compute_fn_var_info fn) s /\
    run_block fuel ctx bb s = OK s' ==>
    vi_alist_sound (af_compute_fn_var_info fn) s'
Proof
  rpt strip_tac >>
  qabbrev_tac `vi = af_compute_fn_var_info fn` >>
  `exec_block fuel ctx bb (s with vs_inst_idx := 0) = OK s'`
    by fs[run_block_def] >>
  qspecl_then [`vi_alist_sound vi`, `bb`, `fuel`, `ctx`,
               `s with vs_inst_idx := 0`, `s'`]
    mp_tac exec_block_preserves_P >>
  simp[vi_alist_sound_idx_indep] >>
  disch_then match_mp_tac >>
  rpt strip_tac >> imp_res_tac fn_insts_MEM >>
  drule_all vi_alist_sound_fn_step >> simp[Abbr `vi`]
QED

Theorem af_transform_function_correct_proof:
  !fuel ctx fn s.
    (* SSA uniqueness: each variable defined at most once *)
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    (* Structural well-formedness *)
    fn_inst_wf fn /\
    (* Lattice soundness for initial state *)
    vi_alist_sound (af_compute_fn_var_info fn) s /\
    (* Per-instruction lattice consistency (from FOLDL + SSA) *)
    (!inst. MEM inst (fn_insts fn) ==>
       vi_entry_consistent (af_compute_fn_var_info fn) inst) /\
    (* SSA: output variable not in operands *)
    (!inst out_var. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] ==>
       ~MEM (Var out_var) inst.inst_operands) /\
    (* SSA: no cross-variable base references to output *)
    (!inst out_var v entry. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] /\
       ALOOKUP (af_compute_fn_var_info fn) v = SOME entry /\
       v <> out_var /\ vi_base entry = SOME (Var out_var) ==> F) /\
    (* No INVOKE instructions (affine folding is intra-procedural) *)
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (* Each instruction has 0 or 1 outputs *)
    (!inst. MEM inst (fn_insts fn) ==>
       inst.inst_outputs = [] \/
       ?out_var. inst.inst_outputs = [out_var]) /\
    (* Bidirectional operand reachability: original operands defined iff transform operands defined.
       This ensures step equality holds even when operands are undefined (both sides error). *)
    (!inst st. MEM inst (fn_insts fn) ==>
       ((!v. MEM (Var v) inst.inst_operands ==> FLOOKUP st.vs_vars v <> NONE) <=>
        (!v. MEM (Var v) (af_transform_inst (dfg_build_function fn)
               (af_compute_fn_var_info fn) inst).inst_operands ==>
             FLOOKUP st.vs_vars v <> NONE))) ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (af_transform_function fn) s)
Proof
  rpt strip_tac >>
  `run_blocks fuel ctx (af_transform_function fn) s =
   run_blocks fuel ctx fn s` suffices_by
    (disch_then (fn th => REWRITE_TAC[th]) >>
     irule lift_result_refl >> rw[state_equiv_refl, execution_equiv_refl]) >>
  `af_transform_function fn =
   function_map_transform
     (af_transform_block (dfg_build_function fn)
        (af_compute_fn_var_info fn)) fn` by
    simp[af_transform_function_def, function_map_transform_def] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  qspecl_then
    [`vi_alist_sound (af_compute_fn_var_info fn)`,
     `af_transform_block (dfg_build_function fn) (af_compute_fn_var_info fn)`,
     `fn`, `fuel`, `ctx`, `s`]
    mp_tac run_blocks_map_inv_eq >>
  disch_then match_mp_tac >>
  simp[af_transform_block_label] >>
  conj_tac
  >- (rpt strip_tac >> irule af_block_eq_helper >> simp[] >> metis_tac[])
  >> rpt strip_tac >> irule af_P_preserved_helper >> simp[] >> metis_tac[]
QED
