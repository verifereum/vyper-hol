(*
 * Algebraic Optimization Pass — Definitions
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Ports vyper/venom/passes/algebraic_optimization.py to HOL4.
 *
 * Reduces algebraically evaluatable expressions via:
 *   - Iszero chain optimization (forward-computed targets)
 *   - Producer-based pattern matching (balance→selfbalance, signextend nesting)
 *   - Per-opcode peephole rules
 *   - Comparator boundary rewrites with iszero insertion/removal
 *
 * IMPORTANT: Python IR reverses operands from EVM stack order.
 * HOL4 uses semantic (EVM) order. So Python operands[0] = HOL4 op2,
 * and Python operands[1] = HOL4 op1. The peephole rules below are
 * written for HOL4 semantic order: [op1; op2] where
 *   SUB → op1 - op2, DIV → op1 / op2, GT → op1 > op2, etc.
 *
 * TOP-LEVEL:
 *   ao_transform_function     — function-level transform
 *   ao_peephole_inst          — main peephole dispatch
 *   ao_handle_offset_inst     — add(lit,label) → offset
 *   ao_opt_producer           — producer-based pattern rewrites
 *
 * Source: vyper/venom/passes/algebraic_optimization.py
 *)

Theory algebraicOptDefs
Ancestors
  passSimulationDefs passSharedDefs dfgDefs dfgAnalysisProps rangeAnalysisDefs
  venomExecSemantics venomInst
Libs
  pred_setTheory integerTheory

(* ===== Utilities ===== *)

Definition ao_fresh_var_def:
  ao_fresh_var (id:num) (suffix:string) =
    STRCAT "ao_" (STRCAT (toString id) (STRCAT "_" suffix))
End

(* Fresh instruction ID for helper instructions in 1-to-N expansions.
   Python creates genuinely new IRInstruction objects (identity by reference);
   in HOL4 we need explicit distinct IDs.

   Convention: the modified original instruction keeps inst.inst_id.
   Helper instructions inserted before it get IDs from a range that is
   disjoint from original IDs.  We achieve this by offsetting into a
   high range: max_id is the maximum instruction ID in the function, passed
   in as `mid` and threaded through ao_transform_block, ao_transform_inst,
   ao_peephole_inst, ao_opt_eq, ao_opt_comparator, ao_cmp_prefer_iz_{zero,max,
   general} and ao_cmp_flip_apply_inst.
   Helper k for original inst_id gets  max_id + 1 + inst_id * 3 + k
   where k ∈ {0,1,2}.  This is injective and > max_id, so it cannot
   collide with any original ID or with helpers from other instructions.

   Output-safety: inst_id is internal instruction identity (the analogue of
   Python's object identity) and is never emitted to bytecode.  Threading
   `mid` only ensures each produced instruction gets a distinct id; it changes
   no opcode, operand or output, so the emitted code is identical.  Distinct
   ids are in fact REQUIRED for correctness, not merely provability: a single
   shared id per expansion would break fn_inst_ids_distinct and would mis-key
   the id-indexed ALOOKUPs in ao_cmp_flip_apply_inst. *)
Definition ao_fresh_id_def:
  ao_fresh_id (max_id:num) (id:num) (slot:num) = max_id + 1 + id * 3 + slot
End

(* Maximum instruction ID in a function.  Used to compute ao_fresh_id base. *)
Definition fn_max_inst_id_def:
  fn_max_inst_id fn =
    FOLDL MAX 0
      (MAP (\i. i.inst_id) (fn_insts fn))
End

(* Truthy instructions: can accept a truthy value (0/nonzero).
   Matches Python TRUTHY_INSTRUCTIONS = ("iszero", "jnz", "assert", "assert_unreachable").
   ISZERO is included for use-analysis (OR truthy, EQ prefer_iszero).
   In iszero chain optimization, ISZERO uses are filtered separately. *)
Definition is_truthy_inst_def:
  is_truthy_inst opc <=>
    opc = ISZERO \/ opc = JNZ \/ opc = ASSERT \/ opc = ASSERT_UNREACHABLE
End

(* prefer_iszero: all uses are assert or iszero.
   Matches Python: all(i.opcode in ("assert", "iszero") for i in uses) *)
Definition ao_all_prefer_iszero_def:
  ao_all_prefer_iszero dfg inst =
    case inst.inst_outputs of
      [out_var] =>
        EVERY (\use. use.inst_opcode = ASSERT \/ use.inst_opcode = ISZERO)
              (dfg_get_uses dfg out_var)
    | _ => F
End

(* all uses are truthy.
   Matches Python: all(i.opcode in TRUTHY_INSTRUCTIONS for i in uses) *)
Definition ao_all_truthy_def:
  ao_all_truthy dfg inst =
    case inst.inst_outputs of
      [out_var] =>
        EVERY (\use. is_truthy_inst use.inst_opcode)
              (dfg_get_uses dfg out_var)
    | _ => F
End

(* ===== Offset Conversion ===== *)

(*
 * Python: if operands[0] is Lit and operands[1] is Label → change opcode to "offset".
 * Since ADD is EVM (reversed): Python operands[0] = HOL4 op2, operands[1] = HOL4 op1.
 * So condition: op2 = Lit, op1 = Label → HOL4 ADD pattern [Label l; Lit v].
 * OFFSET is non-EVM: semantics expects [offset_op; Label lbl] = [Lit v; Label l].
 * Must swap operands when converting ADD (EVM convention) → OFFSET (non-EVM convention).
 *)
Definition ao_handle_offset_inst_def:
  ao_handle_offset_inst inst =
    if inst.inst_opcode = ADD then
      case inst.inst_operands of
        [Label l; Lit v] =>
          inst with <| inst_opcode := OFFSET;
                       inst_operands := [Lit v; Label l] |>
      | _ => inst
    else inst
End

(* ===== Forward Iszero Target Computation ===== *)

(*
 * Compute iszero chain targets in a forward pass.
 *
 * iszero_targets: maps variable name → chain (operand list)
 *   where chain = [root; 1st_iszero_out; 2nd; ...; final_out]
 *
 * For iszero chains:
 *   If inst is iszero with input inp:
 *     prev = targets[inp] if inp is a variable in targets, else [inp]
 *     targets[output] = prev ++ [Var output]
 *)
Definition ao_compute_iszero_step_def:
  ao_compute_iszero_step targets (inst : instruction) =
    if inst.inst_opcode = ISZERO then
      case (inst.inst_operands, inst.inst_outputs) of
        ([inp], [out_var]) =>
          let prev =
            case inp of
              Var v => (case ALOOKUP targets v of
                          SOME chain => chain
                        | NONE => [inp])
            | _ => [inp] in
          (out_var, SNOC (Var out_var) prev) :: targets
      | _ => targets
    else targets
End

Definition ao_compute_iszero_targets_def:
  ao_compute_iszero_targets (insts : instruction list) =
    FOLDL ao_compute_iszero_step [] insts
End

Definition ao_compute_fn_iszero_targets_def:
  ao_compute_fn_iszero_targets fn =
    ao_compute_iszero_targets (fn_insts fn)
End

(* ===== Iszero Chain Resolution ===== *)

(*
 * Resolve iszero chain for a single operand at a specific use site.
 *
 * Python: _rewrite_iszero_uses processes each non-iszero instruction.
 * For each operand that is a chain output:
 *   chain = (root, 1st_iszero_out, ..., op)
 *   depth = len(chain) - 1
 *   For truthy contexts (jnz, assert, assert_unreachable): keep = depth % 2
 *   For other contexts: keep = 2 - depth % 2
 *   If keep < depth: replace op with chain[keep]
 *
 * Note: iszero uses are skipped (they preserve the chain).
 *
 * The extra `get_label (EL keep chain) = NONE` guard below has no Python
 * counterpart and never fires on any IR Vyper emits: chain roots are
 * iszero operands and chain interior elements are iszero outputs, none of
 * which are labels in well-formed code, so the substituted operand is
 * always a non-label and the guard is a no-op (zero bytecode divergence).
 * It is kept only as a soundness refinement: get_successors-preservation
 * for a resolved JNZ condition needs the replacement to be a non-label,
 * and "chain elements are non-labels" is NOT derivable from inst_wf /
 * wf_function / wf_ssa (ISZERO operands and JNZ conditions are
 * label-unconstrained there). Removing the guard would require adding a
 * new well-formedness precondition, which we avoid.
 *)
Definition ao_resolve_iszero_op_def:
  ao_resolve_iszero_op targets use_opcode op =
    case op of
      Var v =>
        (case ALOOKUP targets v of
           NONE => op
         | SOME chain =>
             (* Skip iszero uses *)
             if use_opcode = ISZERO then op
             else
               let depth = LENGTH chain - 1 in
               let keep =
                 if use_opcode = JNZ \/ use_opcode = ASSERT \/
                    use_opcode = ASSERT_UNREACHABLE then
                   depth MOD 2
                 else
                   2 - depth MOD 2 in
               if keep < depth /\ keep < LENGTH chain /\
                  get_label (EL keep chain) = NONE then
                 EL keep chain
               else op)
    | _ => op
End

(* Apply iszero resolution to all operands of an instruction *)
Definition ao_resolve_iszero_inst_def:
  ao_resolve_iszero_inst targets inst =
    inst with inst_operands :=
      MAP (ao_resolve_iszero_op targets inst.inst_opcode) inst.inst_operands
End

(* ===== Producer-Based Rules ===== *)

(*
 * Python: _rewrite_or_skip_producer(inst) — pattern matching on producers.
 * Returns SOME result if rewrite applied or opcode should be skipped.
 * Returns NONE to fall through to local peephole rules.
 *
 * Rules:
 *   balance(address()) → selfbalance()
 *   extcodesize → skip (no optimizations)
 *   signextend(n, signextend(m, x)) where n >=+ m → assign(x)
 *     (>=+ is the UNSIGNED word compare: the byte-count operand is a
 *      magnitude, matching Python's plain-int comparison.  It agrees with
 *      the signed >= on every width that can actually occur (0..31), so this
 *      is a model-faithfulness fix, not a change to the emitted output.)
 *)
Definition ao_opt_producer_def:
  ao_opt_producer dfg inst =
    if inst.inst_opcode = BALANCE then
      case inst.inst_operands of
        [op] =>
          (case op of
             Var v =>
               (case dfg_get_def dfg v of
                  SOME producer =>
                    if producer.inst_opcode = ADDRESS then
                      SOME [inst with <| inst_opcode := SELFBALANCE;
                                         inst_operands := [] |>]
                    else SOME [inst]  (* no other rules for balance *)
                | NONE => SOME [inst])
           | _ => SOME [inst])
      | _ => SOME [inst]
    else if inst.inst_opcode = EXTCODESIZE then
      SOME [inst]  (* no optimizations for extcodesize *)
    else if inst.inst_opcode = SIGNEXTEND then
      case inst.inst_operands of
        [Lit w; x] =>
          (case x of
             Var v =>
               (case dfg_get_def dfg v of
                  SOME producer =>
                    if producer.inst_opcode = SIGNEXTEND then
                      (case producer.inst_operands of
                         [Lit inner_w; _] =>
                           if w >=+ inner_w then
                             SOME [inst with <| inst_opcode := ASSIGN;
                                                inst_operands := [x] |>]
                           else NONE
                       | _ => NONE)
                    else NONE
                | NONE => NONE)
           | _ => NONE)
      | _ => NONE
    else NONE
End

(* ===== Per-Opcode Peephole Helpers ===== *)

(*
 * Operand order key (HOL4 semantic = EVM order):
 *   SHL/SHR/SAR [shift_amount; value]  — shift_amount is op1
 *   SIGNEXTEND [n; x]                  — n is byte count
 *   EXP [base; exponent]
 *   SUB [minuend; subtrahend]          — result = op1 - op2
 *   DIV [dividend; divisor]            — result = op1 / op2
 *   MOD [dividend; divisor]
 *   GT/LT/SGT/SLT [a; b]             — result = a > b (GT), a < b (LT)
 *
 * For commutative ops (ADD, MUL, AND, OR, XOR, EQ):
 *   Python pre-flips literal to operands[0] (= HOL4 op2).
 *   We check op2 for literal values to match Python.
 *)

(* Shift: x >> 0 = x << 0 = x
   HOL4 order: [shift_amount; value] *)
Definition ao_opt_shift_def:
  ao_opt_shift inst =
    case inst.inst_operands of
      [shift_amt; x] =>
        if lit_eq shift_amt 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>]
        else [inst]
    | _ => [inst]
End

(* Signextend: signextend(n >= 31, x) → x
   Range-based: if x is already in valid signed range for (n+1) bytes → x
   HOL4 order: [n; x]
   Note: nested signextend is handled by producer rules *)
Definition ao_opt_signextend_def:
  ao_opt_signextend ra lbl idx inst =
    case inst.inst_operands of
      [n_op; x] =>
        (case n_op of
           Lit w =>
             if w >= 31w then
               [inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>]
             else
               let n = w2n w in
               if n < 31 then
                 let x_range = range_get_range ra lbl idx x in
                 if ~vr_is_top x_range then
                   let bits = 8 * (n + 1) in
                   let signed_min = ~(&(2 ** (bits - 1))) in
                   let signed_max = &(2 ** (bits - 1)) - 1 in
                   if vr_lo x_range >= signed_min /\ vr_hi x_range <= signed_max then
                     [inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>]
                   else [inst]
                 else [inst]
               else [inst]
         | _ => [inst])
    | _ => [inst]
End

(* Exp: x**0→1, x**1→x, 1**x→1, 0**x→iszero(x)
   HOL4 order: [base; exponent] *)
Definition ao_opt_exp_def:
  ao_opt_exp inst =
    case inst.inst_operands of
      [base_op; exp_op] =>
        if lit_eq exp_op 0w then                    (* x^0 = 1 *)
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>]
        else if lit_eq exp_op 1w then               (* x^1 = x *)
          [inst with <| inst_opcode := ASSIGN; inst_operands := [base_op] |>]
        else if lit_eq base_op 1w then              (* 1^x = 1 *)
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>]
        else if lit_eq base_op 0w then              (* 0^x = iszero(x) *)
          [inst with <| inst_opcode := ISZERO; inst_operands := [exp_op] |>]
        else [inst]
    | _ => [inst]
End

(* Add/Sub/Xor identities
   HOL4 order: [op1; op2] where SUB = op1 - op2.
   Python pre-flips literal to operands[0] = HOL4 op2 for ADD/XOR (commutative).
   SUB is not commutative; Python operands[0] = subtrahend = HOL4 op2. *)
Definition ao_opt_addsub_def:
  ao_opt_addsub inst =
    let opc = inst.inst_opcode in
    case inst.inst_operands of
      [op1; op2] =>
        (* x - x = 0, x ^ x = 0 *)
        if (opc = SUB \/ opc = XOR) /\ op1 = op2 then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
        (* For ADD/XOR (commutative): after pre-flip, literal at op2.
           For SUB: op2 is subtrahend. op2=0 → op1-0=op1. *)
        else if lit_eq op2 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [op1] |>]
        (* SUB: (-1) - x = NOT(x). op1=minuend=-1. *)
        else if opc = SUB /\ lit_eq op1 (0w - 1w) then
          [inst with <| inst_opcode := NOT; inst_operands := [op2] |>]
        (* XOR: x ^ (-1) = NOT(x). After pre-flip, literal at op2. *)
        else if opc = XOR /\ lit_eq op2 (0w - 1w) then
          [inst with <| inst_opcode := NOT; inst_operands := [op1] |>]
        else [inst]
    | _ => [inst]
End

(* And: x & MAX → x, x & 0 → 0
   Commutative: after pre-flip, literal at op2. *)
Definition ao_opt_and_def:
  ao_opt_and inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_eq op2 (0w - 1w) then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [op1] |>]
        else if lit_eq op1 0w \/ lit_eq op2 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
        else [inst]
    | _ => [inst]
End

(* Mul/Div/Mod identities
   MUL is commutative (pre-flip: literal at op2).
   DIV/MOD: [dividend; divisor]. Result = op1 / op2.
   Python operands[0] = HOL4 op2 for all.
   Power-of-two: div→shr, mul→shl, mod→and. *)
Definition ao_opt_muldiv_def:
  ao_opt_muldiv inst =
    let opc = inst.inst_opcode in
    case inst.inst_operands of
      [op1; op2] =>
        (* x * 0 = 0 (commutative), x / 0 handled by safe_div *)
        if lit_eq op1 0w \/ lit_eq op2 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
        (* MUL: x * 1 = x (literal at op2 after pre-flip)
           DIV/SDIV: x / 1 = x (divisor = op2 = 1) *)
        else if (opc = MUL \/ opc = Div \/ opc = SDIV) /\ lit_eq op2 1w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [op1] |>]
        (* MOD/SMOD: x % 1 = 0 (divisor = op2 = 1) *)
        else if (opc = Mod \/ opc = SMOD) /\ lit_eq op2 1w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
        (* Power-of-two reductions: op2 is the literal (divisor/multiplier) *)
        else (case op2 of
          Lit w =>
            if is_power_of_two w then
              let n = word_log2 w in
              if opc = Mod then
                [inst with <| inst_opcode := AND;
                              inst_operands := [op1; Lit (w - 1w)] |>]
              else if opc = Div then
                [inst with <| inst_opcode := SHR;
                              inst_operands := [Lit n; op1] |>]
              else if opc = MUL then
                [inst with <| inst_opcode := SHL;
                              inst_operands := [Lit n; op1] |>]
              else [inst]
            else [inst]
        | _ => [inst])
    | _ => [inst]
End

(* Or: x | MAX → MAX, x | 0 → x   (value-preserving cases only)
   Commutative: after pre-flip, literal at op2.
   Python _rule_or has a third, value-CHANGING case — x | nonzero_lit → 1 in
   truthy contexts — which lives in the separate ao_or_truthy_function
   mini-pass (phase 5; see "OR-truthy mini-pass" below), NOT here: this
   peephole runs inside the value-preserving per-instruction engine, which is
   not allowed to change any non-fresh variable's value. *)
Definition ao_opt_or_def:
  ao_opt_or dfg inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_eq op2 (0w - 1w) then
          [inst with <| inst_opcode := ASSIGN;
                        inst_operands := [Lit (0w - 1w)] |>]
        else if lit_eq op2 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [op1] |>]
        else [inst]
    | _ => [inst]
End

(* Eq: x==x→1, x==0→iszero(x), x==(-1)→iszero(~x),
       prefer_iszero: eq(x,y) → iszero(xor(x,y))
   Commutative: after pre-flip, literal at op2. *)
Definition ao_opt_eq_def:
  ao_opt_eq mid dfg inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>]
        else if lit_eq op2 0w then
          [inst with <| inst_opcode := ISZERO; inst_operands := [op1] |>]
        else if lit_eq op2 (0w - 1w) then
          let id = inst.inst_id in
          let tmp = ao_fresh_var id "not" in
          [<| inst_id := ao_fresh_id mid id 0; inst_opcode := NOT;
              inst_operands := [op1]; inst_outputs := [tmp] |>;
           inst with <| inst_opcode := ISZERO;
                        inst_operands := [Var tmp] |>]
        (* prefer_iszero: eq(x,y) → iszero(xor(x,y)) when uses are assert/iszero *)
        else if ao_all_prefer_iszero dfg inst then
          let id = inst.inst_id in
          let tmp = ao_fresh_var id "xor" in
          [<| inst_id := ao_fresh_id mid id 0; inst_opcode := XOR;
              inst_operands := [op1; op2]; inst_outputs := [tmp] |>;
           inst with <| inst_opcode := ISZERO;
                        inst_operands := [Var tmp] |>]
        else [inst]
    | _ => [inst]
End

(* ===== Comparator Optimization ===== *)

(*
 * Comparator optimizations (GT, LT, SGT, SLT).
 * HOL4 order: [op1; op2] where GT = op1 > op2.
 *
 * Boundary values:
 *   For GT (is_gt=T): almost_always=lo, never=hi, almost_never=hi-1
 *   For LT (is_gt=F): almost_always=hi, never=lo, almost_never=lo+1
 *   unsigned: lo=0, hi=MAX_UINT256
 *   signed: lo=INT256_MIN, hi=INT256_MAX
 *)

(* Unsigned boundaries *)
Definition ao_unsigned_boundaries_def:
  ao_unsigned_boundaries (is_gt : bool) =
    let lo = 0w : bytes32 in
    let hi = 0w - 1w in (* MAX_UINT256 *)
    if is_gt then (lo, hi, hi - 1w)   (* almost_always, never, almost_never *)
    else (hi, lo, lo + 1w)
End

(* Signed boundaries *)
Definition ao_signed_boundaries_def:
  ao_signed_boundaries (is_gt : bool) =
    let lo = i2w INT256_MIN : bytes32 in
    let hi = i2w INT256_MAX in
    if is_gt then (lo, hi, hi - 1w)
    else (hi, lo, lo + 1w)
End

(* Helper: validate range for comparison.
   Python guards: unsigned requires lo >= 0, signed requires hi <= MAX_INT256. *)
Definition ao_range_valid_for_cmp_def:
  ao_range_valid_for_cmp var_range (signed : bool) =
    if vr_is_top var_range then F
    else if signed then vr_hi var_range <= INT256_MAX
    else vr_lo var_range >= 0
End

(* Helper: wrap literal for comparison.
   Python: wrap256(lit, signed=signed). *)
Definition ao_wrap_lit_def:
  ao_wrap_lit (w : bytes32) (signed : bool) : int =
    if signed then w2i w else &(w2n w)
End

(* Range-based comparator optimization.
   Python: _try_range_cmp. *)
Definition ao_opt_cmp_range_def:
  ao_opt_cmp_range ra lbl idx inst is_gt signed =
    case inst.inst_operands of
      [op1; op2] =>
    if is_lit_op op1 /\ ~is_lit_op op2 then
      let var_range = range_get_range ra lbl idx op2 in
      if ~ao_range_valid_for_cmp var_range signed then NONE
      else
        let lit_val = ao_wrap_lit (THE (case op1 of Lit w => SOME w)) signed in
        if is_gt then
          if lit_val > vr_hi var_range then SOME (Lit 1w)
          else if lit_val <= vr_lo var_range then SOME (Lit 0w)
          else NONE
        else
          if lit_val < vr_lo var_range then SOME (Lit 1w)
          else if lit_val >= vr_hi var_range then SOME (Lit 0w)
          else NONE
    else if ~is_lit_op op1 /\ is_lit_op op2 then
      let var_range = range_get_range ra lbl idx op1 in
      if ~ao_range_valid_for_cmp var_range signed then NONE
      else
        let lit_val = ao_wrap_lit (THE (case op2 of Lit w => SOME w)) signed in
        if is_gt then
          if vr_lo var_range > lit_val then SOME (Lit 1w)
          else if vr_hi var_range <= lit_val then SOME (Lit 0w)
          else NONE
        else
          if vr_hi var_range < lit_val then SOME (Lit 1w)
          else if vr_lo var_range >= lit_val then SOME (Lit 0w)
          else NONE
    else NONE
    | _ => NONE
End

(* Helper: prefer_iszero + almost_always with val=0
   gt x 0 in iszero context → iszero(iszero(x)) *)
Definition ao_cmp_prefer_iz_zero_def:
  ao_cmp_prefer_iz_zero mid id op1 inst =
    let tmp = ao_fresh_var id "iz" in
    [<| inst_id := ao_fresh_id mid id 0; inst_opcode := ISZERO;
        inst_operands := [op1]; inst_outputs := [tmp] |>;
     inst with <| inst_opcode := ISZERO;
                  inst_operands := [Var tmp] |>]
End

(* Helper: prefer_iszero + almost_always with val=-1
   slt x MAX in iszero context → iszero(iszero(not(x))) *)
Definition ao_cmp_prefer_iz_max_def:
  ao_cmp_prefer_iz_max mid id op1 inst =
    let inner = ao_fresh_var id "not" in
    let tmp = ao_fresh_var id "iz" in
    [<| inst_id := ao_fresh_id mid id 0; inst_opcode := NOT;
        inst_operands := [op1]; inst_outputs := [inner] |>;
     <| inst_id := ao_fresh_id mid id 1; inst_opcode := ISZERO;
        inst_operands := [Var inner]; inst_outputs := [tmp] |>;
     inst with <| inst_opcode := ISZERO;
                  inst_operands := [Var tmp] |>]
End

(* Helper: prefer_iszero + almost_always with general val
   cmp x val in iszero context → iszero(iszero(xor(x, val))) *)
Definition ao_cmp_prefer_iz_general_def:
  ao_cmp_prefer_iz_general mid id op1 op2 inst =
    let inner = ao_fresh_var id "xor" in
    let tmp = ao_fresh_var id "iz" in
    [<| inst_id := ao_fresh_id mid id 0; inst_opcode := XOR;
        inst_operands := [op1; op2]; inst_outputs := [inner] |>;
     <| inst_id := ao_fresh_id mid id 1; inst_opcode := ISZERO;
        inst_operands := [Var inner]; inst_outputs := [tmp] |>;
     inst with <| inst_opcode := ISZERO;
                  inst_operands := [Var tmp] |>]
End

(*
 * Main comparator optimization.
 * Python: _optimize_comparator_instruction.
 *
 * Updated to match new Python:
 *   - almost_never with never=0 → iszero(x)
 *   - almost_never with never=-1 → iszero(not(x))
 *   - prefer_iszero + almost_always uses xor/not pattern (not eq)
 *)
Definition ao_opt_comparator_def:
  ao_opt_comparator mid dfg ra lbl idx inst =
    let opc = inst.inst_opcode in
    case inst.inst_operands of
      [op1; op2] =>
        (* x cmp x → 0 *)
        if op1 = op2 then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
        else
          let is_gt = (opc = GT \/ opc = SGT) in
          let signed = (opc = SGT \/ opc = SLT) in
          (* Range-based optimization *)
          let range_result = ao_opt_cmp_range ra lbl idx inst is_gt signed in
          (case range_result of
            SOME replacement =>
              [inst with <| inst_opcode := ASSIGN;
                            inst_operands := [replacement] |>]
          | NONE =>
          let (almost_always, never, almost_never) =
            if signed then ao_signed_boundaries is_gt
            else ao_unsigned_boundaries is_gt in
          let prefer_iszero = ao_all_prefer_iszero dfg inst in
          (* Boundary checks: Python checks operands[0] = HOL4 op2 for lit *)
          if ~is_lit_op op2 then [inst]
          (* never: cmp x never → 0. *)
          else if lit_eq op2 never then
            [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
          (* almost_never: cmp x almost_never → eq(x, never).
             Special cases for never=0 and never=-1. *)
          else if lit_eq op2 almost_never then
            if never = 0w then
              (* eq x 0 → iszero(x) *)
              [inst with <| inst_opcode := ISZERO;
                            inst_operands := [op1] |>]
            else if never = 0w - 1w then
              (* eq x (-1) → iszero(not(x)) *)
              let id = inst.inst_id in
              let tmp = ao_fresh_var id "not" in
              [<| inst_id := ao_fresh_id mid id 0; inst_opcode := NOT;
                  inst_operands := [op1]; inst_outputs := [tmp] |>;
               inst with <| inst_opcode := ISZERO;
                            inst_operands := [Var tmp] |>]
            else
              [inst with <| inst_opcode := EQ;
                            inst_operands := [op1; Lit never] |>]
          (* prefer_iszero + almost_always:
             Python produces iszero(iszero(inner)) where:
             - val=0: inner=x
             - val=-1: inner=not(x)
             - else: inner=xor(val, x) *)
          else if prefer_iszero /\ lit_eq op2 almost_always then
            let id = inst.inst_id in
            let val_w = case op2 of Lit w => w | _ => 0w in
            if val_w = 0w then
              ao_cmp_prefer_iz_zero mid id op1 inst
            else if val_w = 0w - 1w then
              ao_cmp_prefer_iz_max mid id op1 inst
            else
              ao_cmp_prefer_iz_general mid id op1 op2 inst
          (* gt x 0 → iszero(iszero(x)). Only for unsigned GT with literal 0. *)
          else if opc = GT /\ lit_eq op2 0w then
            let id = inst.inst_id in
            let tmp = ao_fresh_var id "iz" in
            [<| inst_id := ao_fresh_id mid id 0; inst_opcode := ISZERO;
                inst_operands := [op1]; inst_outputs := [tmp] |>;
             inst with <| inst_opcode := ISZERO;
                          inst_operands := [Var tmp] |>]
          (* Remaining comparators: iszero insertion/removal handled by
             ao_cmp_flip_function (separate mini-pass after peephole). *)
          else [inst])
    | _ => [inst]
End

(* ===== Main Dispatch ===== *)

(*
 * Python: _rewrite_local dispatches to per-opcode rules.
 * Pre-flip is applied before dispatch, post-flip after.
 *)
Definition ao_peephole_inst_def:
  ao_peephole_inst mid (dfg : dfg_analysis) ra lbl idx inst =
    let opc = inst.inst_opcode in
    if inst.inst_outputs = [] then [inst]
    else if opc = ASSIGN \/ opc = PHI \/ opc = PARAM then [inst]
    else if opc = SHL \/ opc = SHR \/ opc = SAR then ao_opt_shift inst
    else if opc = SIGNEXTEND then ao_opt_signextend ra lbl idx inst
    else if opc = Exp then ao_opt_exp inst
    else if opc = ADD \/ opc = SUB \/ opc = XOR then ao_opt_addsub inst
    else if opc = AND then ao_opt_and inst
    else if opc = MUL \/ opc = Div \/ opc = SDIV \/
            opc = Mod \/ opc = SMOD then ao_opt_muldiv inst
    else if opc = OR then ao_opt_or dfg inst
    else if opc = EQ then ao_opt_eq mid dfg inst
    else if opc = GT \/ opc = LT \/ opc = SGT \/ opc = SLT then
      ao_opt_comparator mid dfg ra lbl idx inst
    else [inst]
End

(* ===== Operand Flipping ===== *)

(* Pre-peephole flip: for commutative ops, put literal at op2 (= Python operands[0]).
   This matches Python's normalization which puts literal at Python operands[0].
   Since HOL4 op2 = Python operands[0] (reversed order), we flip literal TO op2. *)
Definition ao_pre_flip_inst_def:
  ao_pre_flip_inst inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_lit_op op1 /\ ~is_lit_op op2 then
          if inst.inst_opcode = ADD \/ inst.inst_opcode = MUL \/
             inst.inst_opcode = AND \/ inst.inst_opcode = OR \/
             inst.inst_opcode = XOR \/ inst.inst_opcode = EQ then
            inst with inst_operands := [op2; op1]
          else if is_comparator inst.inst_opcode then
            (* comparator: swap operands AND flip opcode (gt<->lt, sgt<->slt) *)
            inst with <| inst_operands := [op2; op1];
                         inst_opcode := flip_comparison_opcode inst.inst_opcode |>
          else inst
        else inst
    | _ => inst
End

(* Post-peephole flip: for commutative ops, put literal at op1 (= Python operands[1]).
   This matches Python's _flip_inst which puts literal at Python operands[1]. *)
Definition ao_post_flip_inst_def:
  ao_post_flip_inst inst =
    case inst.inst_operands of
      [op1; op2] =>
        if ~is_lit_op op1 /\ is_lit_op op2 /\
           (inst.inst_opcode = ADD \/ inst.inst_opcode = MUL \/
            inst.inst_opcode = AND \/ inst.inst_opcode = OR \/
            inst.inst_opcode = XOR \/ inst.inst_opcode = EQ) then
          inst with inst_operands := [op2; op1]
        else inst
    | _ => inst
End

(* Post-flip only the rewritten original instruction, which a rule always emits
   LAST (any inserted helpers precede it, matching Python's add_before).  Python
   applies _flip_inst to the rewritten inst only, never to inserted helpers. *)
Definition ao_post_flip_last_def:
  ao_post_flip_last [] = [] /\
  ao_post_flip_last [inst] = [ao_post_flip_inst inst] /\
  ao_post_flip_last (inst :: rest) = inst :: ao_post_flip_last rest
End

(* ===== Comparator Iszero Flip Mini-Pass ===== *)

(*
 * For comparators with single use: if use is iszero (with non-assert
 * downstream), remove the iszero and flip strict→non-strict (e.g. GT→LT
 * with val+1). If use is assert, insert iszero before assert and flip.
 *
 * This is a separate pass because it modifies two instructions
 * (the comparator and its consumer).
 *)

(*
 * Scan instructions for comparator flip opportunities.
 * Returns three lists:
 *   flips   : (cmp_id, new_opcode, new_literal, original_op1)
 *   removes : iszero inst_ids to convert to ASSIGN
 *   inserts : (assert_id, cmp_out_var, fresh_var, cmp_id) for iszero insertion
 *)
Definition ao_cmp_flip_scan_def:
  ao_cmp_flip_scan dfg [] = ([], [], []) /\
  ao_cmp_flip_scan dfg (inst :: rest) =
    let (flips, removes, inserts) = ao_cmp_flip_scan dfg rest in
    if ~is_comparator inst.inst_opcode then (flips, removes, inserts)
    else case (inst.inst_operands, inst.inst_outputs) of
      ([op1; Lit w], [out_var]) =>
        let uses = dfg_get_uses dfg out_var in
        if LENGTH uses <> 1 then (flips, removes, inserts)
        else
          let after = HD uses in
          if after.inst_opcode <> ISZERO /\ after.inst_opcode <> ASSERT then
            (flips, removes, inserts)
          else
            let is_gt = (inst.inst_opcode = GT \/ inst.inst_opcode = SGT) in
            let signed = (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) in
            let (_, never, _) =
              if signed then ao_signed_boundaries is_gt
              else ao_unsigned_boundaries is_gt in
            (* Guard: skip if literal = never boundary *)
            if w = never then (flips, removes, inserts)
            else
              let new_w = if is_gt then w + 1w else w - 1w in
              let new_opc = flip_comparison_opcode inst.inst_opcode in
              if after.inst_opcode = ISZERO then
                (case after.inst_outputs of
                   [iz_out] =>
                     let n_uses = dfg_get_uses dfg iz_out in
                     if LENGTH n_uses <> 1 then (flips, removes, inserts)
                     (* iszero→assert is already optimal: skip *)
                     else if (HD n_uses).inst_opcode = ASSERT then
                       (flips, removes, inserts)
                     else
                       ((inst.inst_id, new_opc, new_w, op1) :: flips,
                        after.inst_id :: removes,
                        inserts)
                 | _ => (flips, removes, inserts))
              else (* after.opcode = ASSERT: insert iszero before assert *)
                let fresh = ao_fresh_var inst.inst_id "iz" in
                ((inst.inst_id, new_opc, new_w, op1) :: flips,
                 removes,
                 (after.inst_id, out_var, fresh, inst.inst_id) :: inserts)
    | _ => (flips, removes, inserts)
End

(* Apply cmp_flip changes to a single instruction. *)
Definition ao_cmp_flip_apply_inst_def:
  ao_cmp_flip_apply_inst mid flips removes inserts inst =
    case ALOOKUP flips inst.inst_id of
      SOME (new_opc, new_w, orig_op1) =>
        (* Python emits (new_opc orig_op1 (Lit new_w)) and then _flip_inst swaps
           it to lit-at-op1, flipping the opcode back to the original. *)
        [inst with <| inst_opcode := flip_comparison_opcode new_opc;
                      inst_operands := [Lit new_w; orig_op1] |>]
    | NONE =>
        if MEM inst.inst_id removes then
          [inst with <| inst_opcode := ASSIGN |>]
        else
          case ALOOKUP inserts inst.inst_id of
            SOME (cmp_out, fresh, cmp_id) =>
              [<| inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
                  inst_operands := [Var cmp_out];
                  inst_outputs := [fresh] |>;
               inst with <| inst_operands := [Var fresh] |>]
          | NONE => [inst]
End

(* Apply cmp_flip to a function: scan all instructions, then FLAT MAP per block. *)
Definition ao_cmp_flip_function_def:
  ao_cmp_flip_function mid dfg fn =
    let all_insts = fn_insts fn in
    let (flips, removes, inserts) = ao_cmp_flip_scan dfg all_insts in
    if NULL flips then fn
    else
      fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                    bb.bb_instructions))
          fn.fn_blocks
End

(* ===== OR-truthy mini-pass =====
 *
 * Python _rule_or: `x | n -> 1` in truthy positions when n is a nonzero
 * literal and every use of the output is a TRUTHY_INSTRUCTION.  This is a
 * value-changing rewrite (output becomes 1 rather than x|n), so unlike the
 * value-preserving peephole it cannot live in the per-instruction sim
 * engine (which preserves all non-fresh var values).  It is a separate
 * mini-pass, justified at the usage level: x|n with n<>0 is always nonzero
 * and 1 is nonzero, so the two agree in every truthy-consuming use.
 *
 * After phase 3, surviving `or (Lit n) op1` instructions have n<>0 and
 * n<>(-1) (those were turned into ASSIGN by ao_opt_or), so the scan's n<>0
 * guard selects exactly the Python truthy case.  The literal sits at op1
 * because ao_post_flip_inst normalises commutative ops to lit-at-op1.
 *)

(* Scan for OR instructions eligible for the truthy rewrite: opcode OR,
   operands [Lit n; op1] with n<>0, and all uses truthy. *)
Definition ao_or_truthy_scan_def:
  ao_or_truthy_scan dfg [] = [] /\
  ao_or_truthy_scan dfg (inst :: rest) =
    let ids = ao_or_truthy_scan dfg rest in
    if inst.inst_opcode = OR /\
       (case inst.inst_operands of
          [Lit n; op1] => n <> 0w
        | _ => F) /\
       ao_all_truthy dfg inst then
      inst.inst_id :: ids
    else ids
End

(* Apply the OR-truthy rewrite to a single instruction.
   The opcode = OR guard is redundant for scanned ids (which are all ORs) but
   makes the transform provably leave terminators and PHIs untouched, which the
   generic WF/SSA-preservation lemmas require. *)
Definition ao_or_truthy_apply_inst_def:
  ao_or_truthy_apply_inst ids inst =
    if inst.inst_opcode = OR /\ MEM inst.inst_id ids then
      inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>
    else inst
End

(* Apply OR-truthy to a function: scan all instructions, then MAP per block. *)
Definition ao_or_truthy_function_def:
  ao_or_truthy_function dfg fn =
    let ids = ao_or_truthy_scan dfg (fn_insts fn) in
    if NULL ids then fn
    else
      fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP (ao_or_truthy_apply_inst ids) bb.bb_instructions)
          fn.fn_blocks
End

(* ===== Block and Function Transform ===== *)

(*
 * Per-instruction transform pipeline (matches Python _rewrite_all):
 * 1. Resolve iszero operands (from forward-computed targets)
 * 2. Try producer rules (balance→selfbalance, signextend nesting)
 * 3. Pre-flip + peephole + post-flip
 *
 * PHI is mapped to [inst] here so the per-instruction simulation engine
 * (inst_transform_structural / inst_transform_phi) can keep treating PHIs as
 * a fixed parallel prefix that is left literally unchanged.  PHI iszero-use
 * resolution (matching Python's _rewrite_iszero_uses on PHIs) is applied
 * separately as a post-pass by ao_resolve_phis_block (see ao_transform_block).
 *)
Definition ao_transform_inst_def:
  ao_transform_inst mid dfg ra lbl idx targets inst =
    if inst.inst_opcode = PHI then [inst]
    else
    let inst0 = ao_resolve_iszero_inst targets inst in
    if inst0.inst_outputs = [] then [inst0]
    else if inst0.inst_opcode = ASSIGN \/ inst0.inst_opcode = PHI \/
            inst0.inst_opcode = PARAM then [inst0]
    else
      case ao_opt_producer dfg inst0 of
        SOME result => ao_post_flip_last result
      | NONE =>
          let inst1 = ao_pre_flip_inst inst0 in
          let result = ao_peephole_inst mid dfg ra lbl idx inst1 in
          ao_post_flip_last result
End

(* Resolve iszero chains inside PHI operands only (Python:
   _rewrite_iszero_uses applied to PHIs).  Non-PHI instructions are left
   untouched.  Resolution only rewrites operands, so opcode/outputs/inst_id
   and the PHI prefix structure are preserved. *)
Definition ao_resolve_phis_block_def:
  ao_resolve_phis_block targets bb =
    bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode = PHI
                  then ao_resolve_iszero_inst targets inst
                  else inst) bb.bb_instructions
End

(* ao_transform_inst keeps PHI -> [inst] (the structural sim engine requires
   PHIs to be left literally unchanged), so PHI iszero-use resolution is run
   as a post-pass over the transformed block.  ao_transform_inst maps PHIs to
   themselves and never produces a PHI from a non-PHI input, hence this
   resolves exactly the original PHI prefix and leaves the transformed body
   untouched. *)
Definition ao_transform_block_def:
  ao_transform_block mid dfg ra targets bb =
    ao_resolve_phis_block targets
      (bb with bb_instructions :=
        FLAT (MAPi (\idx inst.
          ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
          bb.bb_instructions))
End

(*
 * Full pass structure (matches Python run_pass):
 *   1. Handle offset conversion (add(lit,label) → offset)
 *   2. Compute iszero targets
 *   3. Single rewrite pass: iszero resolution + producer + peephole
 *   4. Comparator iszero flip (separate mini-pass)
 *   5. OR-truthy rewrite x|n → 1 (separate mini-pass)
 *)
Definition ao_transform_function_def:
  ao_transform_function fn =
    (* Phase 1: offset conversion *)
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    (* Phase 2: compute iszero targets *)
    let targets = ao_compute_fn_iszero_targets fn0 in
    (* Phase 3: main rewrite pass *)
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    (* Phase 4: comparator iszero flip *)
    let dfg1 = dfg_build_function fn1 in
    let mid1 = fn_max_inst_id fn1 in
    let fn2 = ao_cmp_flip_function mid1 dfg1 fn1 in
    (* Phase 5: OR-truthy rewrite (x|n -> assign 1) *)
    let dfg2 = dfg_build_function fn2 in
    ao_or_truthy_function dfg2 fn2
End

(* Proof-only (not used by the pass): characterises which variables the
   cmp-flip phase may change — the simulation theorem's "modulo" set.
   - Comparator outputs that get flipped (out_var differs)
   - Fresh variables introduced by insert (ISZERO before ASSERT) *)
Definition ao_cmp_flip_dead_vars_def:
  ao_cmp_flip_dead_vars dfg fn =
    let (flips, removes, inserts) = ao_cmp_flip_scan dfg (fn_insts fn) in
    { v | ?inst. MEM inst (fn_insts fn) /\
          MEM inst.inst_id (MAP FST flips) /\
          MEM v inst.inst_outputs } UNION
    { fresh | ?aid out_var cmp_id.
          MEM (aid, out_var, fresh, cmp_id) inserts }
End

(* Proof-only (not used by the pass): the variables OR-truthy may change —
   outputs of the OR instructions rewritten to `assign 1` (originally x|n). *)
Definition ao_or_truthy_dead_vars_def:
  ao_or_truthy_dead_vars dfg fn =
    let ids = ao_or_truthy_scan dfg (fn_insts fn) in
    { v | ?inst. MEM inst (fn_insts fn) /\
          MEM inst.inst_id ids /\
          MEM v inst.inst_outputs }
End

Definition ao_transform_context_def:
  ao_transform_context ctx =
    ctx with ctx_functions := MAP ao_transform_function ctx.ctx_functions
End

(* ===== Proof-only definitions =====
 * None of the definitions below are referenced by ao_transform_function or
 * ao_transform_context (the pass itself); they exist solely to STATE and
 * PROVE the correctness theorems — fresh-/dead-variable sets, the
 * fresh-names precondition, and a runtime DFG invariant — and therefore have
 * no effect on the instructions the pass emits. *)

Definition ao_fn_fresh_vars_def:
  ao_fn_fresh_vars fn =
    { v | ?id.
        MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
        (v = ao_fresh_var id "not" \/
         v = ao_fresh_var id "iz" \/
         v = ao_fresh_var id "xor") }
End

(* Fresh-var disjointness: no name synthesized by the pass collides with a
   source operand or output.  Not derivable from wf_function (which imposes no
   naming constraint); carried as an explicit precondition, matching the
   convention of every other insertion pass (m2v_fresh_names_disjoint,
   branch_opt's bo_fresh_vars_fn).  Satisfiable because real Venom variable
   names never use the synthetic "ao_<id>_<suffix>" scheme.
   Stronger than output-only disjointness (the operand clause is needed by
   the phase-3 simulation proof); implies the output-only fact used by the
   WF/SSA preservation proofs. *)
Definition ao_fresh_names_disjoint_def:
  ao_fresh_names_disjoint fn <=>
    !v. v IN ao_fn_fresh_vars fn ==>
      !inst. MEM inst (fn_insts fn) ==>
        ~MEM v inst.inst_outputs /\ ~MEM (Var v) inst.inst_operands
End

Definition ao_cmp_fresh_vars_def:
  ao_cmp_fresh_vars fn =
    { v | ?id.
        (?i. MEM i (fn_insts fn) /\
             is_comparator i.inst_opcode /\
             i.inst_id = id) /\
        v = ao_fresh_var id "iz" }
End

Definition ao_fn_total_fresh_vars_def:
  ao_fn_total_fresh_vars fn =
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    let dfg1 = dfg_build_function fn1 in
    let mid1 = fn_max_inst_id fn1 in
    let fn2 = ao_cmp_flip_function mid1 dfg1 fn1 in
    let dfg2 = dfg_build_function fn2 in
    ao_fn_fresh_vars fn UNION ao_cmp_flip_dead_vars dfg1 fn1 UNION
    ao_or_truthy_dead_vars dfg2 fn2
End

(* DFG runtime invariant: tracked opcode outputs have expected values *)
Definition ao_dfg_inv_def:
  ao_dfg_inv dfg s <=>
    !x inst val. dfg_get_def dfg x = SOME inst /\
      lookup_var x s = SOME val ==>
      (inst.inst_opcode = ADDRESS ==>
        val = w2w s.vs_call_ctx.cc_address) /\
      (inst.inst_opcode = SIGNEXTEND ==>
        !w inner_op. inst.inst_operands = [Lit w; inner_op] ==>
        ?inner_val. val = sign_extend w inner_val)
End
