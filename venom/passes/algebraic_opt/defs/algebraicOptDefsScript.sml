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
               if keep < depth /\ keep < LENGTH chain then
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
 *   signextend(n, signextend(m, x)) where n >= m → assign(x)
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
                           if w >= inner_w then
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

(* Or: x | MAX → MAX, x | 0 → x, x | nonzero_lit → 1 (truthy context)
   Commutative: after pre-flip, literal at op2. *)
Definition ao_opt_or_def:
  ao_opt_or dfg inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_eq op2 (0w - 1w) then
          [inst with <| inst_opcode := ASSIGN;
                        inst_operands := [Lit (0w - 1w)] |>]
        (* x | nonzero_lit → 1 when all uses are truthy *)
        else if ao_all_truthy dfg inst /\
                is_lit_op op2 /\ ~lit_eq op2 0w then
          [inst with <| inst_opcode := ASSIGN;
                        inst_operands := [Lit 1w] |>]
        else if lit_eq op2 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [op1] |>]
        else [inst]
    | _ => [inst]
End

(* Eq: x==x→1, x==0→iszero(x), x==(-1)→iszero(~x),
       prefer_iszero: eq(x,y) → iszero(xor(x,y))
   Commutative: after pre-flip, literal at op2. *)
Definition ao_opt_eq_def:
  ao_opt_eq dfg inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>]
        else if lit_eq op2 0w then
          [inst with <| inst_opcode := ISZERO; inst_operands := [op1] |>]
        else if lit_eq op2 (0w - 1w) then
          let id = inst.inst_id in
          let tmp = ao_fresh_var id "not" in
          [<| inst_id := id; inst_opcode := NOT;
              inst_operands := [op1]; inst_outputs := [tmp] |>;
           inst with <| inst_opcode := ISZERO;
                        inst_operands := [Var tmp] |>]
        (* prefer_iszero: eq(x,y) → iszero(xor(x,y)) when uses are assert/iszero *)
        else if ao_all_prefer_iszero dfg inst then
          let id = inst.inst_id in
          let tmp = ao_fresh_var id "xor" in
          [<| inst_id := id; inst_opcode := XOR;
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
  ao_cmp_prefer_iz_zero id op1 inst =
    let tmp = ao_fresh_var id "iz" in
    [<| inst_id := id; inst_opcode := ISZERO;
        inst_operands := [op1]; inst_outputs := [tmp] |>;
     inst with <| inst_opcode := ISZERO;
                  inst_operands := [Var tmp] |>]
End

(* Helper: prefer_iszero + almost_always with val=-1
   slt x MAX in iszero context → iszero(iszero(not(x))) *)
Definition ao_cmp_prefer_iz_max_def:
  ao_cmp_prefer_iz_max id op1 inst =
    let inner = ao_fresh_var id "not" in
    let tmp = ao_fresh_var id "iz" in
    [<| inst_id := id; inst_opcode := NOT;
        inst_operands := [op1]; inst_outputs := [inner] |>;
     <| inst_id := id; inst_opcode := ISZERO;
        inst_operands := [Var inner]; inst_outputs := [tmp] |>;
     inst with <| inst_opcode := ISZERO;
                  inst_operands := [Var tmp] |>]
End

(* Helper: prefer_iszero + almost_always with general val
   cmp x val in iszero context → iszero(iszero(xor(x, val))) *)
Definition ao_cmp_prefer_iz_general_def:
  ao_cmp_prefer_iz_general id op1 op2 inst =
    let inner = ao_fresh_var id "xor" in
    let tmp = ao_fresh_var id "iz" in
    [<| inst_id := id; inst_opcode := XOR;
        inst_operands := [op1; op2]; inst_outputs := [inner] |>;
     <| inst_id := id; inst_opcode := ISZERO;
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
  ao_opt_comparator dfg ra lbl idx inst =
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
          case range_result of
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
              [<| inst_id := id; inst_opcode := NOT;
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
              ao_cmp_prefer_iz_zero id op1 inst
            else if val_w = 0w - 1w then
              ao_cmp_prefer_iz_max id op1 inst
            else
              ao_cmp_prefer_iz_general id op1 op2 inst
          (* gt x 0 → iszero(iszero(x)). Only for unsigned GT with literal 0. *)
          else if opc = GT /\ lit_eq op2 0w then
            let id = inst.inst_id in
            let tmp = ao_fresh_var id "iz" in
            [<| inst_id := id; inst_opcode := ISZERO;
                inst_operands := [op1]; inst_outputs := [tmp] |>;
             inst with <| inst_opcode := ISZERO;
                          inst_operands := [Var tmp] |>]
          (* Remaining comparators: iszero insertion/removal handled by
             ao_cmp_flip_function (separate mini-pass after peephole). *)
          else [inst]
    | _ => [inst]
End

(* ===== Main Dispatch ===== *)

(*
 * Python: _rewrite_local dispatches to per-opcode rules.
 * Pre-flip is applied before dispatch, post-flip after.
 *)
Definition ao_peephole_inst_def:
  ao_peephole_inst (dfg : dfg_analysis) ra lbl idx inst =
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
    else if opc = EQ then ao_opt_eq dfg inst
    else if opc = GT \/ opc = LT \/ opc = SGT \/ opc = SLT then
      ao_opt_comparator dfg ra lbl idx inst
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
        if is_lit_op op1 /\ ~is_lit_op op2 /\
           (inst.inst_opcode = ADD \/ inst.inst_opcode = MUL \/
            inst.inst_opcode = AND \/ inst.inst_opcode = OR \/
            inst.inst_opcode = XOR \/ inst.inst_opcode = EQ) then
          inst with inst_operands := [op2; op1]
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
  ao_cmp_flip_apply_inst flips removes inserts inst =
    case ALOOKUP flips inst.inst_id of
      SOME (new_opc, new_w, orig_op1) =>
        [inst with <| inst_opcode := new_opc;
                      inst_operands := [orig_op1; Lit new_w] |>]
    | NONE =>
        if MEM inst.inst_id removes then
          [inst with <| inst_opcode := ASSIGN |>]
        else
          case ALOOKUP inserts inst.inst_id of
            SOME (cmp_out, fresh, cmp_id) =>
              [<| inst_id := cmp_id; inst_opcode := ISZERO;
                  inst_operands := [Var cmp_out];
                  inst_outputs := [fresh] |>;
               inst with <| inst_operands := [Var fresh] |>]
          | NONE => [inst]
End

(* Apply cmp_flip to a function: scan all instructions, then FLAT MAP per block. *)
Definition ao_cmp_flip_function_def:
  ao_cmp_flip_function dfg fn =
    let all_insts = fn_insts fn in
    let (flips, removes, inserts) = ao_cmp_flip_scan dfg all_insts in
    if NULL flips then fn
    else
      fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          FLAT (MAP (ao_cmp_flip_apply_inst flips removes inserts)
                    bb.bb_instructions))
          fn.fn_blocks
End

(* ===== Block and Function Transform ===== *)

(*
 * Per-instruction transform pipeline (matches Python _rewrite_all):
 * 1. Resolve iszero operands (from forward-computed targets)
 * 2. Try producer rules (balance→selfbalance, signextend nesting)
 * 3. Pre-flip + peephole + post-flip
 *)
Definition ao_transform_inst_def:
  ao_transform_inst dfg ra lbl idx targets inst =
    let inst0 = ao_resolve_iszero_inst targets inst in
    if inst0.inst_outputs = [] then [inst0]
    else if inst0.inst_opcode = ASSIGN \/ inst0.inst_opcode = PHI \/
            inst0.inst_opcode = PARAM then [inst0]
    else
      case ao_opt_producer dfg inst0 of
        SOME result => MAP ao_post_flip_inst result
      | NONE =>
          let inst1 = ao_pre_flip_inst inst0 in
          let result = ao_peephole_inst dfg ra lbl idx inst1 in
          MAP ao_post_flip_inst result
End

Definition ao_transform_block_def:
  ao_transform_block dfg ra targets bb =
    bb with bb_instructions :=
      FLAT (MAPi (\idx inst.
        ao_transform_inst dfg ra bb.bb_label idx targets inst)
        bb.bb_instructions)
End

(*
 * Full pass structure (matches Python run_pass):
 *   1. Handle offset conversion (add(lit,label) → offset)
 *   2. Compute iszero targets
 *   3. Single rewrite pass: iszero resolution + producer + peephole
 *   4. Comparator iszero flip (separate mini-pass)
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
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block dfg ra targets) fn0.fn_blocks in
    (* Phase 4: comparator iszero flip *)
    let dfg1 = dfg_build_function fn1 in
    ao_cmp_flip_function dfg1 fn1
End

Definition ao_transform_context_def:
  ao_transform_context ctx =
    ctx with ctx_functions := MAP ao_transform_function ctx.ctx_functions
End
