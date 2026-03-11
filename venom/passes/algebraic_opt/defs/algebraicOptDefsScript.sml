(*
 * Algebraic Optimization Pass — Definitions
 *
 * Ports vyper/venom/passes/algebraic_optimization.py to HOL4.
 *
 * Reduces algebraically evaluatable expressions via peephole rules.
 * Split into per-opcode-group helpers to keep definitions small.
 *
 * IMPORTANT: Python IR reverses operands from EVM stack order.
 * HOL4 uses semantic (EVM) order. So Python operands[0] = HOL4 op2,
 * and Python operands[1] = HOL4 op1. The peephole rules below are
 * written for HOL4 semantic order: [op1; op2] where
 *   SUB → op1 - op2, DIV → op1 / op2, GT → op1 > op2, etc.
 *
 * TOP-LEVEL:
 *   ao_peephole_inst          — main peephole dispatch
 *   ao_handle_offset_inst     — add(lit,label) → offset
 *   ao_transform_function     — function-level transform
 *
 * Source: vyper/venom/passes/algebraic_optimization.py
 *)

Theory algebraicOptDefs
Ancestors
  passSimulationDefs dfgDefs dfgAnalysisProps rangeAnalysisDefs
  venomExecSemantics venomInst
Libs
  pred_setTheory integerTheory

(* ===== Utilities ===== *)

Definition is_lit_op_def:
  is_lit_op (Lit _) = T /\
  is_lit_op _ = F
End

Definition lit_eq_def:
  lit_eq op v <=>
    case op of Lit w => (w = v) | _ => F
End

Definition ao_fresh_var_def:
  ao_fresh_var (id:num) (suffix:string) =
    STRCAT "ao_" (STRCAT (toString id) (STRCAT "_" suffix))
End

(* Power-of-two check: w ≠ 0 ∧ w AND (w - 1) = 0 *)
Definition is_power_of_two_def:
  is_power_of_two (w : bytes32) <=>
    w <> 0w /\ word_and w (w - 1w) = 0w
End

(* Integer log2: find n such that 2^n = w. Returns 0 for non-powers. *)
Definition word_log2_def:
  word_log2 (w : bytes32) : bytes32 =
    n2w (LOG2 (w2n w))
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

(* Flip comparison opcode: GT↔LT, SGT↔SLT.
   Matches Python flip_comparison_opcode. *)
Definition flip_comparison_opcode_def:
  flip_comparison_opcode GT = (LT : opcode) /\
  flip_comparison_opcode LT = GT /\
  flip_comparison_opcode SGT = SLT /\
  flip_comparison_opcode SLT = SGT /\
  flip_comparison_opcode opc = opc (* shouldn't happen *)
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

(* ===== Iszero Chain ===== *)

(* Walk iszero chain via DFG with visited-set termination (no fuel).
   Terminates because each step adds an inst_id to visited,
   and dfg_def_ids is finite. *)
Definition ao_get_iszero_chain_def:
  ao_get_iszero_chain dfg visited op =
    case op of
      Var v =>
        (case dfg_get_def dfg v of
           SOME inst =>
             if inst.inst_id IN visited then []
             else if inst.inst_opcode = ISZERO then
               (case inst.inst_operands of
                  [src] => inst :: ao_get_iszero_chain dfg
                                    (inst.inst_id INSERT visited) src
                | _ => [])
             else []
         | NONE => [])
    | _ => []
Termination
  WF_REL_TAC `inv_image $< (\(dfg,visited,_). CARD (dfg_def_ids dfg DIFF visited))`
  >> rpt strip_tac
  >> imp_res_tac dfg_get_def_implies_dfg_def_ids
  >> irule CARD_PSUBSET
  >> simp[FINITE_DIFF, dfg_def_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION]
  >> qexists_tac `inst.inst_id` >> simp[]
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
 *   GEP [base; offset]
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

(* Helper: nested signextend check *)
Definition ao_opt_signextend_nested_def:
  ao_opt_signextend_nested dfg w x inst =
    case x of
      Var v =>
        (case dfg_get_def dfg v of
           SOME producer =>
             if producer.inst_opcode = SIGNEXTEND then
               (case producer.inst_operands of
                  [Lit inner_w; _] =>
                    if w >= inner_w then
                      [inst with <| inst_opcode := ASSIGN;
                                    inst_operands := [x] |>]
                    else [inst]
                | _ => [inst])
             else [inst]
         | NONE => [inst])
    | _ => [inst]
End

(* Signextend: signextend(n >= 31, x) → x
   Range-based: if x is already in valid signed range for (n+1) bytes → x
   Nested: signextend(n, signextend(m, x)) where n >= m → x
   HOL4 order: [n; x] *)
Definition ao_opt_signextend_def:
  ao_opt_signextend dfg ra lbl idx inst =
    case inst.inst_operands of
      [n_op; x] =>
        (case n_op of
           Lit w =>
             if w >= 31w then
               [inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>]
             else
               (* Range-based elimination: if x is in signed range for (n+1) bytes,
                  signextend is a no-op.
                  Python: n = n_op.value; bits = 8*(n+1);
                  signed_min = -(1 << (bits-1)); signed_max = (1 << (bits-1)) - 1 *)
               let n = w2n w in
               if n < 31 then
                 let x_range = range_get_range ra lbl idx x in
                 if ~vr_is_top x_range then
                   let bits = 8 * (n + 1) in
                   let signed_min = ~(&(2 ** (bits - 1))) in
                   let signed_max = &(2 ** (bits - 1)) - 1 in
                   if vr_lo x_range >= signed_min /\ vr_hi x_range <= signed_max then
                     [inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>]
                   else
                     ao_opt_signextend_nested dfg w x inst
                 else
                   ao_opt_signextend_nested dfg w x inst
               else
                 ao_opt_signextend_nested dfg w x inst
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

(* GEP: gep(base, 0) → base *)
Definition ao_opt_gep_def:
  ao_opt_gep (inst : instruction) =
    case inst.inst_operands of
      [bop; goff] =>
        if lit_eq goff 0w then
          [inst with <| inst_opcode := ASSIGN; inst_operands := [bop] |>]
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
        (* Power-of-two reductions: op2 is the literal (divisor/multiplier)
           Python operands[0] = HOL4 op2 for MUL (commutative, pre-flipped)
           For DIV/MOD: op2 = divisor *)
        else (case op2 of
          Lit w =>
            if is_power_of_two w then
              let n = word_log2 w in
              (* x % (2^n) → x & (2^n - 1) *)
              if opc = Mod then
                [inst with <| inst_opcode := AND;
                              inst_operands := [op1; Lit (w - 1w)] |>]
              (* x / (2^n) → x >> n. HOL4 SHR: [shift; value] *)
              else if opc = Div then
                [inst with <| inst_opcode := SHR;
                              inst_operands := [Lit n; op1] |>]
              (* x * (2^n) → x << n. HOL4 SHL: [shift; value] *)
              else if opc = MUL then
                [inst with <| inst_opcode := SHL;
                              inst_operands := [Lit n; op1] |>]
              else [inst]
            else [inst]
        | _ => [inst])
    | _ => [inst]
End

(* Or: x | MAX → MAX, x | 0 → x, x | nonzero_lit → 1 (truthy context)
   Commutative: after pre-flip, literal at op2.
   Python: uses DFG to check if all uses are truthy. *)
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
 * Python: operands[-1] = a (text first) = HOL4 op1,
 *         operands[-2] = b (text second) = HOL4 op2.
 *
 * Python boundary values:
 *   int_bounds(256, signed=False) = (0, 2^256 - 1)
 *   int_bounds(256, signed=True)  = (-2^255, 2^255 - 1)
 *   NOTE: Python returns hi=2^256 for unsigned, which wraps to 0 via wrap256.
 *   This is a Python compiler bug — we replicate it for byte-for-byte equivalence.
 *
 * For GT (is_gt=T, signed=F): lo=0, hi=2^256-1
 *   almost_always=lo=0, never=hi=2^256-1 (wraps!), almost_never=hi-1
 *   NOTE: unsigned never=2^256-1 (MAX_UINT256), wrap256(MAX_UINT256+1)=0
 *         lit_eq(ops[0], never) checks operands[0]=HOL4 op2 against MAX.
 *         But unsigned GT almost_always=0, so lit_eq(ops[0], 0) fires BEFORE
 *         the gt-x-0 rule. This is the Python wrapping bug.
 *
 * For LT (is_gt=F, signed=F): lo=0, hi=2^256-1
 *   almost_always=hi=2^256-1 (wraps to MAX), never=lo=0
 *
 * For SGT (is_gt=T, signed=T): lo=-2^255, hi=2^255-1
 *   almost_always=lo=-2^255, never=hi=2^255-1
 *
 * For SLT (is_gt=F, signed=T): lo=-2^255, hi=2^255-1
 *   almost_always=hi=2^255-1, never=lo=-2^255
 *)

(* Helper: compute (almost_always, never, almost_never) boundary words.
   Returns (almost_always, never, almost_never).
   Python: lo, hi = int_bounds(256, signed)
           if is_gt: almost_always=lo, never=hi; almost_never=hi-1
           else:     almost_always=hi, never=lo; almost_never=lo+1

   For unsigned (signed=F):
     lo=0w, hi=0w-1w (MAX_UINT256).
     NOTE: Python int_bounds returns hi=2^256 for unsigned, wrap256 wraps to 0.
     We use 0w-1w=MAX_UINT256 as never for unsigned GT (matches Python wrap256
     behavior: wrap256(2^256) = 0, but lit_eq checks the wrapped value).
     Actually, Python's never for unsigned GT is 2^256, which wraps to 0.
     The lit_eq(operands[0], never) becomes lit_eq(operands[0], 0) — matches
     the "almost_always" case too. This causes the Python bug where gt x 0
     hits the "never" branch first. We replicate this.

   For signed (signed=T):
     lo = i2w(INT256_MIN), hi = i2w(INT256_MAX). *)

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
   Python guards: unsigned requires lo >= 0, signed requires hi <= MAX_INT256.
   If guard fails, lit is set to None and range optimization is skipped. *)
Definition ao_range_valid_for_cmp_def:
  ao_range_valid_for_cmp var_range (signed : bool) =
    if vr_is_top var_range then F
    else if signed then vr_hi var_range <= INT256_MAX
    else vr_lo var_range >= 0
End

(* Helper: wrap literal for comparison.
   Python: wrap256(lit, signed=signed). For signed: signed interpretation.
   For unsigned: unsigned interpretation (mod 2^256).
   We use w2i which gives signed interpretation of the word. *)
Definition ao_wrap_lit_def:
  ao_wrap_lit (w : bytes32) (signed : bool) : int =
    if signed then w2i w else &(w2n w)
End

(* Range-based comparator optimization.
   Python: check if literal vs variable comparison can be folded.
   HOL4 order: [op1; op2] = [a; b] where GT → a > b, LT → a < b.
   Python: a_op = operands[-1] = HOL4 op1, b_op = operands[-2] = HOL4 op2.

   For GT (a > b): always true if a.lo > b (var > lit), always false if a.hi <= b
   For LT (a < b): always true if a.hi < b (var < lit), always false if a.lo >= b
   When op1 is lit and op2 is var: lit vs var
   When op1 is var and op2 is lit: var vs lit *)
Definition ao_opt_cmp_range_def:
  ao_opt_cmp_range ra lbl idx inst is_gt signed =
    case inst.inst_operands of
      [op1; op2] =>
    if is_lit_op op1 /\ ~is_lit_op op2 then
      (* op1 is literal (=a), op2 is variable (=b): lit cmp var *)
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
      (* op1 is variable (=a), op2 is literal (=b): var cmp lit *)
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

(* Main comparator optimization.
   Python _optimize_comparator_instruction. *)
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
          (* never: cmp x never → 0. Python: lit_eq(operands[0], never) *)
          else if lit_eq op2 never then
            [inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>]
          (* almost_never: cmp x almost_never → eq(x, never).
             Python: operands[0] = HOL4 op2 = almost_never.
             Replaces with eq [operands[1], IRLiteral(never)] =
             eq [HOL4 op1, Lit never] in Python order.
             HOL4 EQ: [op1; op2]. Python eq operands[0]=never=HOL4 op2,
             operands[1]=original operands[1]=HOL4 op1.
             So HOL4: EQ [op1; Lit never]. *)
          else if lit_eq op2 almost_never then
            [inst with <| inst_opcode := EQ;
                          inst_operands := [op1; Lit never] |>]
          (* prefer_iszero + almost_always: cmp x 0 (for unsigned GT) etc.
             Python: add_before eq, then iszero.
             e.g. gt x 0 → tmp=eq(x,0); iszero(tmp) *)
          else if prefer_iszero /\ lit_eq op2 almost_always then
            let id = inst.inst_id in
            let tmp = ao_fresh_var id "eq" in
            [<| inst_id := id; inst_opcode := EQ;
                inst_operands := [op1; op2]; inst_outputs := [tmp] |>;
             inst with <| inst_opcode := ISZERO;
                          inst_operands := [Var tmp] |>]
          (* gt x 0 → iszero(iszero(x)). Only for unsigned GT with literal 0.
             Python: opcode == "gt" and lit_eq(operands[0], 0).
             operands[0] = HOL4 op2. So op2 = 0. *)
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

Definition ao_peephole_inst_def:
  ao_peephole_inst (dfg : dfg_analysis) ra lbl idx inst =
    let opc = inst.inst_opcode in
    if inst.inst_outputs = [] then [inst]
    else if opc = ASSIGN \/ opc = PHI \/ opc = PARAM then [inst]
    else if opc = SHL \/ opc = SHR \/ opc = SAR then ao_opt_shift inst
    else if opc = SIGNEXTEND then ao_opt_signextend dfg ra lbl idx inst
    else if opc = Exp then ao_opt_exp inst
    else if opc = GEP then ao_opt_gep inst
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
   This matches Python's _flip_operands which puts literal at Python operands[0].
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
   This matches Python's _flip_for_codesize which puts literal at Python operands[1]. *)
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

(* ===== Iszero Chain Optimization ===== *)

(*
 * Build chain map: for each iszero in the block, map its output var
 * to the iszero chain behind it.
 *
 * Chain is in HOL4 walk order: [nearest, ..., deepest].
 * Python reverses: [deepest, ..., nearest], then indexes chain[keep_count].
 * In HOL4: Python chain[k] = EL (chain_len - 1 - k) of HOL4 chain.
 *)
Definition ao_build_chain_map_def:
  ao_build_chain_map dfg [] = [] /\
  ao_build_chain_map dfg ((inst : instruction) :: rest) =
    if inst.inst_opcode = ISZERO then
      case (inst.inst_operands, inst.inst_outputs) of
        ([src_op], [out_var]) =>
          let chain = ao_get_iszero_chain dfg {} src_op in
          if chain = [] then ao_build_chain_map dfg rest
          else (out_var, chain) :: ao_build_chain_map dfg rest
      | _ => ao_build_chain_map dfg rest
    else ao_build_chain_map dfg rest
End

(*
 * Resolve a single operand for a specific use instruction.
 * Each use instruction gets its own replacement based on its opcode's
 * truthy/non-truthy status — this is the key difference from the old
 * batch replacement that conflated per-use replacements.
 *
 * Note: is_truthy_inst includes ISZERO here, but we explicitly skip
 * ISZERO uses (they keep the chain as-is), matching Python behavior
 * where iszero uses are skipped before the truthy check.
 *)
Definition ao_resolve_operand_def:
  ao_resolve_operand chain_map use_opcode op =
    case op of
      Var v =>
        (case ALOOKUP chain_map v of
           NONE => op
         | SOME chain =>
             let chain_len = LENGTH chain in
             (* Skip iszero uses — they keep the chain as-is *)
             if use_opcode = ISZERO then op
             else
               let keep_count =
                 if is_truthy_inst use_opcode then
                   1 - chain_len MOD 2
                 else
                   1 + chain_len MOD 2 in
               if keep_count >= chain_len then op
               else
                 let idx = chain_len - 1 - keep_count in
                 if idx < chain_len then
                   case (EL idx chain).inst_operands of
                     [src] => src
                   | _ => op
                 else op)
    | _ => op
End

(*
 * Apply iszero chain optimization to a single instruction.
 * Each instruction's operands are resolved based on THAT instruction's
 * opcode, matching Python's per-use update_operands behavior.
 *)
Definition ao_optimize_iszero_inst_def:
  ao_optimize_iszero_inst chain_map inst =
    inst with inst_operands :=
      MAP (ao_resolve_operand chain_map inst.inst_opcode) inst.inst_operands
End

(*
 * Apply iszero chain optimization to a block.
 *)
Definition ao_optimize_iszero_block_def:
  ao_optimize_iszero_block dfg bb =
    let chain_map = ao_build_chain_map dfg bb.bb_instructions in
    bb with bb_instructions :=
      MAP (ao_optimize_iszero_inst chain_map) bb.bb_instructions
End

(* ===== Comparator Iszero Flip Mini-Pass ===== *)

(*
 * Ports Python lines 481-531 of algebraic_optimization.py.
 * For comparators with single use: if use is iszero (with non-assert
 * downstream), remove the iszero and flip strict→non-strict (e.g. GT→LT
 * with val+1). If use is assert, insert iszero before assert and flip.
 *
 * 2-phase approach: scan all instructions for qualifying patterns,
 * then FLAT MAP to apply changes. Needed because this modifies two
 * instructions (the comparator and its consumer).
 *)

Definition is_comparator_def:
  is_comparator (opc : opcode) <=>
    (opc = GT \/ opc = LT \/ opc = SGT \/ opc = SLT)
End

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
            (* Guard: skip if literal = never boundary (already handled by peephole) *)
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
                     (* Remove iszero: flip comparator, convert iszero to ASSIGN *)
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

(*
 * Apply cmp_flip changes to a single instruction.
 *   - flips: update opcode + operands
 *   - removes: convert iszero to ASSIGN (keeps operands = pass-through)
 *   - inserts: prepend iszero before assert + update assert operand
 *)
Definition ao_cmp_flip_apply_inst_def:
  ao_cmp_flip_apply_inst flips removes inserts inst =
    case ALOOKUP flips inst.inst_id of
      SOME (new_opc, new_w, orig_op1) =>
        [inst with <| inst_opcode := new_opc;
                      inst_operands := [orig_op1; Lit new_w] |>]
    | NONE =>
        if MEM inst.inst_id removes then
          (* Remove iszero: convert to ASSIGN (pass through operand) *)
          [inst with <| inst_opcode := ASSIGN |>]
        else
          case ALOOKUP inserts inst.inst_id of
            SOME (cmp_out, fresh, cmp_id) =>
              (* Insert iszero before assert, update assert operand *)
              [<| inst_id := cmp_id; inst_opcode := ISZERO;
                  inst_operands := [Var cmp_out];
                  inst_outputs := [fresh] |>;
               inst with <| inst_operands := [Var fresh] |>]
          | NONE => [inst]
End

(*
 * Apply cmp_flip to a function: scan all instructions, then FLAT MAP per block.
 *)
Definition ao_cmp_flip_function_def:
  ao_cmp_flip_function dfg fn =
    let all_insts = fn_insts fn in
    let (flips, removes, inserts) = ao_cmp_flip_scan dfg all_insts in
    if NULL flips then fn  (* fast path: nothing to do *)
    else
      fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          FLAT (MAP (ao_cmp_flip_apply_inst flips removes inserts)
                    bb.bb_instructions))
          fn.fn_blocks
End

(* ===== Block and Function Transform ===== *)

Definition ao_peephole_block_def:
  ao_peephole_block dfg ra bb =
    bb with bb_instructions :=
      FLAT (MAPi (\idx inst.
        let inst' = ao_handle_offset_inst inst in
        let inst'' = ao_pre_flip_inst inst' in
        let result = ao_peephole_inst dfg ra bb.bb_label idx inst'' in
        MAP ao_post_flip_inst result)
        bb.bb_instructions)
End

(*
 * Full pass: peephole → cmp_flip → iszero chains → peephole → cmp_flip.
 * Matches Python: _handle_offset(); _algebraic_opt(); _optimize_iszero_chains(); _algebraic_opt()
 * cmp_flip is integrated into each _algebraic_opt call (lines 481-531).
 * Note: offset is folded into peephole_block.
 *)
Definition ao_transform_function_def:
  ao_transform_function fn =
    let dfg = dfg_build_function fn in
    let ra = range_analyze fn in
    (* Pass 1a: peephole *)
    let fn1 = fn with fn_blocks :=
      MAP (ao_peephole_block dfg ra) fn.fn_blocks in
    (* Pass 1b: comparator iszero flip (needs fresh DFG) *)
    let dfg1b = dfg_build_function fn1 in
    let fn1b = ao_cmp_flip_function dfg1b fn1 in
    (* Pass 2: iszero chain optimization (needs fresh DFG) *)
    let dfg2 = dfg_build_function fn1b in
    let fn2 = fn1b with fn_blocks :=
      MAP (ao_optimize_iszero_block dfg2) fn1b.fn_blocks in
    (* Pass 3a: second peephole (needs fresh DFG + range) *)
    let dfg3 = dfg_build_function fn2 in
    let ra3 = range_analyze fn2 in
    let fn3 = fn2 with fn_blocks :=
      MAP (ao_peephole_block dfg3 ra3) fn2.fn_blocks in
    (* Pass 3b: second comparator iszero flip *)
    let dfg3b = dfg_build_function fn3 in
    ao_cmp_flip_function dfg3b fn3
End

Definition ao_transform_context_def:
  ao_transform_context ctx =
    ctx with ctx_functions := MAP ao_transform_function ctx.ctx_functions
End
