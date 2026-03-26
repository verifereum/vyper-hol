(*
 * Sparse Conditional Constant Propagation — Definitions
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Ports vyper/venom/passes/sccp/ to HOL4.
 *
 * Implements the Wegman-Zadeck SCCP algorithm using the generic
 * dataflow framework (df_analyze) with worklist iteration:
 *   - Edge executability encoded in lattice (sl_targets)
 *   - PHI evaluation in edge_transfer (per-predecessor filtering)
 *   - Constant folding for 25 arithmetic operations
 *   - Branch folding (JNZ → JMP when condition known)
 *   - Assert elimination (ASSERT of nonzero → NOP)
 *
 * TOP-LEVEL:
 *   sccp_lattice              — lattice type (const vals + exec targets)
 *   sccp_df_analyze           — analysis via df_analyze Forward
 *   sccp_inst                 — per-instruction transform
 *   sccp_function             — function-level transform (uses df_at)
 *)

Theory sccpDefs
Ancestors
  dfAnalyzeDefs analysisSimDefs passSharedDefs venomExecSemantics

(* ===== Constant lattice ===== *)

Datatype:
  const_val = CL_Top | CL_Const (256 word) | CL_Label string | CL_Bottom
End

Type const_lattice = ``:(string, const_val) fmap``

Definition const_meet_def:
  const_meet CL_Top y = y /\
  const_meet x CL_Top = x /\
  const_meet (CL_Const c1) (CL_Const c2) =
    (if c1 = c2 then CL_Const c1 else CL_Bottom) /\
  const_meet (CL_Label l1) (CL_Label l2) =
    (if l1 = l2 then CL_Label l1 else CL_Bottom) /\
  const_meet _ _ = CL_Bottom
End

Definition const_lookup_def:
  const_lookup (st : const_lattice) v =
    case FLOOKUP st v of NONE => CL_Top | SOME cv => cv
End

(* ===== Constant folding ===== *)

Definition const_eval_operand_def:
  const_eval_operand st (Lit w) = CL_Const w /\
  const_eval_operand st (Var v) = const_lookup st v /\
  const_eval_operand st (Label l) = CL_Label l
End

Datatype:
  eval_ops_result =
    EvalTop
  | EvalBottom
  | EvalConsts ((256 word) list)
End

Definition const_eval_ops_def:
  const_eval_ops st [] = EvalConsts [] /\
  const_eval_ops st (op::ops) =
    case const_eval_operand st op of
      CL_Bottom => EvalBottom
    | CL_Top => EvalTop
    | CL_Label _ => EvalBottom
    | CL_Const c =>
        case const_eval_ops st ops of
          EvalBottom => EvalBottom
        | EvalTop => EvalTop
        | EvalConsts cs => EvalConsts (c :: cs)
End

(* 25 arithmetic operations matching Python's ARITHMETIC_OPS (eval.py) *)
Definition const_eval_arith_def:
  const_eval_arith ADD [a; b] = SOME (word_add a b) /\
  const_eval_arith SUB [a; b] = SOME (word_sub a b) /\
  const_eval_arith MUL [a; b] = SOME (word_mul a b) /\
  const_eval_arith Div [a; b] = SOME (safe_div a b) /\
  const_eval_arith SDIV [a; b] = SOME (safe_sdiv a b) /\
  const_eval_arith Mod [a; b] = SOME (safe_mod a b) /\
  const_eval_arith SMOD [a; b] = SOME (safe_smod a b) /\
  const_eval_arith Exp [a; b] = SOME (word_exp a b) /\
  const_eval_arith EQ [a; b] = SOME (bool_to_word (a = b)) /\
  const_eval_arith LT [a; b] = SOME (bool_to_word (w2n a < w2n b)) /\
  const_eval_arith GT [a; b] = SOME (bool_to_word (w2n a > w2n b)) /\
  const_eval_arith SLT [a; b] = SOME (bool_to_word (word_lt a b)) /\
  const_eval_arith SGT [a; b] = SOME (bool_to_word (word_gt a b)) /\
  const_eval_arith OR [a; b] = SOME (word_or a b) /\
  const_eval_arith AND [a; b] = SOME (word_and a b) /\
  const_eval_arith XOR [a; b] = SOME (word_xor a b) /\
  const_eval_arith NOT [a] = SOME (word_1comp a) /\
  const_eval_arith ISZERO [a] = SOME (bool_to_word (a = 0w)) /\
  const_eval_arith SHL [n; w] = SOME (word_lsl w (w2n n)) /\
  const_eval_arith SHR [n; w] = SOME (word_lsr w (w2n n)) /\
  const_eval_arith SAR [n; w] = SOME (word_asr w (w2n n)) /\
  const_eval_arith SIGNEXTEND [n; w] = SOME (sign_extend n w) /\
  const_eval_arith ADDMOD [a; b; n] = SOME (addmod a b n) /\
  const_eval_arith MULMOD [a; b; n] = SOME (mulmod a b n) /\
  const_eval_arith BYTE [n; x] = SOME (evm_byte n x) /\
  const_eval_arith _ _ = NONE
End

Definition const_try_fold_def:
  const_try_fold op st operands =
    case const_eval_ops st operands of
      EvalBottom => CL_Bottom
    | EvalTop => CL_Top
    | EvalConsts ws =>
        case const_eval_arith op ws of
          SOME r => CL_Const r
        | NONE => CL_Bottom
End

(* Opcodes whose outputs can be constant-folded.
   Non-foldable opcodes (MLOAD, SLOAD, CALL, etc.) get BOTTOM. *)
Definition is_sccp_foldable_def:
  is_sccp_foldable ADD = T /\
  is_sccp_foldable SUB = T /\
  is_sccp_foldable MUL = T /\
  is_sccp_foldable Div = T /\
  is_sccp_foldable SDIV = T /\
  is_sccp_foldable Mod = T /\
  is_sccp_foldable SMOD = T /\
  is_sccp_foldable Exp = T /\
  is_sccp_foldable EQ = T /\
  is_sccp_foldable LT = T /\
  is_sccp_foldable GT = T /\
  is_sccp_foldable SLT = T /\
  is_sccp_foldable SGT = T /\
  is_sccp_foldable OR = T /\
  is_sccp_foldable AND = T /\
  is_sccp_foldable XOR = T /\
  is_sccp_foldable NOT = T /\
  is_sccp_foldable ISZERO = T /\
  is_sccp_foldable SHL = T /\
  is_sccp_foldable SHR = T /\
  is_sccp_foldable SAR = T /\
  is_sccp_foldable SIGNEXTEND = T /\
  is_sccp_foldable ADDMOD = T /\
  is_sccp_foldable MULMOD = T /\
  is_sccp_foldable BYTE = T /\
  is_sccp_foldable _ = F
End

(* ===== SCCP Lattice for df_analyze ===== *)

(* Combined lattice: variable values + outgoing executable targets.
   sl_targets records which successor blocks are reachable from
   this block (determined by the terminator's condition value).
   PHI evaluation happens in edge_transfer, not in block transfer. *)
Datatype:
  sccp_lattice = <|
    sl_vals    : const_lattice;
    sl_targets : string set
  |>
End

Definition sccp_bottom_def:
  sccp_bottom : sccp_lattice =
    <| sl_vals := FEMPTY; sl_targets := {} |>
End

(* Per-variable meet + target set union *)
Definition sccp_join_def:
  sccp_join (a : sccp_lattice) (b : sccp_lattice) =
    <| sl_vals :=
         let keys = FDOM a.sl_vals UNION FDOM b.sl_vals in
         FUN_FMAP (\v. const_meet (const_lookup a.sl_vals v)
                                  (const_lookup b.sl_vals v))
                  keys;
       sl_targets := a.sl_targets UNION b.sl_targets |>
End

(* ===== Per-instruction transfer ===== *)

(* Transfer for non-PHI, non-terminator instructions.
   PHIs are handled in edge_transfer; terminators update sl_targets. *)
Definition sccp_transfer_inst_def:
  sccp_transfer_inst (fn : ir_function) inst (lat : sccp_lattice) =
    if inst.inst_opcode = PHI then lat
    else if is_terminator inst.inst_opcode then
      (* Terminator: determine outgoing executable edges *)
      if inst.inst_opcode = JMP then
        (case inst.inst_operands of
           [Label dst] =>
             lat with sl_targets := {dst} UNION lat.sl_targets
         | _ => lat)
      else if inst.inst_opcode = JNZ then
        let cond_val =
          case inst.inst_operands of
            (cond_op :: _) =>
              const_eval_operand lat.sl_vals cond_op
          | _ => CL_Bottom in
        (case inst.inst_operands of
           [_; Label t_lbl; Label f_lbl] =>
             (case cond_val of
                CL_Const c =>
                  if c <> 0w then
                    lat with sl_targets :=
                      {t_lbl} UNION lat.sl_targets
                  else
                    lat with sl_targets :=
                      {f_lbl} UNION lat.sl_targets
              | _ =>
                  lat with sl_targets :=
                    {t_lbl; f_lbl} UNION lat.sl_targets)
         | _ => lat)
      else if inst.inst_opcode = DJMP then
        let targets = FOLDR (\op acc.
          case op of Label dst => dst INSERT acc | _ => acc)
          {} (TL inst.inst_operands) in
        lat with sl_targets := targets UNION lat.sl_targets
      else lat (* STOP, REVERT, etc. — no successors *)
    else if inst.inst_outputs = [] then lat
    else if inst.inst_opcode = ASSIGN then
      (case (inst.inst_operands, inst.inst_outputs) of
         ([op], [out]) =>
           lat with sl_vals :=
             lat.sl_vals |+ (out, const_eval_operand lat.sl_vals op)
       | (_, outs) =>
           lat with sl_vals :=
             FOLDL (\l v. l |+ (v, CL_Bottom)) lat.sl_vals outs)
    else
      (case inst.inst_outputs of
         [out] =>
           if is_sccp_foldable inst.inst_opcode then
             let folded = const_try_fold inst.inst_opcode
                            lat.sl_vals inst.inst_operands in
             lat with sl_vals := lat.sl_vals |+ (out, folded)
           else
             lat with sl_vals := lat.sl_vals |+ (out, CL_Bottom)
       | outs =>
           lat with sl_vals :=
             FOLDL (\l v. l |+ (v, CL_Bottom)) lat.sl_vals outs)
End

(* ===== Edge transfer: executability filter + PHI evaluation ===== *)

(* Extract (label, operand) pairs from PHI operands:
   [Label l1, Var v1, Label l2, Var v2, ...] → [(l1, Var v1), ...] *)
Definition sccp_phi_pairs_def:
  sccp_phi_pairs [] = [] /\
  sccp_phi_pairs [_] = [] /\
  sccp_phi_pairs (Label lbl :: val_op :: rest) =
    (lbl, val_op) :: sccp_phi_pairs rest /\
  sccp_phi_pairs (_ :: _ :: rest) = sccp_phi_pairs rest
End

(* Evaluate one PHI instruction for a specific predecessor edge.
   Returns SOME (out_var, value) if this PHI has an operand from src. *)
Definition sccp_eval_phi_for_edge_def:
  sccp_eval_phi_for_edge src_lbl src_vals inst =
    case inst.inst_outputs of
      [out] =>
        let pairs = sccp_phi_pairs inst.inst_operands in
        (case FIND (\(lbl, _). lbl = src_lbl) pairs of
           SOME (_, val_op) =>
             SOME (out, const_eval_operand src_vals val_op)
         | NONE => NONE)
    | _ => NONE
End

(* Evaluate all PHIs in destination block for a specific edge.
   Updates lattice with PHI output values from src's perspective. *)
Definition sccp_eval_phis_for_edge_def:
  sccp_eval_phis_for_edge src_lbl src_vals dst_instrs lat =
    FOLDL (\lat' inst.
      if inst.inst_opcode = PHI then
        (case sccp_eval_phi_for_edge src_lbl src_vals inst of
           SOME (out, v) => lat' with sl_vals :=
             lat'.sl_vals |+ (out, v)
         | NONE => lat')
      else lat')
    lat dst_instrs
End

(* Edge transfer: if edge (src → dst) is executable, evaluate dst's
   PHIs using src's lattice values; otherwise return bottom (all TOP).
   The fn context provides access to dst's block instructions. *)
Definition sccp_edge_transfer_def:
  sccp_edge_transfer (fn : ir_function) src dst
                     (lat : sccp_lattice) =
    if dst NOTIN lat.sl_targets then sccp_bottom
    else
      let dst_instrs =
        case lookup_block dst fn.fn_blocks of
          NONE => []
        | SOME bb => bb.bb_instructions in
      sccp_eval_phis_for_edge src lat.sl_vals dst_instrs
        (lat with sl_targets := {})
End

(* ===== Top-level analysis via df_analyze ===== *)

(* Run SCCP analysis via df_analyze. Returns the full df_state;
   callers use df_at to query per-instruction lattice values. *)
Definition sccp_df_analyze_def:
  sccp_df_analyze fn =
    let entry_val = OPTION_MAP (\lbl. (lbl, sccp_bottom))
          (fn_entry_label fn) in
    df_analyze Forward sccp_bottom sccp_join
      sccp_transfer_inst sccp_edge_transfer fn entry_val fn
End

(* ===== Per-instruction transform ===== *)

Definition const_subst_op_def:
  const_subst_op (st : const_lattice) (Var v) =
    (case const_lookup st v of
       CL_Const c => Lit c
     | _ => Var v) /\
  const_subst_op st (Lit w) = Lit w /\
  const_subst_op st (Label l) = Label l
End

(* Python _replace_constants: substitute constants, fold branches *)
Definition sccp_inst_def:
  sccp_inst (st : const_lattice) inst =
    if inst.inst_opcode = PHI then inst
    else
    let inst' = inst with inst_operands :=
      MAP (const_subst_op st) inst.inst_operands in
    if inst'.inst_opcode = JNZ then
      (case inst'.inst_operands of
         [Lit cond; Label t_lbl; Label f_lbl] =>
           if cond <> 0w then
             inst' with <| inst_opcode := JMP;
                           inst_operands := [Label t_lbl] |>
           else
             inst' with <| inst_opcode := JMP;
                           inst_operands := [Label f_lbl] |>
       | _ => inst')
    else if inst'.inst_opcode = ASSERT \/
            inst'.inst_opcode = ASSERT_UNREACHABLE then
      (case inst'.inst_operands of
         [Lit w] => if w <> 0w then mk_nop_inst inst' else inst'
       | _ => inst')
    else inst'
End

(* Check for provably-failing assertions (compile-time error).
   Python: raises StaticAssertionException.
   Uses df_at to get per-instruction lattice values. *)
Definition sccp_has_static_assertion_failure_def:
  sccp_has_static_assertion_failure (result : sccp_lattice df_state) fn <=>
    ?bb idx inst.
      MEM bb fn.fn_blocks /\
      idx < LENGTH bb.bb_instructions /\
      EL idx bb.bb_instructions = inst /\
      (inst.inst_opcode = ASSERT \/
       inst.inst_opcode = ASSERT_UNREACHABLE) /\
      let vals = (df_at sccp_bottom result bb.bb_label idx).sl_vals in
      (case inst.inst_operands of
         [Var v] =>
           (case const_lookup vals v of
              CL_Const c => c = 0w
            | _ => F)
       | [Lit w] => w = 0w
       | _ => F)
End

(* ===== Function-level transform ===== *)

(* Returns NONE if static assertion failure (compile error).
   Returns SOME fn' with the optimized function otherwise.
   Uses df_at per instruction: each sccp_inst gets the lattice
   value just before that instruction (pre-instruction fixpoint). *)
Definition sccp_function_def:
  sccp_function fn =
    let result = sccp_df_analyze fn in
    if sccp_has_static_assertion_failure result fn then NONE
    else SOME (clear_nops_function
      (analysis_function_transform sccp_bottom result
        (\lat inst. [sccp_inst lat.sl_vals inst]) fn))
End
