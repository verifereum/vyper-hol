(*
 * Affine Folding Pass — Definitions
 *
 * Ports vyper/venom/passes/affine_folding.py to HOL4.
 *
 * Lattice-driven affine chain folding: collapses chains of add/sub
 * into single operations. For example:
 *   add(add(x, 3), 5)  =>  add(x, 8)
 *
 * TOP-LEVEL:
 *   af_transform_function  — function-level transform
 *
 * Source: vyper/venom/passes/affine_folding.py
 *)

Theory affineFoldingDefs
Ancestors
  passSimulationDefs passSharedDefs dfgDefs dfgAnalysisProps
  venomExecSemantics venomInst
Libs
  pred_setTheory

(* ===== Utilities ===== *)

(* PUSH instruction byte width.
   Python: _push_size(value) — 0 for PUSH0, else ceil(bit_length / 8). *)
Definition push_size_def:
  push_size (w : bytes32) =
    if w = 0w then 0n
    else (LOG2 (w2n w) + 8) DIV 8
End

(* ===== VarInfo Lattice ===== *)

(*
 * Affine knowledge: value = base + offset (mod 2^256).
 * base = NONE means a pure constant (offset only).
 * base = SOME op means value = op + offset.
 *
 * Python: @dataclass VarInfo(base: IROperand | None, offset: int)
 *)
Datatype:
  var_info = VarInfo (operand option) bytes32
End

Definition vi_base_def:
  vi_base (VarInfo b _) = b
End

Definition vi_offset_def:
  vi_offset (VarInfo _ off) = off
End

(* Lookup VarInfo for an operand.
   Python: _lookup(op, info) *)
Definition vi_lookup_def:
  vi_lookup (info : (string, var_info) alist) (op : operand) =
    case op of
      Var v => (case ALOOKUP info v of
                  SOME vi => vi
                | NONE => VarInfo (SOME op) 0w)
    | Lit w => VarInfo NONE w
    | Label _ => VarInfo (SOME op) 0w
End

(* Transfer function for ADD: (lhs + rhs).
   Python: transfer_add(lhs, rhs, out) *)
Definition transfer_add_def:
  transfer_add lhs rhs (out : operand) =
    case (lhs, rhs) of
      (VarInfo NONE loff, VarInfo rbase roff) =>
        VarInfo rbase (roff + loff)
    | (VarInfo lbase loff, VarInfo NONE roff) =>
        VarInfo lbase (loff + roff)
    | _ => VarInfo (SOME out) 0w
End

(* Transfer function for SUB: (minuend - subtrahend).
   Python: transfer_sub(minuend, subtrahend, out) *)
Definition transfer_sub_def:
  transfer_sub minuend subtrahend (out : operand) =
    case subtrahend of
      VarInfo NONE soff =>
        (case minuend of
           VarInfo mbase moff => VarInfo mbase (moff - soff))
    | _ => VarInfo (SOME out) 0w
End

(* Transfer function for ASSIGN: propagate unchanged. *)
Definition transfer_assign_def:
  transfer_assign src = src
End

(* ===== Forward VarInfo Computation ===== *)

(*
 * Compute VarInfo lattice in a single forward pass.
 *
 * HOL4 order for ADD [op1; op2]:
 *   Python: lhs = operands[1] = op1, rhs = operands[0] = op2
 * HOL4 order for SUB [op1; op2]:
 *   Python: minuend = operands[1] = op1, subtrahend = operands[0] = op2
 *)
Definition af_compute_info_step_def:
  af_compute_info_step info (inst : instruction) =
    case inst.inst_outputs of
      [out_var] =>
        let out_op = Var out_var in
        if inst.inst_opcode = ADD then
          (case inst.inst_operands of
             [op1; op2] =>
               let lhs = vi_lookup info op1 in
               let rhs = vi_lookup info op2 in
               (out_var, transfer_add lhs rhs out_op) :: info
           | _ => (out_var, VarInfo (SOME out_op) 0w) :: info)
        else if inst.inst_opcode = SUB then
          (case inst.inst_operands of
             [op1; op2] =>
               let minuend = vi_lookup info op1 in
               let subtrahend = vi_lookup info op2 in
               (out_var, transfer_sub minuend subtrahend out_op) :: info
           | _ => (out_var, VarInfo (SOME out_op) 0w) :: info)
        else if inst.inst_opcode = ASSIGN then
          (case inst.inst_operands of
             [src] =>
               (out_var, transfer_assign (vi_lookup info src)) :: info
           | _ => (out_var, VarInfo (SOME out_op) 0w) :: info)
        else
          (out_var, VarInfo (SOME out_op) 0w) :: info
    | _ => info
End

Definition af_compute_var_info_def:
  af_compute_var_info (insts : instruction list) =
    FOLDL af_compute_info_step [] insts
End

Definition af_compute_fn_var_info_def:
  af_compute_fn_var_info fn =
    af_compute_var_info (fn_insts fn)
End

(* ===== Affine Chain Folding ===== *)

(* Extract value and literal operands from an instruction.
   Returns SOME (value_op, lit_op) or NONE. *)
Definition af_extract_val_lit_def:
  af_extract_val_lit inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_lit_op op2 /\ ~is_lit_op op1 then SOME (op1, op2)
        else if is_lit_op op1 /\ ~is_lit_op op2 then SOME (op2, op1)
        else NONE
    | _ => NONE
End

(*
 * Walk producers from imm_base toward lattice_base, stopping at the first
 * multi-use intermediate. Preserves shared base pointers for CSE/DFT.
 *
 * Uses visited set for termination.
 *)
Definition af_effective_base_def:
  af_effective_base dfg visited current lattice_base =
    if current = lattice_base then lattice_base
    else case current of
      Var v =>
        if LENGTH (dfg_get_uses dfg v) > 1 then current
        else (case dfg_get_def dfg v of
          NONE => current
        | SOME prod =>
            if prod.inst_id IN visited then current
            else if prod.inst_opcode = ASSIGN then
              (case prod.inst_operands of
                 [src] => af_effective_base dfg
                            (prod.inst_id INSERT visited) src lattice_base
               | _ => current)
            else if prod.inst_opcode = ADD then
              (case af_extract_val_lit prod of
                 SOME (val_op, _) =>
                   af_effective_base dfg
                     (prod.inst_id INSERT visited) val_op lattice_base
               | NONE => current)
            else current)
    | _ => current
Termination
  WF_REL_TAC `inv_image $< (\(dfg,visited,_,_). CARD (dfg_def_ids dfg DIFF visited))`
  >> rpt strip_tac
  >> imp_res_tac dfg_get_def_implies_dfg_def_ids
  >> irule CARD_PSUBSET
  >> simp[FINITE_DIFF, dfg_def_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION]
  >> qexists_tac `prod.inst_id` >> simp[]
End

(* Extract immediate base and literal for SUB [op1; op2].
   SUB: op2 must be literal, op1 must not be. *)
Definition af_extract_sub_val_lit_def:
  af_extract_sub_val_lit inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_lit_op op2 /\ ~is_lit_op op1 then
          SOME (op1, op2)
        else NONE
    | _ => NONE
End

(*
 * Lattice-driven affine chain folding for a single instruction.
 * Returns SOME result if rewrite applied, NONE otherwise.
 *)
Definition af_rewrite_inst_def:
  af_rewrite_inst dfg var_info inst =
    if inst.inst_opcode <> ADD /\ inst.inst_opcode <> SUB then NONE
    else case inst.inst_outputs of
      [out_var] =>
        (case ALOOKUP var_info out_var of
           NONE => NONE
         | SOME vi =>
             case vi_base vi of
               NONE => NONE
             | SOME vi_b =>
                 if vi_b = Var out_var then NONE
                 else case vi_b of
                   Label _ => NONE
                 | _ =>
                   let extract =
                     if inst.inst_opcode = ADD then
                       af_extract_val_lit inst
                     else
                       af_extract_sub_val_lit inst in
                   case extract of
                     NONE => NONE
                   | SOME (imm_base, curr_lit_op) =>
                       if vi_b = imm_base then NONE
                       else
                         let eff_base = af_effective_base dfg {}
                                          imm_base vi_b in
                         if eff_base = imm_base then NONE
                         else
                           let offset = vi_offset vi in
                           let eff_offset_opt =
                             if eff_base = vi_b then SOME offset
                             else case eff_base of
                               Var ev =>
                                 (case ALOOKUP var_info ev of
                                    SOME evi =>
                                      if vi_base evi = SOME vi_b then
                                        SOME (offset - vi_offset evi)
                                      else NONE
                                  | NONE => NONE)
                             | _ => NONE in
                           case eff_offset_opt of
                             NONE => NONE
                           | SOME eff_offset =>
                               if eff_offset = 0w then
                                 SOME (inst with <| inst_opcode := ASSIGN;
                                                    inst_operands := [eff_base] |>)
                               else
                                 let curr_lit_w =
                                   case curr_lit_op of Lit w => w | _ => 0w in
                                 if push_size eff_offset > push_size curr_lit_w then
                                   NONE
                                 else
                                   SOME (inst with <| inst_opcode := ADD;
                                           inst_operands :=
                                             [Lit eff_offset; eff_base] |>))
    | _ => NONE
End

(* ===== Block and Function Transform ===== *)

Definition af_transform_inst_def:
  af_transform_inst dfg var_info inst =
    if inst.inst_outputs = [] then inst
    else if inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
            inst.inst_opcode = PARAM then inst
    else
      case af_rewrite_inst dfg var_info inst of
        SOME result => result
      | NONE => inst
End

Definition af_transform_block_def:
  af_transform_block dfg var_info bb =
    bb with bb_instructions :=
      MAP (af_transform_inst dfg var_info) bb.bb_instructions
End

Definition af_transform_function_def:
  af_transform_function fn =
    let var_info = af_compute_fn_var_info fn in
    let dfg = dfg_build_function fn in
    fn with fn_blocks :=
      MAP (af_transform_block dfg var_info) fn.fn_blocks
End

Definition af_transform_context_def:
  af_transform_context ctx =
    ctx with ctx_functions := MAP af_transform_function ctx.ctx_functions
End
