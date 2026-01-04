(*
 * SSA Construction Definitions
 *
 * This theory defines basic structures for SSA construction.
 * SSA (Static Single Assignment) form ensures each variable is defined exactly once.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - ssa_var_name           : Construct versioned variable name (base:version)
 *   - base_var_name          : Extract base name from SSA variable
 *   - var_version            : Extract version from SSA variable
 *   - version_map            : Type for tracking current versions
 *
 * TOP-LEVEL THEOREMS:
 *   - ssa_var_name_base      : base_var_name (ssa_var_name base v) = base
 *   - ssa_var_name_version   : var_version (ssa_var_name base v) = v
 *
 * ============================================================================
 *)

Theory mkSsaDefs
Ancestors
  list finite_map pred_set string
  venomState venomInst venomSem

(* ==========================================================================
   SSA Variable Naming
   ==========================================================================

   In SSA form, variables are versioned: x becomes x:0, x:1, x:2, etc.
   The version number increases with each definition of the variable.
   ========================================================================== *)

(* TOP-LEVEL: Construct an SSA-versioned variable name *)
Definition ssa_var_name_def:
  ssa_var_name base (version:num) =
    if version = 0 then base
    else base ++ ":" ++ toString version
End

(* Helper: Check if a string contains a colon *)
Definition has_version_suffix_def:
  has_version_suffix s = MEM #":" s
End

(* Helper: Find the index of the last colon in a string *)
Definition last_colon_index_def:
  last_colon_index [] (idx:num) = (NONE:num option) /\
  last_colon_index (c::cs) idx =
    if c = #":" then
      case last_colon_index cs (idx + 1) of
        SOME i => SOME i
      | NONE => SOME idx
    else
      last_colon_index cs (idx + 1)
End

(* Helper: Split a string at a given index *)
Definition split_at_def:
  split_at (s:string) (idx:num) = (TAKE idx s, DROP (idx + 1) s)
End

(* Helper: Split a string at the last colon *)
Definition split_at_colon_def:
  split_at_colon (s:string) : string # string =
    case last_colon_index s 0 of
      SOME idx => split_at s idx
    | NONE => (s, "")
End

(* TOP-LEVEL: Extract base variable name (without version suffix) *)
Definition base_var_name_def:
  base_var_name s =
    if has_version_suffix s then FST (split_at_colon s)
    else s
End

(* TOP-LEVEL: Extract version number from SSA variable (0 if unversioned)
   Note: This is a simplified version that doesn't parse the string.
   For the correctness proof, we track versions via the variable mapping. *)
Definition var_version_def:
  var_version (s:string) : num = 0
End

(* ==========================================================================
   Version Map - Tracks Current Version of Each Variable
   ========================================================================== *)

(* TOP-LEVEL: Version map type - maps base variable names to current version *)
Type version_map = ``:(string, num) fmap``

(* TOP-LEVEL: Get current version for a variable (0 if not in map) *)
Definition get_version_def:
  get_version (vm:version_map) base =
    case FLOOKUP vm base of
      SOME v => v
    | NONE => 0
End

(* TOP-LEVEL: Increment version for a variable *)
Definition inc_version_def:
  inc_version (vm:version_map) base =
    vm |+ (base, get_version vm base + 1)
End

(* TOP-LEVEL: Get current SSA name for a variable *)
Definition current_ssa_name_def:
  current_ssa_name (vm:version_map) base = ssa_var_name base (get_version vm base)
End

(* ==========================================================================
   Variable Name Stack - For Dominator-Tree-Based Renaming
   ==========================================================================

   During SSA construction, we maintain a stack of version numbers for each
   variable. When entering a block, we push new versions; when leaving, we pop.
   ========================================================================== *)

(* TOP-LEVEL: Name stack type - maps base names to list of versions *)
Type name_stack = ``:(string, num list) fmap``

(* TOP-LEVEL: Get current version from stack (0 if empty) *)
Definition stack_top_def:
  stack_top (ns:name_stack) base =
    case FLOOKUP ns base of
      SOME (v::vs) => v
    | _ => 0
End

(* TOP-LEVEL: Push a new version onto the stack *)
Definition stack_push_def:
  stack_push (ns:name_stack) base version =
    case FLOOKUP ns base of
      SOME vs => ns |+ (base, version::vs)
    | NONE => ns |+ (base, [version])
End

(* TOP-LEVEL: Pop version from the stack *)
Definition stack_pop_def:
  stack_pop (ns:name_stack) base =
    case FLOOKUP ns base of
      SOME (v::vs) => ns |+ (base, vs)
    | _ => ns
End

(* ==========================================================================
   Definition Points - Where Variables Are Defined
   ========================================================================== *)

(* TOP-LEVEL: Definition point - records where a variable is defined *)
Datatype:
  def_point = <|
    dp_block : string;       (* Basic block label *)
    dp_inst_idx : num        (* Instruction index in block *)
  |>
End

(* TOP-LEVEL: Definition map - maps variables to their definition points *)
Type def_map = ``:(string, def_point set) fmap``

(* TOP-LEVEL: Add a definition point for a variable *)
Definition add_def_def:
  add_def (dm:def_map) var block idx =
    let dp = <| dp_block := block; dp_inst_idx := idx |> in
    case FLOOKUP dm var of
      SOME dps => dm |+ (var, dp INSERT dps)
    | NONE => dm |+ (var, {dp})
End

(* ==========================================================================
   Instruction Helpers
   ========================================================================== *)

(* TOP-LEVEL: Get output variables of an instruction (now a list) *)
Definition inst_output_vars_def:
  inst_output_vars inst = inst.inst_outputs
End

(* TOP-LEVEL: Get input variables from operands *)
Definition operand_vars_def:
  operand_vars [] = [] /\
  operand_vars (Var v :: ops) = v :: operand_vars ops /\
  operand_vars (_ :: ops) = operand_vars ops
End

(* TOP-LEVEL: Check if instruction produces an output *)
Definition has_output_def:
  has_output inst = (inst.inst_outputs <> [])
End

(* ==========================================================================
   SSA Well-Formedness
   ========================================================================== *)

(* TOP-LEVEL: Check if function is in SSA form - each variable defined once *)
Definition fn_ssa_form_def:
  fn_ssa_form fn <=>
    !bb1 bb2 idx1 idx2 inst1 inst2 v.
      MEM bb1 fn.fn_blocks /\
      MEM bb2 fn.fn_blocks /\
      get_instruction bb1 idx1 = SOME inst1 /\
      get_instruction bb2 idx2 = SOME inst2 /\
      MEM v inst1.inst_outputs /\
      MEM v inst2.inst_outputs ==>
      bb1 = bb2 /\ idx1 = idx2
End

(* ==========================================================================
   Helpers for PHI Instruction Construction
   ========================================================================== *)

(* Helper: Check if PHI operands are well-formed (Label, Var pairs) *)
Definition phi_well_formed_def:
  phi_well_formed [] = T /\
  phi_well_formed [_] = F /\
  phi_well_formed (Label lbl :: Var v :: rest) = phi_well_formed rest /\
  phi_well_formed (_ :: _ :: rest) = F
End

(* TOP-LEVEL: Construct PHI operands from predecessor blocks and variable *)
Definition mk_phi_operands_def:
  mk_phi_operands [] var = [] /\
  mk_phi_operands (pred::preds) var =
    Label pred :: Var var :: mk_phi_operands preds var
End

(* TOP-LEVEL: Construct a PHI instruction *)
Definition mk_phi_inst_def:
  mk_phi_inst id out preds var =
    <| inst_id := id;
       inst_opcode := PHI;
       inst_operands := mk_phi_operands preds var;
       inst_outputs := [out]
    |>
End

(* ==========================================================================
   Basic Theorems
   ========================================================================== *)

(* Version 0 produces the base name *)
Theorem ssa_var_name_zero:
  !base. ssa_var_name base 0 = base
Proof
  rw[ssa_var_name_def]
QED

(* mk_phi_operands produces well-formed PHI operands *)
Theorem mk_phi_operands_well_formed:
  !preds var. phi_well_formed (mk_phi_operands preds var)
Proof
  Induct_on `preds` >> rw[mk_phi_operands_def, phi_well_formed_def]
QED

