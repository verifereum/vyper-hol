(*
 * Syntactic unit hypotheses for PLAN §5.8 (not compiler checks).
 * TOP-LEVEL: retpc_var, opaque_use_ok, retpc_shape_ok,
 *   label_positions_ok,
 *   reserved_label, entry_fn_first, unit_shape_ok, o1_source_unit_ok;
 *   entry_fn_first_lookup (L4).
 * Helpers: copy_phi_var is the least seeded ASSIGN/PHI closure;
 *   retpc_use_ok specifies the opaque return-PC operand positions;
 *   inst_shape_ok / fn_shape_ok collect output-shape restrictions;
 *   call_checks_ok: failed calls end the frame with an exception
 *   (revert_path, flag_fails, flag_path, calls_flagged).
 * Raw-only restrictions are deliberately absent from unit_shape_ok.
 *)
Theory unitShapeDefs
Ancestors
  venomCompilerTypes venomInst venomWf venomEffects stackPlanTypes
  stackPlanGen contextCodegenRel simplifyCfgDefs
  list

(* ===== Least copy/PHI closure ===== *)

(* Finite derivations, not recursive graph traversal: an unseeded cycle adds
 * nothing; a seeded cycle propagates opacity.  A PHI needs just ONE opaque
 * incoming variable, not all incoming variables. *)
Inductive copy_phi_var:
[~seed:]
  (!origin fn inst x.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = origin /\
    MEM x inst.inst_outputs ==> copy_phi_var origin fn x)
[~assign:]
  (!origin fn inst x y.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var y] /\ MEM x inst.inst_outputs /\
    copy_phi_var origin fn y ==> copy_phi_var origin fn x)
[~phi:]
  (!origin fn inst x y.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
    MEM (Var y) inst.inst_operands /\ MEM x inst.inst_outputs /\
    copy_phi_var origin fn y ==> copy_phi_var origin fn x)
End

Definition gas_var_def:
  gas_var fn x <=> copy_phi_var GAS fn x
End

Definition retpc_var_def:
  retpc_var fn x <=> copy_phi_var RETPC_PARAM fn x
End

(* Boundary fact: no circular derivation can invent an opaque seed. *)
Theorem copy_phi_var_has_seed:
  !origin fn x. copy_phi_var origin fn x ==>
    ?inst y. MEM inst (fn_insts fn) /\ inst.inst_opcode = origin /\
             MEM y inst.inst_outputs
Proof
  Induct_on `copy_phi_var` >> metis_tac[]
QED

Theorem copy_phi_var_no_seed:
  (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> origin) ==>
  !x. ~copy_phi_var origin fn x
Proof
  metis_tac[copy_phi_var_has_seed]
QED

(* ===== Opaque uses and label positions ===== *)

Definition gas_use_ok_def:
  gas_use_ok inst x <=>
    inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
    ((inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
     ?rest. inst.inst_operands = Var x :: rest /\ ~MEM (Var x) rest)
End

Definition retpc_use_ok_def:
  retpc_use_ok inst x <=>
    inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
    (MEM inst.inst_opcode [RET; RETFMP; DRET] /\
     ?front. inst.inst_operands = front ++ [Var x] /\ ~MEM (Var x) front)
End

Definition opaque_use_ok_def:
  opaque_use_ok fn <=>
    !inst x. MEM inst (fn_insts fn) /\ MEM (Var x) inst.inst_operands ==>
      (retpc_var fn x ==> retpc_use_ok inst x)
End

Theorem opaque_use_ok_retpc_use:
  opaque_use_ok fn /\ retpc_var fn x /\ MEM inst (fn_insts fn) /\
  MEM (Var x) inst.inst_operands ==> retpc_use_ok inst x
Proof
  metis_tac[opaque_use_ok_def]
QED

(* The code SimplifyCFG keeps: the blocks reachable from the entry block,
   each PHI keeping only the pairs from reachable predecessors
   (remove_unreachable_blocks, then fix_all_phis' operand filter). *)
Definition reachable_preds_def:
  reachable_preds fn lbl =
    FILTER (\l. fn_reachable fn l /\ fn_cfg_edge fn l lbl)
      (MAP (\bb. bb.bb_label) fn.fn_blocks)
End

Definition reachable_inst_def:
  reachable_inst fn lbl inst =
    if inst.inst_opcode = PHI then
      inst with inst_operands :=
        filter_phi_ops (reachable_preds fn lbl) inst.inst_operands
    else inst
End

Definition reachable_fn_def:
  reachable_fn fn =
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
                   MAP (reachable_inst fn bb.bb_label) bb.bb_instructions)
        (FILTER (\bb. fn_reachable fn bb.bb_label) fn.fn_blocks)
End

Theorem reachable_inst_fields:
  (reachable_inst fn lbl inst).inst_opcode = inst.inst_opcode /\
  (reachable_inst fn lbl inst).inst_outputs = inst.inst_outputs /\
  (inst.inst_opcode <> PHI ==> reachable_inst fn lbl inst = inst) /\
  (MEM op (reachable_inst fn lbl inst).inst_operands ==>
   MEM op inst.inst_operands)
Proof
  rw[reachable_inst_def] >> metis_tac[MEM_filter_phi_ops]
QED

Theorem MEM_fn_insts_blocks_iff:
  !bbs inst. MEM inst (fn_insts_blocks bbs) <=>
             ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem MEM_reachable_fn_insts:
  !fn inst. MEM inst (fn_insts (reachable_fn fn)) <=>
            ?bb i. MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
                   MEM i bb.bb_instructions /\
                   inst = reachable_inst fn bb.bb_label i
Proof
  simp[reachable_fn_def, fn_insts_def, MEM_fn_insts_blocks_iff, MEM_FILTER,
       MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem reachable_fn_insts_mem:
  !fn inst. MEM inst (fn_insts (reachable_fn fn)) ==>
            ?lbl i. MEM i (fn_insts fn) /\ inst = reachable_inst fn lbl i
Proof
  simp[MEM_reachable_fn_insts, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[]
QED

Theorem reachable_fn_insts_nonphi:
  !fn inst. MEM inst (fn_insts (reachable_fn fn)) /\ inst.inst_opcode <> PHI ==>
            MEM inst (fn_insts fn)
Proof
  rpt strip_tac >> drule reachable_fn_insts_mem >> strip_tac >>
  gvs[reachable_inst_fields]
QED

Theorem reachable_fn_insts_operand:
  !fn inst op. MEM inst (fn_insts (reachable_fn fn)) /\
               MEM op inst.inst_operands ==>
               ?i. MEM i (fn_insts fn) /\ i.inst_opcode = inst.inst_opcode /\
                   MEM op i.inst_operands
Proof
  rpt strip_tac >> drule reachable_fn_insts_mem >> strip_tac >>
  gvs[reachable_inst_fields] >> metis_tac[reachable_inst_fields]
QED

Theorem copy_phi_var_mono:
  !origin fn x. copy_phi_var origin fn x ==>
    !fn'. (!i. MEM i (fn_insts fn) ==> MEM i (fn_insts fn')) ==>
          copy_phi_var origin fn' x
Proof
  Induct_on `copy_phi_var` >> metis_tac[copy_phi_var_rules]
QED

Theorem entry_insts_reachable:
  !fn inst. fn.fn_blocks <> [] /\ MEM inst (HD fn.fn_blocks).bb_instructions /\
            inst.inst_opcode <> PHI ==>
            MEM inst (fn_insts (reachable_fn fn))
Proof
  rw[MEM_reachable_fn_insts] >> Cases_on `fn.fn_blocks` >> gvs[] >>
  qexistsl_tac [`h`, `inst`] >>
  simp[reachable_inst_fields, fn_reachable_def, fn_entry_label_def,
       entry_block_def, relationTheory.RTC_REFL]
QED

Theorem reachable_fn_single_block:
  !fn bb. fn.fn_blocks = [bb] /\
          EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
          reachable_fn fn = fn
Proof
  rw[reachable_fn_def, fn_reachable_def, fn_entry_label_def, entry_block_def,
     relationTheory.RTC_REFL, ir_function_component_equality,
     basic_block_component_equality] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> gvs[EVERY_EL, reachable_inst_fields]
QED

Theorem reachable_retpc_var:
  retpc_var (reachable_fn fn) x ==> retpc_var fn x
Proof
  rw[retpc_var_def] >>
  `!origin g x. copy_phi_var origin g x ==> g = reachable_fn fn ==>
                copy_phi_var origin fn x`
    suffices_by metis_tac[] >>
  Induct_on `copy_phi_var` >> rw[] >>
  drule reachable_fn_insts_mem >> strip_tac >> gvs[reachable_inst_fields] >>
  metis_tac[copy_phi_var_rules, reachable_inst_fields]
QED

(* The generated code for RET jumps to its last operand, so the function
   theorem can land at the caller's return pc only if that operand is a
   return-PC variable; and a PHI that merges a return-PC variable with an
   ordinary one would read as ra on the ordinary path too.  opaque_use_ok
   restricts where return-PC variables may be used but requires neither.
   RETFMP and DRET become RET with the same last operand (DretDesugar,
   FmpLowering), so they carry the same requirement.

   The first two clauses range over reachable_fn, the code SimplifyCFG
   keeps, so a witness that only dead code supplies doesn't count.  The
   last two range over every instruction and the full closure, the one
   frame_view classifies by: retpc_var is a may-closure and the input need
   not be in SSA form, so they make each return-PC variable written once,
   by a RETPC_PARAM, a copy of one, or a PHI all of whose variables are
   return-PC variables. *)
Definition retpc_shape_ok_def:
  retpc_shape_ok fn <=>
    (!inst. MEM inst (fn_insts (reachable_fn fn)) /\
       MEM inst.inst_opcode [RET; RETFMP; DRET] ==>
       ?front x. inst.inst_operands = front ++ [Var x] /\
                 retpc_var (reachable_fn fn) x) /\
    (!inst x y. MEM inst (fn_insts (reachable_fn fn)) /\
       inst.inst_opcode = PHI /\
       MEM (Var x) inst.inst_operands /\ MEM (Var y) inst.inst_operands /\
       retpc_var (reachable_fn fn) x ==> retpc_var (reachable_fn fn) y) /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
       retpc_var fn x ==>
       inst.inst_opcode = RETPC_PARAM \/
       (inst.inst_opcode = ASSIGN /\ ?y. inst.inst_operands = [Var y] /\
                                          retpc_var fn y) \/
       (inst.inst_opcode = PHI /\
        (?y. MEM (Var y) inst.inst_operands /\ retpc_var fn y) /\
        (!y. MEM (Var y) inst.inst_operands ==> retpc_var fn y))) /\
    (!i j x. MEM i (fn_insts fn) /\ MEM j (fn_insts fn) /\
       MEM x i.inst_outputs /\ MEM x j.inst_outputs /\
       retpc_var fn x ==> i = j)
End

(* Label operands sit only where the codegen expects them: jump targets,
   PHI sources, the INVOKE target, the second operand of LowerDload's
   ADD [ptr; Label "code_end"] (Python's lower_dload.py emits the same), and
   the source operand of the constructor's CODECOPY [dst; Label "runtime_begin"; sz].
   Fixed labels are equations rather than literal patterns, so the case
   doesn't split on the label's characters. *)
Definition label_positions_ok_def:
  label_positions_ok inst <=>
    case (inst.inst_opcode, inst.inst_operands) of
      (JMP, [Label l]) => T
    | (JNZ, [c; Label t; Label f]) => ~is_label_operand c /\ t <> f
    | (PHI, ops) => T
    | (INVOKE, Label l :: args) => EVERY (\op. ~is_label_operand op) args
    | (ADD, [op; Label l]) => l = "code_end" /\ ~is_label_operand op
    | (CODECOPY, [dst; Label l; sz]) =>
        l = "runtime_begin" /\ ~is_label_operand dst /\ ~is_label_operand sz
    | (_, ops) => EVERY (\op. ~is_label_operand op) ops
End

(* The ADD case for an operand that is not a label, as it is left after
   unfolding label_positions_ok on a generic operand. *)
Theorem operand_case_not_label:
  ~is_label_operand op ==>
  ((case op of Lit v => T | Var v => T | Label l => P l) <=> T)
Proof
  Cases_on `op` >> simp[stackPlanTypesTheory.is_label_operand_def]
QED

Definition reserved_label_def:
  reserved_label l <=>
    l = "revert" \/ l = "code_end" \/ l = "runtime_begin" \/
    isPREFIX "return_label_" l \/ isPREFIX "reachable_" l
End

(* All 19 step_inst_base/exec_read0 cases, including raw-only MEMTOP. *)
Definition is_read0_opcode_def:
  is_read0_opcode op <=>
    MEM op [ADDRESS; BASEFEE; BLOBBASEFEE; CALLDATASIZE; CALLER; CALLVALUE;
            CHAINID; CODESIZE; COINBASE; GAS; GASLIMIT; GASPRICE; MEMTOP;
            NUMBER; ORIGIN; PREVRANDAO; RETURNDATASIZE; SELFBALANCE; TIMESTAMP]
End

(* ===== Output shape ===== *)

Definition entry_fn_first_def:
  entry_fn_first ctx <=>
    ?name fn rest. ctx.ctx_entry = SOME name /\
                   ctx.ctx_functions = fn :: rest /\ fn.fn_name = name
End

Definition inst_shape_ok_def:
  inst_shape_ok inst <=>
    ~MEM inst.inst_opcode [DJMP; OFFSET] /\
    (is_read0_opcode inst.inst_opcode ==> inst.inst_operands = []) /\
    (inst.inst_opcode = PHI ==>
       2 <= LENGTH (phi_pairs inst.inst_operands) /\
       ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))) /\
    label_positions_ok inst
End

(* ===== Call success checks ===== *)

(* Label l names a block of bbs from which every path ends in REVERT
   without invoking an internal function: the block ends in REVERT, or in a
   JMP to such a block.  n bounds the chain; LENGTH bbs suffices for every
   chain that visits no block twice. *)
Definition revert_path_def:
  (revert_path bbs 0 l <=> F) /\
  (revert_path bbs (SUC n) l <=>
     EXISTS (\bb. bb.bb_label = l /\ bb.bb_instructions <> [] /\
                  EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                  ((LAST bb.bb_instructions).inst_opcode = REVERT \/
                   (LAST bb.bb_instructions).inst_opcode = JMP /\
                   case (LAST bb.bb_instructions).inst_operands of
                     [Label l'] => revert_path bbs n l'
                   | _ => F))
       bbs)
End

(* inst ends the frame with an exception when every variable in vs holds
   0: it asserts one of them, branches on one into a revert path, or itself
   leads only to REVERT. *)
Definition flag_fails_def:
  flag_fails bbs vs inst <=>
    case (inst.inst_opcode, inst.inst_operands) of
      (ASSERT, [Var x]) => MEM x vs
    | (JNZ, [Var x; Label ok_lbl; Label fail_lbl]) =>
        MEM x vs /\ revert_path bbs (LENGTH bbs) fail_lbl
    | (JMP, [Label l]) => revert_path bbs (LENGTH bbs) l
    | (REVERT, _) => T
    | _ => F
End

(* The instructions after a call reach a failing instruction with no
   INVOKE on the way; vs are the variables that still hold the call's success
   flag (the flag and its ASSIGN copies, less any redefined). An instruction
   that writes state empties vs: in EVM a starved precompile call leaves its
   output buffer unwritten, so a later write could land on the flag's spill
   slot, and only a check with no write since the call counts. REVERT and
   JMP to a revert path don't read vs. *)
Definition flag_path_def:
  (flag_path bbs vs [] <=> F) /\
  (flag_path bbs vs (inst :: rest) <=>
     inst.inst_opcode <> INVOKE /\
     (flag_fails bbs vs inst \/
      flag_path bbs
        (if write_effects inst.inst_opcode <> empty_effects then []
         else
           case (inst.inst_opcode, inst.inst_operands) of
             (ASSIGN, [Var u]) =>
               if MEM u vs then inst.inst_outputs ++ vs
               else FILTER (\x. ~MEM x inst.inst_outputs) vs
           | _ => FILTER (\x. ~MEM x inst.inst_outputs) vs)
        rest))
End

Definition calls_flagged_def:
  (calls_flagged bbs [] <=> T) /\
  (calls_flagged bbs (inst :: rest) <=>
     ((inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) ==>
        case inst.inst_outputs of
          [v] => flag_path bbs [v] rest
        | _ => F) /\
     calls_flagged bbs rest)
End

(* A failed CALL/STATICCALL (success flag 0) never lets the frame finish
   normally: later in the same block, with no INVOKE in between, the flag
   (or a copy) is asserted or branched on into a revert path, or the block
   itself leads only to REVERT.  The lowering puts ASSERT or JNZ right after
   the call; the slack is for what the O1 passes do to that (DFT schedules
   effect-free work before a JNZ, SingleUseExpansion copies a flag with
   several uses, CFGNormalization and SimplifyCFG split or merge the edges
   into the revert block). *)
Definition call_checks_ok_def:
  call_checks_ok fn <=>
    EVERY (\bb. calls_flagged fn.fn_blocks bb.bb_instructions) fn.fn_blocks
End

Theorem MEM_fn_insts_blocks:
  !bbs bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
                MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem calls_flagged_no_calls:
  !insts. EVERY (\inst. ~MEM inst.inst_opcode [CALL; STATICCALL]) insts ==>
          calls_flagged bbs insts
Proof
  Induct >> rw[calls_flagged_def]
QED

Theorem call_checks_ok_no_calls:
  EVERY (\inst. ~MEM inst.inst_opcode [CALL; STATICCALL]) (fn_insts fn) ==>
  call_checks_ok fn
Proof
  rw[call_checks_ok_def, EVERY_MEM] >> irule calls_flagged_no_calls >>
  rw[EVERY_MEM] >>
  `MEM inst (fn_insts fn)`
    by (simp[fn_insts_def] >> metis_tac[MEM_fn_insts_blocks]) >>
  res_tac
QED

Definition fn_shape_ok_def:
  fn_shape_ok fn <=>
    fn_entry_label fn = SOME fn.fn_name /\ opaque_use_ok fn /\
    retpc_shape_ok fn /\ EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks /\
    EVERY inst_shape_ok (fn_insts fn) /\ call_checks_ok fn
End

Definition unit_shape_ok_def:
  unit_shape_ok unit <=>
    entry_fn_first unit.cu_context /\
    entry_fn_no_ret (HD unit.cu_context.ctx_functions) /\
    get_params (HD (HD unit.cu_context.ctx_functions).fn_blocks).bb_instructions = [] /\
    EVERY fn_shape_ok unit.cu_context.ctx_functions
End

(* ===== Additional raw O1-source restrictions ===== *)

Definition raw_opcode_ok_def:
  raw_opcode_ok op <=>
    ~MEM op [PHI; ASSERT_UNREACHABLE; DALLOCA; DRET;
             GETFMP; SETFMP; RETFMP; INITIAL_FMP; BUMP; FMP_PARAM; MEMTOP]
End

Definition internal_termination_ok_def:
  internal_termination_ok ctx <=>
    !fn. MEM fn ctx.ctx_functions /\ fn <> HD ctx.ctx_functions ==>
      EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn)
End

Definition first_block_no_preds_def:
  first_block_no_preds fn <=>
    EVERY (\bb. ~MEM (HD fn.fn_blocks).bb_label (bb_succs bb)) fn.fn_blocks
End

Definition o1_source_unit_ok_def:
  o1_source_unit_ok unit <=>
    unit_shape_ok unit /\
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts fn))
          unit.cu_context.ctx_functions /\
    internal_termination_ok unit.cu_context /\
    EVERY first_block_no_preds unit.cu_context.ctx_functions
End

(* ===== Entry lookup (L4) ===== *)

Theorem entry_fn_first_lookup:
  entry_fn_first ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME efn ==>
  efn = HD ctx.ctx_functions
Proof
  rw[entry_fn_first_def] >> gvs[lookup_function_def, FIND_thm]
QED
