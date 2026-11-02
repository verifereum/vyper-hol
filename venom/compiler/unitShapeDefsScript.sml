(*
 * Syntactic unit hypotheses for PLAN §5.8 (not compiler checks).
 * TOP-LEVEL: retpc_var, opaque_use_ok, label_positions_ok,
 *   reserved_label, entry_fn_first, unit_shape_ok, o1_source_unit_ok;
 *   entry_fn_first_lookup (L4).
 * Helpers: copy_phi_var is the least seeded ASSIGN/PHI closure;
 *   retpc_use_ok specifies the opaque return-PC operand positions;
 *   inst_shape_ok / fn_shape_ok collect output-shape restrictions.
 * Raw-only restrictions are deliberately absent from unit_shape_ok.
 *)
Theory unitShapeDefs
Ancestors
  venomCompilerTypes venomInst stackPlanTypes stackPlanGen contextCodegenRel
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

Definition retpc_use_ok_def:
  retpc_use_ok inst x <=>
    inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
    (inst.inst_opcode = RET /\
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

(* Label operands sit only where the codegen expects them: jump targets,
   PHI sources, the INVOKE target, and the second operand of LowerDload's
   ADD [ptr; Label "code_end"] (Python's lower_dload.py emits the same). *)
Definition label_positions_ok_def:
  label_positions_ok inst <=>
    case (inst.inst_opcode, inst.inst_operands) of
      (JMP, [Label l]) => T
    | (JNZ, [c; Label t; Label f]) => ~is_label_operand c
    | (PHI, ops) => T
    | (INVOKE, Label l :: args) => EVERY (\op. ~is_label_operand op) args
    | (ADD, [op; Label l]) => l = "code_end" /\ ~is_label_operand op
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
    l = "revert" \/ l = "code_end" \/
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
    ~MEM inst.inst_opcode
      [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT; DJMP; OFFSET] /\
    (is_read0_opcode inst.inst_opcode ==> inst.inst_operands = []) /\
    label_positions_ok inst
End

Definition fn_shape_ok_def:
  fn_shape_ok fn <=>
    fn_entry_label fn = SOME fn.fn_name /\ opaque_use_ok fn /\
    EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks /\
    EVERY inst_shape_ok (fn_insts fn)
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
    ~MEM op [ASSERT_UNREACHABLE; DLOAD; DLOADBYTES; DALLOCA; DRET;
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
