(*
 * SSA Construction Block-Level: Result Equivalence for Loads and Stores
 *
 * TOP-LEVEL:
 *   - mload_result_ssa_equiv
 *   - sload_result_ssa_equiv
 *   - tload_result_ssa_equiv
 *   - mstore_result_ssa_equiv
 *   - sstore_result_ssa_equiv
 *   - tstore_result_ssa_equiv
 *)

Theory ssaBlockResultMem
Ancestors
  ssaBlockResultCore ssaStateEquiv venomSem venomState

(* Helper: MLOAD gives ssa_result_equiv with SAME vm.
 * Follows the same pattern as exec_binop_result_ssa_equiv. *)
Theorem mload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "mload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME addr =>
            case inst.inst_outputs of
              [] => Error "mload requires single output"
            | [out] => OK (update_var out (mload (w2n addr) s_orig) s_orig)
            | out::v6::v7 => Error "mload requires single output")
       | op1::v9::v10 => Error "mload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "mload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME addr =>
            case inst_ssa.inst_outputs of
              [] => Error "mload requires single output"
            | [out] => OK (update_var out (mload (w2n addr) s_ssa) s_ssa)
            | out::v6::v7 => Error "mload requires single output")
       | op1::v9::v10 => Error "mload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  (* Case split on operands - use fs to preserve subgoals *)
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  (* Establish operand equivalence *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  (* Case split on outputs *)
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
  (* Establish mload equality from ssa_state_equiv *)
  `mload (w2n x) s_orig = mload (w2n x) s_ssa` by fs[ssa_state_equiv_def, mload_def] >>
  pop_assum (fn eq => simp_tac std_ss [eq]) >>
  (* Use ssa_state_equiv_update_same_vm *)
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: SLOAD gives ssa_result_equiv with SAME vm. *)
Theorem sload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst.inst_outputs of
              [] => Error "sload requires single output"
            | [out] => OK (update_var out (sload key s_orig) s_orig)
            | out::v6::v7 => Error "sload requires single output")
       | op1::v9::v10 => Error "sload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "sload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst_ssa.inst_outputs of
              [] => Error "sload requires single output"
            | [out] => OK (update_var out (sload key s_ssa) s_ssa)
            | out::v6::v7 => Error "sload requires single output")
       | op1::v9::v10 => Error "sload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
  `sload x s_orig = sload x s_ssa` by fs[ssa_state_equiv_def, sload_def] >>
  pop_assum (fn eq => simp_tac std_ss [eq]) >>
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: TLOAD gives ssa_result_equiv with SAME vm. *)
Theorem tload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "tload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst.inst_outputs of
              [] => Error "tload requires single output"
            | [out] => OK (update_var out (tload key s_orig) s_orig)
            | out::v6::v7 => Error "tload requires single output")
       | op1::v9::v10 => Error "tload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "tload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst_ssa.inst_outputs of
              [] => Error "tload requires single output"
            | [out] => OK (update_var out (tload key s_ssa) s_ssa)
            | out::v6::v7 => Error "tload requires single output")
       | op1::v9::v10 => Error "tload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
  `tload x s_orig = tload x s_ssa` by fs[ssa_state_equiv_def, tload_def] >>
  pop_assum (fn eq => simp_tac std_ss [eq]) >>
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: MSTORE gives ssa_result_equiv with SAME vm.
 * Store operations have no output variable, so vm is unchanged.
 * Note: case structure matches expanded form from gvs[AllCaseEqs()] *)
Theorem mstore_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "mstore requires 2 operands"
       | [op_val] => Error "mstore requires 2 operands"
       | [op_val; op_addr] =>
           (case eval_operand op_val s_orig of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_addr s_orig of
                  NONE => Error "undefined operand"
                | SOME addr => OK (mstore (w2n addr) value s_orig))
       | op_val::op_addr::v12::v13 => Error "mstore requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "mstore requires 2 operands"
       | [op_val] => Error "mstore requires 2 operands"
       | [op_val; op_addr] =>
           (case eval_operand op_val s_ssa of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_addr s_ssa of
                  NONE => Error "undefined operand"
                | SOME addr => OK (mstore (w2n addr) value s_ssa))
       | op_val::op_addr::v12::v13 => Error "mstore requires 2 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule mstore_ssa_equiv >> simp[]
QED

(* Helper: SSTORE gives ssa_result_equiv with SAME vm. *)
Theorem sstore_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sstore requires 2 operands"
       | [op_val] => Error "sstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_orig of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_orig of
                  NONE => Error "undefined operand"
                | SOME key => OK (sstore key value s_orig))
       | op_val::op_key::v12::v13 => Error "sstore requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "sstore requires 2 operands"
       | [op_val] => Error "sstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_ssa of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_ssa of
                  NONE => Error "undefined operand"
                | SOME key => OK (sstore key value s_ssa))
       | op_val::op_key::v12::v13 => Error "sstore requires 2 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule sstore_ssa_equiv >> simp[]
QED

(* Helper: TSTORE gives ssa_result_equiv with SAME vm. *)
Theorem tstore_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "tstore requires 2 operands"
       | [op_val] => Error "tstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_orig of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_orig of
                  NONE => Error "undefined operand"
                | SOME key => OK (tstore key value s_orig))
       | op_val::op_key::v12::v13 => Error "tstore requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "tstore requires 2 operands"
       | [op_val] => Error "tstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_ssa of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_ssa of
                  NONE => Error "undefined operand"
                | SOME key => OK (tstore key value s_ssa))
       | op_val::op_key::v12::v13 => Error "tstore requires 2 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule tstore_ssa_equiv >> simp[]
QED
