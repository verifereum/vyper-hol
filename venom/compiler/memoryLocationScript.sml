(*
 * Memory Location Definitions
 *
 * Port of venom/memory_location.py for compiler analyses/passes.
 *)

Theory memoryLocation
Ancestors
  list
  venomState venomInst
  irOps

Datatype:
  allocation = <|
    alloc_inst_id : num;
    alloc_size : num
  |>
End

Definition allocation_of_inst_def:
  allocation_of_inst inst =
    if inst.inst_opcode IN {ALLOCA; PALLOCA} then
      case inst.inst_operands of
        (Lit w :: _) => SOME <| alloc_inst_id := inst.inst_id;
                               alloc_size := w2n w |>
      | _ => NONE
    else NONE
End

Datatype:
  memory_location = <|
    ml_offset : num option;
    ml_size : num option;
    ml_alloca : allocation option;
    ml_volatile : bool
  |>
End

Definition memory_location_empty_def:
  memory_location_empty =
    <| ml_offset := SOME 0; ml_size := SOME 0; ml_alloca := NONE; ml_volatile := F |>
End

Definition memory_location_undefined_def:
  memory_location_undefined =
    <| ml_offset := NONE; ml_size := NONE; ml_alloca := NONE; ml_volatile := F |>
End

Definition memory_location_is_empty_def:
  memory_location_is_empty loc <=> loc.ml_size = SOME 0
End

Definition memory_location_is_offset_fixed_def:
  memory_location_is_offset_fixed loc <=> IS_SOME loc.ml_offset
End

Definition memory_location_is_size_fixed_def:
  memory_location_is_size_fixed loc <=> IS_SOME loc.ml_size
End

Definition memory_location_is_fixed_def:
  memory_location_is_fixed loc <=>
    memory_location_is_offset_fixed loc /\ memory_location_is_size_fixed loc
End

Definition memory_location_is_concrete_def:
  memory_location_is_concrete loc <=> loc.ml_alloca = NONE
End

Definition memory_location_mk_volatile_def:
  memory_location_mk_volatile loc = loc with ml_volatile := T
End

Definition memory_location_completely_contains_def:
  memory_location_completely_contains loc1 loc2 <=>
    if memory_location_is_empty loc2 then T else
    if ~memory_location_is_fixed loc1 then F else
    if ~memory_location_is_fixed loc2 then F else
    if memory_location_is_concrete loc1 <> memory_location_is_concrete loc2 then F else
    if loc1.ml_alloca <> loc2.ml_alloca then F else
    case (loc1.ml_offset, loc1.ml_size, loc2.ml_offset, loc2.ml_size) of
      (SOME o1, SOME s1, SOME o2, SOME s2) =>
        let end1 = o1 + s1 in
        let end2 = o2 + s2 in
        o1 <= o2 /\ end1 >= end2
    | _ => F
End

Definition memory_location_may_overlap_def:
  memory_location_may_overlap loc1 loc2 <=>
    if memory_location_is_empty loc1 \/ memory_location_is_empty loc2 then F else
    if memory_location_is_concrete loc1 <> memory_location_is_concrete loc2 then T else
    if IS_SOME loc1.ml_alloca /\ IS_SOME loc2.ml_alloca /\ loc1.ml_alloca <> loc2.ml_alloca then F else
    case (loc1.ml_offset, loc1.ml_size, loc2.ml_offset, loc2.ml_size) of
      (SOME o1, SOME s1, SOME o2, SOME s2) =>
        let end1 = o1 + s1 in
        let end2 = o2 + s2 in
        ~(end1 <= o2 \/ end2 <= o1)
    | (SOME o1, SOME s1, SOME o2, NONE) => ~(o1 + s1 <= o2)
    | (SOME o1, NONE, SOME o2, SOME s2) => ~(o2 + s2 <= o1)
    | (NONE, _, _, _) => T
    | (_, _, NONE, _) => T
End

Datatype:
  inst_access_ops = <|
    ia_ofst : operand option;
    ia_size : operand option;
    ia_max_size : operand option
  |>
End

Definition inst_access_ops_def:
  inst_access_ops ofst size max_size =
    <| ia_ofst := ofst; ia_size := size; ia_max_size := if IS_SOME max_size then max_size else size |>
End

Definition memory_write_ops_def:
  memory_write_ops inst =
    case inst.inst_opcode of
      MSTORE =>
        (case inst.inst_operands of
           _::dst::_ => inst_access_ops (SOME dst) (SOME (Lit 32w)) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | MCOPY =>
        (case inst.inst_operands of
           sz::_::dst::_ => inst_access_ops (SOME dst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | CALLDATACOPY =>
        (case inst.inst_operands of
           sz::_::dst::_ => inst_access_ops (SOME dst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | DLOADBYTES =>
        (case inst.inst_operands of
           sz::_::dst::_ => inst_access_ops (SOME dst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | CODECOPY =>
        (case inst.inst_operands of
           sz::_::dst::_ => inst_access_ops (SOME dst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | RETURNDATACOPY =>
        (case inst.inst_operands of
           sz::_::dst::_ => inst_access_ops (SOME dst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | CALL =>
        (case inst.inst_operands of
           max_size::dst::_ => inst_access_ops (SOME dst) NONE (SOME max_size)
         | _ => inst_access_ops NONE NONE NONE)
    | DELEGATECALL =>
        (case inst.inst_operands of
           max_size::dst::_ => inst_access_ops (SOME dst) NONE (SOME max_size)
         | _ => inst_access_ops NONE NONE NONE)
    | STATICCALL =>
        (case inst.inst_operands of
           max_size::dst::_ => inst_access_ops (SOME dst) NONE (SOME max_size)
         | _ => inst_access_ops NONE NONE NONE)
    | EXTCODECOPY =>
        (case inst.inst_operands of
           sz::_::dst::_ => inst_access_ops (SOME dst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | _ => inst_access_ops NONE NONE NONE
End

Definition get_memory_write_op_def:
  get_memory_write_op inst = (memory_write_ops inst).ia_ofst
End

Definition get_write_size_def:
  get_write_size inst = (memory_write_ops inst).ia_size
End

Definition get_write_max_size_def:
  get_write_max_size inst = (memory_write_ops inst).ia_max_size
End

Definition memory_read_ops_def:
  memory_read_ops inst =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           ofst::_ => inst_access_ops (SOME ofst) (SOME (Lit 32w)) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | MCOPY =>
        (case inst.inst_operands of
           sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | CALL =>
        (case inst.inst_operands of
           _::_::sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | DELEGATECALL =>
        (case inst.inst_operands of
           _::_::sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | STATICCALL =>
        (case inst.inst_operands of
           _::_::sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | RETURN =>
        (case inst.inst_operands of
           sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | CREATE =>
        (case inst.inst_operands of
           sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | CREATE2 =>
        (case inst.inst_operands of
           _::sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | SHA3 =>
        (case inst.inst_operands of
           sz::ofst::_ => inst_access_ops (SOME ofst) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | LOG =>
        (case REVERSE inst.inst_operands of
           src::sz::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | REVERT =>
        (case inst.inst_operands of
           sz::src::_ => inst_access_ops (SOME src) (SOME sz) NONE
         | _ => inst_access_ops NONE NONE NONE)
    | _ => inst_access_ops NONE NONE NONE
End

Definition get_memory_read_op_def:
  get_memory_read_op inst = (memory_read_ops inst).ia_ofst
End

Definition get_read_size_def:
  get_read_size inst = (memory_read_ops inst).ia_size
End

Definition update_write_location_def:
  update_write_location inst new_op =
    case inst.inst_opcode of
      MSTORE =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | MCOPY =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | CALLDATACOPY =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | DLOADBYTES =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | CODECOPY =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | RETURNDATACOPY =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | CALL =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | DELEGATECALL =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | STATICCALL =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | EXTCODECOPY =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | _ => inst
End

Definition update_read_location_def:
  update_read_location inst new_op =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           a::rest => inst with inst_operands := new_op::rest
         | _ => inst)
    | MCOPY =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | CALL =>
        (case inst.inst_operands of
           a::b::c::d::rest => inst with inst_operands := a::b::c::new_op::rest
         | _ => inst)
    | DELEGATECALL =>
        (case inst.inst_operands of
           a::b::c::d::rest => inst with inst_operands := a::b::c::new_op::rest
         | _ => inst)
    | STATICCALL =>
        (case inst.inst_operands of
           a::b::c::d::rest => inst with inst_operands := a::b::c::new_op::rest
         | _ => inst)
    | RETURN =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | CREATE =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | CREATE2 =>
        (case inst.inst_operands of
           a::b::c::rest => inst with inst_operands := a::b::new_op::rest
         | _ => inst)
    | SHA3 =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | LOG =>
        let ops = inst.inst_operands in
        if ops = [] then inst else
          let rev = REVERSE ops in
          (case rev of
             src::rest =>
               inst with inst_operands := REVERSE (new_op::rest)
           | _ => inst)
    | REVERT =>
        (case inst.inst_operands of
           a::b::rest => inst with inst_operands := a::new_op::rest
         | _ => inst)
    | _ => inst
End

val _ = export_theory();
