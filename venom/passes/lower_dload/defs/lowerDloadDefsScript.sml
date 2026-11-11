(*
 * Lower DLOAD Pass — Definitions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 * Ports vyper/venom/passes/lower_dload.py to HOL4.
 *
 * Lowers dload and dloadbytes instructions to their EVM equivalents:
 *   dload ptr        -> alloca 32; add ptr code_end; codecopy dst add_out 32; mload dst
 *   dloadbytes dst src size -> add src code_end; codecopy dst code_ptr size
 *
 * Matches Python: emits ADD [ptr; Label "code_end"]. Labels resolve via
 * vs_labels (eval_operand handles Label operands). Correctness requires
 * code_layout_valid: vs_labels "code_end" = code/data boundary.
 *
 * No analysis needed - pure per-instruction expansion (1:N).
 *
 * CONFIGURED EXECUTABLE API:
 *   lower_dload_configured_with_supply - unit transform plus final supply
 *   lower_dload_configured             - transformed unit projection
 *
 *   code_layout_valid     - code_end marks the code/data boundary
 *
 * Source: vyper/venom/passes/lower_dload.py
 *)

Theory lowerDloadDefs
Ancestors
  passTransform venomExecSemantics venomInst irSupply
(* ===== Supply-aware configured transform ===== *)

(* Supply-threaded implementation.  The only configured entry points are the
   compilation-unit wrappers lower_dload_configured_with_supply and
   lower_dload_configured below: they initialize one supply from the whole unit
   and thread it across every function.  Future pipeline composition must call
   a configured unit wrapper once, never invoke this function-level API
   independently for each function. *)
Definition lower_dload_inst_supply_def:
  lower_dload_inst_supply s inst =
    if inst.inst_opcode = DLOAD then
      case (inst.inst_operands, inst.inst_outputs) of
        ([ptr_op], [out]) =>
          (case fresh_ir_var s of (alloca_v,s1) =>
           case fresh_ir_var s1 of (add_v,s2) =>
           case fresh_inst_id s2 of (alloca_id,s3) =>
           case fresh_inst_id s3 of (add_id,s4) =>
           case fresh_inst_id s4 of (copy_id,s5) =>
           case fresh_inst_id s5 of (load_id,s6) =>
             ([<| inst_id := alloca_id; inst_opcode := ALLOCA;
                  inst_operands := [Lit 32w]; inst_outputs := [alloca_v] |>;
               <| inst_id := add_id; inst_opcode := ADD;
                  inst_operands := [ptr_op; Label "code_end"];
                  inst_outputs := [add_v] |>;
               <| inst_id := copy_id; inst_opcode := CODECOPY;
                  inst_operands := [Var alloca_v; Var add_v; Lit 32w];
                  inst_outputs := [] |>;
               <| inst_id := load_id; inst_opcode := MLOAD;
                  inst_operands := [Var alloca_v]; inst_outputs := [out] |>],s6))
      | _ => ([inst],s)
    else if inst.inst_opcode = DLOADBYTES then
      case inst.inst_operands of
        [dst_op; src_op; size_op] =>
          (case fresh_ir_var s of (add_v,s1) =>
           case fresh_inst_id s1 of (add_id,s2) =>
           case fresh_inst_id s2 of (copy_id,s3) =>
             ([<| inst_id := add_id; inst_opcode := ADD;
                  inst_operands := [src_op; Label "code_end"];
                  inst_outputs := [add_v] |>;
               <| inst_id := copy_id; inst_opcode := CODECOPY;
                  inst_operands := [dst_op; Var add_v; size_op];
                  inst_outputs := [] |>],s3))
      | _ => ([inst],s)
    else ([inst],s)
End

Definition lower_dload_insts_supply_def:
  lower_dload_insts_supply s [] = ([],s) /\
  lower_dload_insts_supply s (inst::insts) =
    case lower_dload_inst_supply s inst of (out,s1) =>
    case lower_dload_insts_supply s1 insts of (outs,s2) =>
      (out ++ outs,s2)
End

Definition lower_dload_block_supply_def:
  lower_dload_block_supply s bb =
    case lower_dload_insts_supply s bb.bb_instructions of (insts,s1) =>
      (bb with bb_instructions := insts,s1)
End

Definition lower_dload_blocks_supply_def:
  lower_dload_blocks_supply s [] = ([],s) /\
  lower_dload_blocks_supply s (bb::bbs) =
    case lower_dload_block_supply s bb of (bb',s1) =>
    case lower_dload_blocks_supply s1 bbs of (bbs',s2) =>
      (bb'::bbs',s2)
End

Definition lower_dload_invalidates_layout_def:
  lower_dload_invalidates_layout fn <=>
    ?bb inst ptr out.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = DLOAD /\
      inst.inst_operands = [ptr] /\ inst.inst_outputs = [out]
End

Definition lower_dload_function_supply_def:
  lower_dload_function_supply s fn =
    case lower_dload_blocks_supply s fn.fn_blocks of (bbs,s1) =>
      (fn with <| fn_blocks := bbs;
                  fn_eom := if lower_dload_invalidates_layout fn
                            then NONE else fn.fn_eom |>,s1)
End

Definition lower_dload_functions_supply_def:
  lower_dload_functions_supply s [] = ([],s) /\
  lower_dload_functions_supply s (fn::fns) =
    case lower_dload_function_supply s fn of (fn',s1) =>
    case lower_dload_functions_supply s1 fns of (fns',s2) =>
      (fn'::fns',s2)
End

Definition lower_dload_context_supply_def:
  lower_dload_context_supply s ctx =
    case lower_dload_functions_supply s ctx.ctx_functions of (fns,s1) =>
      (ctx with ctx_functions := fns,s1)
End

Definition lower_dload_unit_supply_def:
  lower_dload_unit_supply s unit =
    case lower_dload_context_supply s unit.cu_context of (ctx,s1) =>
      (unit with cu_context := ctx,s1)
End

Definition lower_dload_configured_with_supply_def:
  lower_dload_configured_with_supply unit =
    lower_dload_unit_supply (init_ir_supply unit) unit
End

Definition lower_dload_configured_def:
  lower_dload_configured unit = FST (lower_dload_configured_with_supply unit)
End

(* ===== Code Layout Precondition ===== *)

(* Precondition for lower_dload correctness:
   1. vs_data_section is a suffix of vs_code
   2. vs_labels maps "code_end" to the boundary between bytecode and data

   Discharged by codegen: the assembler produces bytecode ++ data_section_bytes
   and sets code_end = LENGTH bytecode in the label map. *)
Definition code_layout_valid_def:
  code_layout_valid s <=>
    (?prefix. s.vs_code = prefix ++ s.vs_data_section) /\
    FLOOKUP s.vs_labels "code_end" =
      SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
    LENGTH s.vs_code <= dimword(:256) DIV 2
End

(* The expansion computes the code offset of a DLOAD/DLOADBYTES source
   offset as ADD [off; Label "code_end"], in word arithmetic, so it reads
   the bytes DLOAD reads only when the sum does not wrap: when the offset
   plus the code prefix length (code_layout_valid's "code_end") fits in a
   word.  Stated per reachable state (mem_inv), since constructor-argument
   offsets are computed at run time. *)
Definition dload_offset_ok_def:
  dload_offset_ok (ctx:venom_context) (fn:ir_function) inst s <=>
    !op off.
      ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [op]) \/
       (inst.inst_opcode = DLOADBYTES /\
        ?dst n. inst.inst_operands = [dst; op; n])) /\
      eval_operand op s = SOME off ==>
      w2n off + (LENGTH s.vs_code - LENGTH s.vs_data_section) <
        dimword (:256)
End

(* The number of DLOAD instructions in a context. *)
Definition ctx_dload_count_def:
  ctx_dload_count (ctx:venom_context) =
    SUM (MAP (\fn. LENGTH (FILTER (\inst. inst.inst_opcode = DLOAD)
                                  (fn_insts fn)))
             ctx.ctx_functions)
End

(* The expansion gives each DLOAD a fresh 32-byte ALLOCA site, and a frame
   allocates each site once, so the output's alloca frontier runs at most
   32 bytes per DLOAD in the context ahead of the input's.  This bound keeps
   that frontier below 2^256, where exec_alloca's offsets would wrap onto
   live sites.  Stated per reachable state (mem_inv), like the frontier
   bound in raw_mem_ok. *)
Definition dload_headroom_ok_def:
  dload_headroom_ok (ctx:venom_context) (fn:ir_function) inst s <=>
    s.vs_alloca_next + 32 * ctx_dload_count ctx < dimword (:256)
End
