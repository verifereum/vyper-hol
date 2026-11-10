(* Concrete checks of the compiler: allocation limits, bytestring
   conversions, the checker's conversion domain, concat buffers, shared callee memory, and a deployed
   immutable read through the source semantics, and a memory struct field
   named msg.data sliced by MCOPY. *)
Theory compilerLoweringTest
Ancestors
  evalCompilerSubsetState compileVyper vyperCompiler exprLowering context
  concretizeMemLocDefs vyperInterpreter alist integer_word
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib vyperCheckContractLib
  jsonASTLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../bytecode/immutables/oracle", "../bytecode/conversions/checker-oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, i2w_def])

(* ===== Allocation limits ===== *)

(* The external return buffer at Python's allocation limit.  Python's
   Context.allocate_buffer raises MemoryAllocationException for 2**64 bytes
   or more, and _lower_external_return allocates the ABI return buffer there
   on each valued return; the runtime lowering rejects the same programs.
   It does the same for a function's locals, as Context.new_variable
   allocates each, and for its parameters, which an external function
   decodes into such a variable, for its return type, as a caller stages
   an internal call's result in a temporary, and for the staging buffer of
   a tuple assignment from a memory view, and for a log's data and ABI
   buffers. *)

(* @external
   def f(x: Bytes[1]) -> Bytes[2**64]:
       return x
   Python: MemoryAllocationException for the return buffer of 64 + 2**64
   bytes, the only allocation over the limit.  (A static type of 2**64 bytes
   is a fixed array of 2**59 words, whose decoding info the evaluator would
   unroll.) *)
Definition allocation_limit_return_program_def:
  allocation_limit_return_program =
    [FunctionDecl External Nonpayable F F "f"
       [("x", BaseT (BytesT (Dynamic 1)))]
       ([] : expr list) (BaseT (BytesT (Dynamic (2 ** 64))))
       [Return (SOME (Name (BaseT (BytesT (Dynamic (2 ** 64)))) "x"))]]
End

val allocation_limit_return_eval =
  EVAL ``lower_vyper_runtime_unit allocation_limit_return_program rpolicy``

Theorem allocation_limit_return_rejected:
  !rpolicy.
    lower_vyper_runtime_unit allocation_limit_return_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_return_eval
QED

val allocation_limit_raise_eval =
  EVAL ``external_return_buffer_ok
           (package_external_fn [] F (K 0)
              (Nonpayable, F, F, "f", [], ([] : expr list),
               BaseT (BytesT (Dynamic (2 ** 64))),
               [Raise RaiseBare]))``

(* @external
   def f() -> Bytes[2**64]:
       raise
   Python compiles it: no valued return, so no return buffer. *)
Theorem allocation_limit_raise_return_buffer_ok:
  external_return_buffer_ok
    (package_external_fn [] F (K 0)
       (Nonpayable, F, F, "f", [], ([] : expr list),
        BaseT (BytesT (Dynamic (2 ** 64))), [Raise RaiseBare]))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_raise_eval)
QED

(* The return buffer of Bytes[n] is 64 + ceil32(n) bytes: the tuple head,
   the length word and the data.  It fits for n = 2**64 - 96 and reaches the
   limit for n = 2**64 - 95.
   @external
   def f() -> Bytes[n]:
       return empty(Bytes[n]) *)
Definition allocation_limit_boundary_fn_def:
  allocation_limit_boundary_fn n =
    package_external_fn [] F (K 0)
      (Nonpayable, F, F, "f", [], ([] : expr list),
       BaseT (BytesT (Dynamic n)),
       [Return (SOME (TypeBuiltin (BaseT (BytesT (Dynamic n))) Empty
                       (BaseT (BytesT (Dynamic n))) []))])
End

val allocation_limit_boundary_ok_eval =
  EVAL ``external_return_buffer_ok
           (allocation_limit_boundary_fn (2 ** 64 - 96))``

Theorem allocation_limit_boundary_ok:
  external_return_buffer_ok (allocation_limit_boundary_fn (2 ** 64 - 96))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_boundary_ok_eval)
QED

val allocation_limit_boundary_rejected_eval =
  EVAL ``external_return_buffer_ok
           (allocation_limit_boundary_fn (2 ** 64 - 95))``

Theorem allocation_limit_boundary_rejected:
  ¬external_return_buffer_ok (allocation_limit_boundary_fn (2 ** 64 - 95))
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_boundary_rejected_eval)
QED

(* @external
   def f():
       y: Bytes[2**64] = b""
   Python: MemoryAllocationException for y's 32 + 2**64 bytes. *)
Definition allocation_limit_local_program_def:
  allocation_limit_local_program =
    [FunctionDecl External Nonpayable F F "f" [] ([] : expr list) NoneT
       [AnnAssign "y" (BaseT (BytesT (Dynamic (2 ** 64))))
          (Literal (BaseT (BytesT (Dynamic 0))) (BytesL []))]]
End

val allocation_limit_local_eval =
  EVAL ``lower_vyper_runtime_unit allocation_limit_local_program rpolicy``

Theorem allocation_limit_local_rejected:
  !rpolicy.
    lower_vyper_runtime_unit allocation_limit_local_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_local_eval
QED

(* A local of type Bytes[n] takes 32 + ceil32(n) bytes: it fits for
   n = 2**64 - 64 and reaches the limit for n = 2**64 - 63.
   def f():
       y: Bytes[n] = b"" *)
Definition allocation_limit_local_fn_def:
  allocation_limit_local_fn n =
    (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list, NoneT,
     [AnnAssign "y" (BaseT (BytesT (Dynamic n)))
        (Literal (BaseT (BytesT (Dynamic 0))) (BytesL []))])
End

val allocation_limit_local_boundary_ok_eval =
  EVAL ``fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 64))``

Theorem allocation_limit_local_boundary_ok:
  fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 64))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_local_boundary_ok_eval)
QED

val allocation_limit_local_boundary_rejected_eval =
  EVAL ``fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 63))``

Theorem allocation_limit_local_boundary_rejected:
  ¬fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 63))
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_local_boundary_rejected_eval)
QED

(* @external
   def f(x: Bytes[2**256-1]):
       pass
   Python: MemoryAllocationException for x's 32 + 2**256 bytes, which a
   word-sized ALLOCA would wrap to 32. *)
Definition allocation_limit_param_program_def:
  allocation_limit_param_program =
    [FunctionDecl External Nonpayable F F "f"
       [("x", BaseT (BytesT (Dynamic (2 ** 256 - 1))))]
       ([] : expr list) NoneT [Pass]]
End

val allocation_limit_param_eval =
  EVAL ``lower_vyper_runtime_unit allocation_limit_param_program rpolicy``

Theorem allocation_limit_param_rejected:
  !rpolicy.
    lower_vyper_runtime_unit allocation_limit_param_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_param_eval
QED

(* @internal
   def f() -> Bytes[2**64]:
       ...
   Python: MemoryAllocationException at each call site, which stages the
   result in new_temporary_value(Bytes[2**64]). *)
val allocation_limit_internal_return_rejected_eval =
  EVAL ``fn_allocs_ok []
           (Nonpayable, F, F, "f", [] : (string # type) list,
            [] : expr list, BaseT (BytesT (Dynamic (2 ** 64))), [Pass])``

Theorem allocation_limit_internal_return_rejected:
  ¬fn_allocs_ok []
     (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list,
      BaseT (BytesT (Dynamic (2 ** 64))), [Pass])
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_internal_return_rejected_eval)
QED

(* a, b = x
   where x is a memory tuple (Bytes[2**64 - 64], uint256): Python stages x
   (_lower_tuple_unpack) in new_temporary_value of
   (32 + 2**64 - 64) + 32 = 2**64 bytes. *)
val allocation_limit_tuple_stage_rejected_eval =
  EVAL ``fn_allocs_ok []
           (Nonpayable, F, F, "f", [] : (string # type) list,
            [] : expr list, NoneT,
            [Assign (TupleTarget [BaseTarget (NameTarget "a");
                                  BaseTarget (NameTarget "b")])
               (Name (TupleT [BaseT (BytesT (Dynamic (2 ** 64 - 64)));
                              BaseT (UintT 256)]) "x")])``

Theorem allocation_limit_tuple_stage_rejected:
  ¬fn_allocs_ok []
     (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list, NoneT,
      [Assign (TupleTarget [BaseTarget (NameTarget "a");
                            BaseTarget (NameTarget "b")])
         (Name (TupleT [BaseT (BytesT (Dynamic (2 ** 64 - 64)));
                        BaseT (UintT 256)]) "x")])
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_tuple_stage_rejected_eval)
QED

(* The same with Bytes[2**64 - 96]: a buffer of 2**64 - 32 bytes is allowed. *)
val allocation_limit_tuple_stage_accepted_eval =
  EVAL ``fn_allocs_ok []
           (Nonpayable, F, F, "f", [] : (string # type) list,
            [] : expr list, NoneT,
            [Assign (TupleTarget [BaseTarget (NameTarget "a");
                                  BaseTarget (NameTarget "b")])
               (Name (TupleT [BaseT (BytesT (Dynamic (2 ** 64 - 96)));
                              BaseT (UintT 256)]) "x")])``

Theorem allocation_limit_tuple_stage_accepted:
  fn_allocs_ok []
    (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list, NoneT,
     [Assign (TupleTarget [BaseTarget (NameTarget "a");
                           BaseTarget (NameTarget "b")])
        (Name (TupleT [BaseT (BytesT (Dynamic (2 ** 64 - 96)));
                       BaseT (UintT 256)]) "x")])
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_tuple_stage_accepted_eval)
QED

(* event Big:
       x: Bytes[n]
       y: Bytes[n]
   def f(x: Bytes[n], y: Bytes[n]):
       log Big(x, y)
   Python's lower_Log allocates the data buffer, 2 * (32 + ceil32(n))
   bytes, and the ABI buffer, 64 more.  n = 2**63 - 32 makes the data
   buffer 2**64 bytes, while each argument fits. *)
Definition allocation_limit_log_tops_def:
  allocation_limit_log_tops n =
    [EventDecl "Big"
       [(("x", BaseT (BytesT (Dynamic n))), F);
        (("y", BaseT (BytesT (Dynamic n))), F)]]
End

Definition allocation_limit_log_fn_def:
  allocation_limit_log_fn n =
    (Nonpayable, F, F, "f",
     [("x", BaseT (BytesT (Dynamic n))); ("y", BaseT (BytesT (Dynamic n)))],
     [] : expr list, NoneT,
     [Log (NONE, "Big")
        [Name (BaseT (BytesT (Dynamic n))) "x";
         Name (BaseT (BytesT (Dynamic n))) "y"]])
End

val allocation_limit_log_rejected_eval =
  EVAL ``fn_allocs_ok (allocation_limit_log_tops (2 ** 63 - 32))
           (allocation_limit_log_fn (2 ** 63 - 32))``

Theorem allocation_limit_log_rejected:
  ¬fn_allocs_ok (allocation_limit_log_tops (2 ** 63 - 32))
     (allocation_limit_log_fn (2 ** 63 - 32))
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_log_rejected_eval)
QED

(* n = 2**63 - 64: the data buffer takes 2**64 - 64 bytes and fits; only
   the ABI buffer, 2**64 bytes, reaches the limit. *)
val allocation_limit_log_abi_rejected_eval =
  EVAL ``fn_allocs_ok (allocation_limit_log_tops (2 ** 63 - 64))
           (allocation_limit_log_fn (2 ** 63 - 64))``

Theorem allocation_limit_log_abi_rejected:
  ¬fn_allocs_ok (allocation_limit_log_tops (2 ** 63 - 64))
     (allocation_limit_log_fn (2 ** 63 - 64))
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_log_abi_rejected_eval)
QED

(* n = 2**63 - 96: the ABI buffer, the larger, takes 2**64 - 64 bytes. *)
val allocation_limit_log_accepted_eval =
  EVAL ``fn_allocs_ok (allocation_limit_log_tops (2 ** 63 - 96))
           (allocation_limit_log_fn (2 ** 63 - 96))``

Theorem allocation_limit_log_accepted:
  fn_allocs_ok (allocation_limit_log_tops (2 ** 63 - 96))
    (allocation_limit_log_fn (2 ** 63 - 96))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_log_accepted_eval)
QED

(* ===== Bytestring conversions ===== *)

(* A bytestring convert whose source buffer is smaller than the target's
   copies the value into a new buffer of the target's size, after the
   argument's own code.  Mirrors Python: convert.py
   _bytestring_convert_value (vyperlang/vyper#5338). *)
(* The instructions convert(e, Bytes[40]) emits after those of e itself,
   and whether they are exactly an ALLOCA of alloc_n bytes, returned as the
   result, and an MCOPY of copy_n bytes from e's operand into it. *)
Definition widen_tail_def:
  widen_tail src_ty e =
    let cenv = build_compile_env [] External Nonpayable "f"
                 [("x", src_ty)] NoneT [] F in
    let st0 = initial_compile_state "entry" in
    let tgt = BaseT (BytesT (Dynamic 40)) in
    let (v, st1) = lower_value compile_expr cenv (expr_type e) e st0 in
    let (vv, st2) = compile_expr cenv tgt (TypeBuiltin tgt Convert tgt [e]) st0 in
    (v, vv_operand vv, st2.cs_blocks = st1.cs_blocks,
     TAKE (LENGTH st1.cs_current_insts) st2.cs_current_insts =
       st1.cs_current_insts,
     DROP (LENGTH st1.cs_current_insts) st2.cs_current_insts)
End

Definition widen_copies_def:
  widen_copies src_ty e alloc_n copy_n =
    case widen_tail src_ty e of
      (v, res, same_blocks, same_prefix, [a; c]) =>
        same_blocks /\ same_prefix /\
        a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit (n2w alloc_n)] /\
        a.inst_outputs <> [] /\ res = Var (HD a.inst_outputs) /\
        c.inst_opcode = MCOPY /\
        c.inst_operands = [res; v; Lit (n2w copy_n)]
    | _ => F
End

(* def f(x: String[2]) -> ...: convert(x, Bytes[40])
   Buffers: Bytes[40] is 32 + 64 = 96 bytes, String[2] is 32 + 32 = 64. *)
Theorem convert_widen_name_copies:
  widen_copies (BaseT (StringT 2)) (Name (BaseT (StringT 2)) "x") 96 64
Proof
  EVAL_TAC
QED

(* convert("ab", Bytes[40]) with the literal typed String[40]: the copy
   size follows the literal's own length, as Python's lowered in_t does. *)
Theorem convert_widen_literal_copies:
  widen_copies (BaseT (StringT 2))
    (Literal (BaseT (StringT 40)) (StringL "ab")) 96 64
Proof
  EVAL_TAC
QED

(* def f(x: String[40]) -> ...: convert(x, Bytes[40]) keeps the pointer. *)
Theorem convert_same_size_no_copy:
  case widen_tail (BaseT (StringT 40)) (Name (BaseT (StringT 40)) "x") of
    (v, res, same_blocks, same_prefix, tail) =>
      same_blocks /\ same_prefix /\
      EVERY (\i. i.inst_opcode <> ALLOCA /\ i.inst_opcode <> MCOPY) tail
Proof
  EVAL_TAC
QED

(* ===== Builtins ===== *)

(* concat's buffer holds the length word and each argument's maximum length. *)
Theorem concat_fixed_word_allocation:
  concat_alloc_size [BaseT (BytesT (Fixed 1)); BaseT (BytesT (Fixed 1))] = 65 /\
  concat_alloc_size [BaseT (BytesT (Dynamic 10)); BaseT (BytesT (Fixed 4))] = 74
Proof
  EVAL_TAC
QED

(* ===== Internal frames ===== *)

(* Metadata order is not ordered-set order. Both sets below contain the
   shared callee allocations of a diamond of internal calls; the analysis
   input must normalize that order. *)
Theorem diamond_shared_import_intersection:
  sinter alloc_to
    (incr_ssort alloc_to [Allocation 21; Allocation 64; Allocation 66; Allocation 67; Allocation 41; Allocation 43])
    (incr_ssort alloc_to [Allocation 17; Allocation 21; Allocation 22; Allocation 52; Allocation 54; Allocation 55; Allocation 41; Allocation 43]) =
    [Allocation 21; Allocation 41; Allocation 43]
Proof
  EVAL_TAC
QED

(* ===== Immutables ===== *)

(* The source of bytecode/immutables/oracle/p23_imm_uint256, which sets a
   uint256 immutable to 42 in its constructor and returns it from get(). *)
Definition p23_source_deployment_def:
  p23_source_deployment =
    load_contract NONE [] initial_machine_state
      (empty_call_txn with
        <|target := 2w; sender := 1w; function_name := "__init__"|>)
      [(NONE, ^(memoryStoreWitnessLib.program "../bytecode/immutables/oracle" "p23_imm_uint256"))] []
End

Theorem p23_source_deploy_get_42:
  ISL p23_source_deployment /\
  FST (call_external NONE [] (FST (OUTL p23_source_deployment))
    (empty_call_txn with
      <|target := 2w; sender := 1w; function_name := "get"|>)) = INL (IntV 42)
Proof
  EVAL_TAC
QED

(* ===== The checker's conversion domain ===== *)

(* The checker on Python's exported ASTs of conversions outside Vyper's input
   sets: it rejects those whose HOL lowering and source semantics disagree,
   and accepts those where they agree. *)
fun check_conversion expected name = let
  val path = "../bytecode/conversions/checker-oracle/" ^ name ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  fun check in_deploy = let
    val term = vyperCheckContractLib.mk_check_contract
      {in_deploy = in_deploy, address = #address input,
       modules = #modules input, layouts = #layouts input}
    val result = rhs (concl (vyperCheckContractLib.check_contract_conv term))
    val matches = if expected then optionSyntax.is_some result
                  else optionSyntax.is_none result
  in if matches then ()
     else raise Fail (name ^ ": unexpected checker result in deployment mode " ^
                      Bool.toString in_deploy ^ ": " ^ term_to_string result)
  end
in List.app check [false, true] end

val () = List.app (check_conversion false)
  ["u256_to_b4", "bys33_to_bool", "bys64_to_u256", "bys8_to_b4",
   "str8_to_b4", "u256_to_bys16", "b4_to_bys2",
   "b4_to_bys", "b4_to_str", "u256_to_bys"]
val () = List.app (check_conversion true)
  ["i8_to_addr", "i256_to_addr", "lit_300_to_u8", "lit_neg_to_u256",
   "lit_bys_narrow"]

(* The HOL typed AST permits a struct variable named msg.  Its data field
   is memory, even though its syntax also satisfies is_msg_data.  Real
   transaction calldata uses the separate CalldataSlice constructor. *)
Definition slice_struct_field_expr_def:
  slice_struct_field_expr =
    Builtin (BaseT (BytesT (Dynamic 40))) (Slice 40)
      [Attribute (BaseT (BytesT (Dynamic 40)))
         (Name (StructT (NONE, "S")) "msg") "data";
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 1)]
End

Definition slice_struct_field_insts_def:
  slice_struct_field_insts =
    let cenv = build_compile_env
      [StructDecl "S" [("data", BaseT (BytesT (Dynamic 40)))]]
      External Pure "entry" [("msg", StructT (NONE, "S"))]
      (BaseT (BytesT (Dynamic 40)))
      [Return (SOME slice_struct_field_expr)] F in
    (SND (compile_expr cenv (BaseT (BytesT (Dynamic 40)))
      slice_struct_field_expr
      (vyperCompiler$initial_compile_state "entry"))).cs_current_insts
End

Theorem slice_struct_field_copies_memory:
  EXISTS (\i. i.inst_opcode = MCOPY) slice_struct_field_insts /\
  ~EXISTS (\i. i.inst_opcode = CALLDATACOPY) slice_struct_field_insts
Proof
  EVAL_TAC
QED
