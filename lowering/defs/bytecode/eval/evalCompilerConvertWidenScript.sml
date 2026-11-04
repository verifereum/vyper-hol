(* A bytestring convert whose source buffer is smaller than the target's
   copies the value into a new buffer of the target's size, after the
   argument's own code.  Mirrors Python: convert.py
   _bytestring_convert_value (vyperlang/vyper#5338).
   TOP-LEVEL: convert_widen_name_copies, convert_widen_literal_copies,
              convert_same_size_no_copy. *)
Theory evalCompilerConvertWiden
Ancestors
  evalCompilerSubsetState compileVyper vyperCompiler exprLowering context alist
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])

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
