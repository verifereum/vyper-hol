(*
 * The custom-error revert gadget: the Venom code compile_revert_with_custom_error
 * emits after its argument stores (stmtLowering).  It allocates a buffer of the
 * arguments' ABI size bound plus a selector word, MSTOREs the selector, ABI-encodes
 * the argument tuple behind it (when there are arguments) and REVERTs from buf+28.
 *
 * The argument stores interleave compile_expr, so each tower (S1 stmt_frag, S3
 * stmt_frag_mem, stmt_frag_ptr) simulates them with its own expression judgement;
 * the tail after them is Venom-only and has this one execution lemma, which all
 * three towers' custom-error cases use.
 *
 * TOP-LEVEL:
 *   custom_error_revert_tail_def               the code after the argument stores
 *   compile_revert_with_custom_error_split     the lowering = alloc; stores; tail
 *   custom_error_revert_tail_run (ADMITTED)    the tail reaches REVERT, writing only
 *                                              inside its own fresh allocas
 *)
Theory stmtSimCustomErrorRevert
Ancestors
  stmtLowering compileEnv fragGasPathMem abiEncoderWindowContract
  abiEncoderAdmissible abiEncoderRegisteredEffect abiEncoderProps
  exprLoweringProps venomMemDefs venomState venomExecSemantics vyperAST
  valueEncoding

Definition custom_error_revert_tail_def:
  custom_error_revert_tail cenv id tys args_buf no_args =
    do buf_alloc <- compile_alloc_buffer
         (abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32);
       buf <- return buf_alloc.buf_operand;
       emit_void MSTORE [buf; Lit (n2w (cenv.ce_method_id (SND id) tys))];
       if no_args then
         do revert_offset <- emit_op ADD [buf; Lit 28w];
            emit_inst REVERT [revert_offset; Lit 4w] []
         od
       else
         do payload_buf <- emit_op ADD [buf; Lit 32w];
            encoded_len <- compile_abi_encode_to_buf payload_buf args_buf
              (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys));
            revert_offset <- emit_op ADD [buf; Lit 28w];
            revert_len <- emit_op ADD [Lit 4w; encoded_len];
            emit_inst REVERT [revert_offset; revert_len] []
         od
    od
End

Theorem compile_revert_with_custom_error_split:
  !cenv id positional kwargs params s0 s1.
    cenv.ce_error_info (nsid_to_string id) = SOME params /\
    compile_revert_with_custom_error cenv (CustomError id positional kwargs) s0 =
      ((),s1) ==>
    ?args_alloc sa sm.
      compile_alloc_buffer (type_memory_bytes cenv (TupleT (MAP SND params))) s0 =
        (args_alloc,sa) /\
      compile_custom_error_store_args cenv
        (custom_error_exprs (CustomError id positional kwargs))
        (MAP SND params) args_alloc.buf_operand 0 sa = ((),sm) /\
      custom_error_revert_tail cenv id (MAP SND params) args_alloc.buf_operand
        (NULL (custom_error_exprs (CustomError id positional kwargs))) sm =
        ((),s1)
Proof
  rpt strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv (TupleT (MAP SND params))) s0` >>
  rename1 `_ = (args_alloc,sa)` >>
  Cases_on `compile_custom_error_store_args cenv
              (custom_error_exprs (CustomError id positional kwargs))
              (MAP SND params) args_alloc.buf_operand 0 sa` >>
  rename1 `_ = (u,sm)` >> Cases_on `u` >>
  qexistsl_tac [`args_alloc`,`sa`,`sm`] >>
  gvs[compile_revert_with_custom_error_def, custom_error_revert_tail_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* ADMITTED: the gadget lemma (run from the state after the argument stores).
   With arguments, the args tuple is a registered alloca outside this fragment,
   holding a valid encoder input whose encoding fits the ABI size bound.  A
   recorded ALLOCA keeps its literal size (the clause stmt_state_rel carries),
   so a re-entered site of this fragment reuses a region of the size it asks. *)
Theorem custom_error_revert_tail_run:
  !ctx func cenv id tys args_buf no_args sm sb s a aid n ei at av.
    custom_error_revert_tail cenv id tys args_buf no_args sm = ((),sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32 < 2 ** 64 /\
    ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) /\
    (~no_args ==>
       abi_encoder_admissible ei /\
       eval_operand args_buf s = SOME (n2w a) /\
       (!x. args_buf = Var x ==> not_fresh_at sm x) /\
       FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid NOTIN frag_ids sm sb /\
       type_memory_bytes cenv (TupleT tys) <= n /\
       abi_encoder_window_input ei at av a (type_memory_bytes cenv (TupleT tys))
         s.vs_memory /\
       LENGTH (enc at av) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)) /\
    alloca_inv s /\ alloca_room ctx func s /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==>
       sz = w2n w) /\
    ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t) /\
        abi_encoder_registered_effect (frag_ids sm sb) [] s t
Proof
  cheat
QED
