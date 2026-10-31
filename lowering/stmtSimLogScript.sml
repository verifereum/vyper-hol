(*
 * Statement simulation: Log (#637)
 *
 * log E(a1, ..., an) for an event E whose fields are word types or
 * bytestrings (supported_scalar_type), each argument of its field's type.
 * The lowering (compile_stmt's Log case, after Python's lower_Log)
 * evaluates every argument in order (compile_log_eval_all), splits them
 * into the indexed ones and the rest (split_log_ops), hashes the indexed
 * bytestrings (compile_encode_log_topic), stores the rest into a buffer
 * (compile_log_store_data), ABI-encodes that buffer into a second one
 * (compile_abi_encode_to_buf) and emits LOG with the event's hash as the
 * first topic.  The source evaluates the arguments and pushes the event
 * encode_source_event builds from the declaration's metadata.
 *
 * TOP-LEVEL:
 *   log_args_ready        — what the statement lemma needs of the
 *                           arguments: each simulates at every state the
 *                           invariant holds in, if the ones before it can
 *                           evaluate, and its value has its type
 *   compile_log_stmt_frag — log E(args), every outcome
 *)

Theory stmtSimLog
Ancestors
  list rich_list finite_map pred_set
  fragExec exprSim stmtSim stmtLowering exprLowering compileEnv
  supportedTypes vyperEvent vyperInterpreter vyperState vyperValue
Libs
  monadsyntax

(* The arguments of a log statement, evaluated and read in order: each
   simulates at its own type from every state Inv holds in, and a value it
   reads has that type and leaves Inv holding; a later argument only if
   the ones before it can evaluate, as evaluate_ind gives them. *)
Definition log_args_ready_def:
  log_args_ready ctx func cenv cx Inv [] = T /\
  log_args_ready ctx func cenv cx Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es'. (do r <- eval_expr cx e; read_result cx r od) es =
                 (INL v, es') ==>
               Inv es' /\
               ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                    value_has_type tv v) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      log_args_ready ctx func cenv cx Inv args))
End

(* log E(args) where the compile env and the source give E the same
   metadata (its hash, field types and indexed flags), each argument has
   its field's type, a word type or a bytestring, and the data buffer and
   the ABI encoding of the non-indexed fields fit below 2 ** 256 (the
   lowering hands their sizes to ALLOCA as words).

   Why it holds (unchecked intuition):
   - the source's encode_source_event cannot fail: the lengths of values,
     types and flags agree, each value has its type, and vyper_to_abi_base
     succeeds on every supported scalar type's value;
   - a word topic is the argument's operand: typed_val_to_w256 agrees with
     event_value_to_word on every supported word type (bytes20, the one
     they disagree on, is not supported); a bytestring topic is SHA3 over
     the data after its length word, which val_in_memory puts there;
   - an argument's value survives the later arguments' code through
     expr_post's frame (allocations before it, locals_kept);
   - compile_log_store_data lays the data out at the SUM of the
     type_memory_bytes before each field, the input layout the encoder
     plan of TupleT expects; with no data, LOG reads 0 bytes and
     enc (Tuple []) (ListV []) = [];
   - the logger is cc_address = cx.txn.target (call_ctx_rel), and
     logs_rel is equality of the two log lists;
   - the two ALLOCAs and the encoder write only their own buffers, which
     stmt_state_rel's allocation facts keep apart from every live local. *)
Theorem compile_log_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id args es res es' Inv h tys flags.
    eval_stmt cx (Log id args) es = (res, es') /\
    cenv.ce_event_info (nsid_to_string id) = SOME (h, tys, flags) /\
    lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
      SOME (h, tys, flags) /\
    MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
    EVERY supported_scalar_type tys /\
    SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) <
      dimword (:256) /\
    abi_size_bound cenv.ce_struct_fields
      (TupleT (log_non_indexed_types flags tys)) < dimword (:256) /\
    log_args_ready ctx func cenv cx Inv args /\ Inv es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Log id args)) es res es'
Proof
  cheat
QED
