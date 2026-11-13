Theory runtimeSymSrcDataExprCallbacksAll
Ancestors
  runtimeSymSrcDataExprCallbacks runtimeSymSrcDataExprAddressing
  runtimeSymSrcDataExprCreation runtimeSymSrcDataExprCalls

(* Whole callback-region consumers import this theory, not just Callbacks.
   The four libraries retain their original theorem names.  The compositions
   below discharge callback-region premises, leaving noncallback operations
   explicit for the expression-helper assembly.  Callback facts remain scoped
   to the actual argument list (and optional salt), not arbitrary expressions. *)

Theorem runtime_data_frame_create_call_composed:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vs p off. runtime_data_frame (compile_extcall_store_values cenv vs p off)) /\
  (!es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_multi_vvs cfn cenv es)) /\
  (!p s enc. runtime_data_frame (compile_abi_encode_to_buf p s enc)) /\
  (!p d n loc. runtime_data_frame (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. runtime_data_frame (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) /\
  (!v. runtime_data_frame (compile_create_proxy_buf v)) /\
  (!p n v s b. runtime_data_frame (compile_create_dispatch p n v s b)) /\
  (!v w s b. runtime_data_frame (compile_create_copy v w s b)) /\
  (!v off. runtime_data_frame (compile_create_blueprint_check v off)) /\
  (!v w s off n p len b.
    runtime_data_frame (compile_create_blueprint_append v w s off n p len b)) /\
  (!e. MEM e args ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_call cfn cenv ck has_salt rof args)
Proof
  strip_tac >> irule runtime_data_frame_create_call >>
  simp[runtime_data_frame_create_blueprint_args,
       runtime_data_frame_create_ctor_tuple, runtime_data_frame_raw_create,
       runtime_data_frame_create_snapshot, runtime_data_frame_create_salt,
       runtime_data_frame_lower_value]
QED

Theorem runtime_data_frame_call_composed:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!topics data e. target = RawLog /\ args = [topics; data] /\
    MEM e (raw_log_topic_exprs topics) ==>
    runtime_data_frame (cfn cenv (expr_type e) e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) /\
  (!es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_multi_vvs cfn cenv es)) /\
  (!vs stack tys. runtime_data_frame (compile_stage_intcall_args cenv vs stack tys)) /\
  (!buf vs off. runtime_data_frame (store_multi_results buf vs off)) /\
  (!a vs ts ms az mid rz mn rb sc v g sk hd d rt dt ei di.
    runtime_data_frame (compile_external_call_kwargs cenv a vs ts ms az mid rz mn rb
      sc v g sk hd d rt dt ei di)) /\
  (!n. runtime_data_frame (compile_raw_call_outbuf n)) /\
  (!a p n g v ct sz rof ov op.
    runtime_data_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) /\
  runtime_data_frame compile_msg_data_to_memory /\
  (!v. runtime_data_frame (compile_raw_revert v)) /\
  (!v. runtime_data_frame (compile_selfdestruct v)) /\
  (!vs p off. runtime_data_frame (compile_extcall_store_values cenv vs p off)) /\
  (!p s enc. runtime_data_frame (compile_abi_encode_to_buf p s enc)) /\
  (!p d n loc. runtime_data_frame (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. runtime_data_frame (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) /\
  (!v. runtime_data_frame (compile_create_proxy_buf v)) /\
  (!p n v s b. runtime_data_frame (compile_create_dispatch p n v s b)) /\
  (!v w s b. runtime_data_frame (compile_create_copy v w s b)) /\
  (!v off. runtime_data_frame (compile_create_blueprint_check v off)) /\
  (!v w s off n p len b.
    runtime_data_frame (compile_create_blueprint_append v w s off n p len b)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty target args dr)
Proof
  strip_tac >> irule runtime_data_frame_call >>
  simp[runtime_data_frame_ext_call_kwargs, runtime_data_frame_materialize_vv,
       runtime_data_frame_create_call_composed]
QED

(* Coverage audit of exprLowering's lower_value .. compile_powmod256_names
   region (the three compiler bodies are a separate publication):
   Callbacks: lower_value/with_loc, value wrappers, multi_exprs, tuple/array,
     concat, store_abi_tuple, materialize/ifexp_arm/snapshot, struct_lit,
     abi_encode_args, external kwargs, and create_salt.
   Addressing: get_target_ptr, subscript, attribute, extcall_store_args.
   Creation: ctor_tuple, blueprint_args, snapshot, raw_create, create_call.
   Calls: all compile_call targets, store_words, invert, acc, modular names.
   call_can_mutate and expr_can_mutate are pure tests, not state computations.
   No recursive callback premise is widened: addressing uses target_indices;
   list builders use members; creation uses members and optional salt; calls
   additionally expose RawLog topic children, guarded by target and arity.
   multi_vvs and all remaining primitive/context/ABI/builtin facts stay explicit
   for the later NonCallback/Context/ABI/Builtins assembly. *)
