(* Ordinary runtime selector endpoint aligned with counted execution.
   Reuses the general vv_post_inst_idx transport; no new transport rule. *)
Theory bodyPtrEnvBuiltinsRuntimePost
Ancestors exprSimHash exprSimVVFrame exprLowering exprLoweringProps
  context compileEnv loweringPosts vyperAST vyperValue venomState finite_map

Theorem method_id_runtime_counted_endpoint_post:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t r. run_inst_seq (emitted_insts sm sb) s = OK t /\
    builtin_result cx es'.accounts
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
         <|ptr_location := LocMemory; ptr_operand := op|>)
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all method_id_runtime_typed_post_run >>
  simp[vv_post_inst_idx]
QED
