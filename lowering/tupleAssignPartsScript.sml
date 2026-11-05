(* Shared tuple-assignment code slices and compiler growth. *)
Theory tupleAssignParts
Ancestors
  tupleAssignCode stmtSimAssignTuple stmtSimReturn exprLowering exprLoweringProps
  loweringSlice compileEnv fragExec stmtLoweringMono
Libs
  monadsyntax

Theorem tuple_target_stores_growth:
  !cenv tys gs ops st sf.
    compile_tuple_store_all cenv tys gs ops st = ((),sf) ==>
    cs_extends st sf /\ st.cs_next_var <= sf.cs_next_var
Proof
  cheat
QED

Theorem assign_tuple_targets_code_parts:
  !cenv lctx ty gs e tys sa sf c func.
    stmt_env cenv lctx ty (Assign (TupleTarget gs) e) sa = (c,sf) /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sc op su staged sl elems ss.
      compile_expr cenv (TupleT tys) e sa = (vv,sc) /\
      unwrap_value cenv vv sc = (op,su) /\
      (if is_memory_view e /\ vv_location vv = SOME LocMemory /\
          EXISTS (\t. ~is_word_type t) tys /\
          0 < SUM (MAP (type_memory_bytes cenv) tys) then
         do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
            ptr <- comp_return buf.buf_operand;
            emit_void MCOPY [ptr; op;
              Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
            comp_return ptr od
       else comp_return op) su = (staged,sl) /\
      compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
      compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
      cs_extends sa sc /\ cs_extends sc su /\ cs_extends su sl /\
      cs_extends sl ss /\ cs_extends ss sf /\
      fn_has_code sa sc func /\ fn_has_code sc su func /\
      fn_has_code su sl func /\ fn_has_code sl ss func /\
      fn_has_code ss sf func /\
      sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
      sl.cs_next_var <= ss.cs_next_var /\ ss.cs_next_var <= sf.cs_next_var
Proof
  cheat
QED
