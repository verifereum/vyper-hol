(* Memory-safe MakeArray with physically widened internal-call elements.
   The shared assembly stores each child at its physical post-value type. *)
Theory bodyMemMakeArrayWidened
Ancestors
  bodyMemMakeArrayAssembly

(* PORT_ADMISSION: SEQ-4299, s3-mem-safety, replaces body_make_array_widened_call_elem_mem which built at 0de4aa499 *)
(* HELD, the twin of bodyMemAggregateLoops' aggregate_make_tuple_nested_sim_mem:
   an element whose declared member type it widens to other than as a
   bytestring (a nested bound change), which needs a typed relayout store. *)
Theorem body_make_array_widened_nested_mem[local]:
  !cx ty t n es tops ctx func cenv env ty' st.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
    (?e. MEM e es /\ int_calls_expr e <> [] /\
         lowered_value_type cenv e <> expr_type e) /\
    ~(case ty of
         TupleT tys => LIST_REL (\m e. m = expr_type e \/
           is_bytestring_type m /\ is_bytestring_type (expr_type e)) tys es
       | ArrayT et' bd => EVERY (\e. et' = expr_type e \/
           is_bytestring_type et' /\ is_bytestring_type (expr_type e)) es
       | _ => T) ==>
    expr_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
    expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  cheat
QED

Theorem body_make_array_widened_call_elem_mem:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) ==>
    !tops ctx func cenv env ty' st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
      (?e. MEM e es /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
      expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(case ty of
           TupleT tys => LIST_REL (\m e. m = expr_type e \/
             is_bytestring_type m /\ is_bytestring_type (expr_type e)) tys es
         | ArrayT et' bd => EVERY (\e. et' = expr_type e \/
             is_bytestring_type et' /\ is_bytestring_type (expr_type e)) es
         | _ => T)`
  >- (mp_tac (SPEC_ALL body_make_array_sim_mem) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[]) >>
  mp_tac (SPEC_ALL body_make_array_widened_nested_mem) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED
