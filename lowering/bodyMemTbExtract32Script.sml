(* Memory case of the body induction for extract32: a dynamic Bytes source
   with an unsigned start (the S1 case compile_extract32_ready_sim covers),
   and the rest, held in bodyMemTbExtract32Held. *)
Theory bodyMemTbExtract32
Ancestors
  bodyMemoryPreds bodyMemTbExtract32Held bodyMemTbExtract32Load
  bodyMemTbExtract32Action bodyMemTbExtract32TypedSuffix bodyMemTbExtract32Bind

Theorem body_type_builtin_extract32_ready_mem_case:
  !cx v11 typ src off m k.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) 2)
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx [src; off]) /\
    expr_type src = BaseT (BytesT (Dynamic m)) /\
    expr_type off = BaseT (UintT k) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ [src; off])
Proof
  cheat
QED

Theorem body_type_builtin_extract32_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ es)
Proof
  rpt strip_tac >>
  Cases_on `?src off m k. es = [src; off] /\
              expr_type src = BaseT (BytesT (Dynamic m)) /\
              expr_type off = BaseT (UintT k)`
  >- (gvs[] >> irule body_type_builtin_extract32_ready_mem_case >>
      gvs[] >> metis_tac[]) >>
  irule body_type_builtin_extract32_other_mem_case >> simp[] >> metis_tac[]
QED
