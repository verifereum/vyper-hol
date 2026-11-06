(* Memory case of the body induction for extract32 outside a dynamic Bytes
   source with an unsigned start.  Held: s3's extract32 typing still admits
   a bytes32 source and a signed start; s1-builtins-aggregates' typing fix
   (extract32 takes dynamic Bytes and an unsigned start) rules this case
   out, and it is discharged from well_typed_type_builtin_args_def once
   that lands. *)
Theory bodyMemTbExtract32Held
Ancestors
  bodyMemoryPreds

Theorem body_type_builtin_extract32_other_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) /\
    ~(?src off m k. es = [src; off] /\
        expr_type src = BaseT (BytesT (Dynamic m)) /\
        expr_type off = BaseT (UintT k)) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ es)
Proof
  cheat
QED
