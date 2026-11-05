(* Memory case of the body induction for empty(T) of a non-word type: a
   fresh zeroed buffer (admitted; its own piece). *)
Theory bodyMemTbEmptyMemory
Ancestors
  bodyMemoryPreds compileEnv

Theorem body_type_builtin_empty_memory_mem_case:
  !cx v11 typ es.
    ~is_word_type typ ==>
    body_expr_mem_ok cx (TypeBuiltin v11 Empty typ es)
Proof
  cheat
QED
