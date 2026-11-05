Theory extRetNormalizeInputsPtr
Ancestors
  typedCopyPtr bodyPtrDefs vyperTypeSystem compileEnv

(* Word-class preservation subsumes the source-word equality observation
   local to stmtSimReturnWiden; that local theorem is not exported. *)
Theorem arg_type_fits_word_class:
  (!sty ty. arg_type_fits sty ty ==>
     (is_word_type sty <=> is_word_type ty)) /\
  (!stys tys. arg_types_fit stys tys ==>
     (EVERY is_word_type stys <=> EVERY is_word_type tys))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_word_type_def] >> gvs[]
QED

Theorem typed_return_nonword_source:
  !env ty e.
    IS_SOME (type_stmt env ty (Return (SOME e))) /\
    ~is_word_type ty ==> ~is_word_type (expr_type e)
Proof
  simp[type_stmt_return_some_iff, type_widens_to_def] >>
  metis_tac[cj 1 arg_type_fits_word_class]
QED

Theorem typed_return_ptr_buf_ok:
  !env ty e ce op G s.
    IS_SOME (type_stmt env ty (Return (SOME e))) /\
    ~is_word_type ty /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) ==>
    ptr_buf_ok ce e op G s
Proof
  metis_tac[typed_return_nonword_source]
QED
