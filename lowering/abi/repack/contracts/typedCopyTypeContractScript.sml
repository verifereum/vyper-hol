(* TOP-LEVEL: a child type-pair contract quantifies over actual compiler
   operands and cuts. Scalar and bytes/string copies discharge it directly. *)
Theory typedCopyTypeContract
Ancestors
  vyperEventArgCompat
  typedCopyContract typedCopyWordContract typedBytesStoreProps
  compileEnv context vyperValue vyperTypeSystem

Definition typed_copy_type_contract_def:
  typed_copy_type_contract ctx func cenv fty aty ftv atv <=>
    !dst src cs ret cs'.
      compile_store_memory_typed cenv dst fty src aty cs = (ret,cs') ==>
      typed_copy_contract ctx func dst src ftv atv cs cs'
End

Theorem typed_copy_type_contract_result:
  !ctx func cenv fty aty ftv atv dst src cs ret cs'.
    typed_copy_type_contract ctx func cenv fty aty ftv atv /\
    compile_store_memory_typed cenv dst fty src aty cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  simp[typed_copy_type_contract_def]
QED

Theorem typed_copy_type_contract_word:
  !tenv ctx func cenv ty tv src_ty.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
    typed_copy_type_contract ctx func cenv ty src_ty tv tv
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `dst`, `ty`, `tv`, `src`, `src_ty`, `cs`, `ret`, `cs'`]
    compile_store_memory_typed_word_contract) >> simp[]
QED

Theorem typed_copy_type_contract_bytes:
  !tenv ctx func cenv fty aty ftv atv.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
    typed_copy_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`, `src`, `aty`, `atv`, `cs`, `ret`, `cs'`]
    compile_store_memory_typed_bytes_contract) >> simp[]
QED
