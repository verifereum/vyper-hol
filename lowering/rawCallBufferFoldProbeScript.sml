(* Independent obstruction probe: no dependency on rawCallBufferPtr. *)
Theory rawCallBufferFoldProbe
Ancestors
  bodyPtrDefs exprSimProps exprSimMemoryTransport valueEncodingProofs
  finite_map ptrDiscipline list valueEncodingProps words

Theorem empty_taint_false_bool_representation[local]:
  mem_agree_outside {} [] mem ==>
  val_in_memory (BaseTV BoolT) (BoolV F) 0 mem
Proof
  strip_tac >>
  `mem_word_at 0 mem = mem_word_at 0 []` by
    (irule memory_window_word >> irule LIST_EQ >>
     simp[LENGTH_mem_bytes_at] >> rpt strip_tac >>
     rename1 `j < 32` >>
     `mem_bytes_at j 1 [] = mem_bytes_at j 1 mem` by
       metis_tac[mem_agree_outside_def, pred_setTheory.NOT_IN_EMPTY] >>
     pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  simp[valueEncodingTheory.val_in_memory_def,
    valueEncodingTheory.val_to_w256_def] >> EVAL_TAC >> simp[]
QED

Theorem ptr_val_ok_from_covers_counterexample:
  !cx s tn.
  evaluate_type (get_tenv cx) (BaseT BoolT) = SOME (BaseTV BoolT) /\
  ptr_covers (FEMPTY |+ ("p", (0,32))) (tn with <|t_var := FEMPTY; t_mem := {}|>)
    "p" (s with <|vs_vars := FEMPTY |+ ("p",0w); vs_memory := []|>) 32 /\
  val_store_size (BaseTV BoolT) (BoolV F) <= 32 /\
  (!w mem. lookup_var "p"
      (s with <|vs_vars := FEMPTY |+ ("p",0w); vs_memory := []|>) = SOME w /\
    mem_agree_outside {} [] mem ==>
    val_in_memory (BaseTV BoolT) (BoolV F) (w2n w) mem) /\
  ~ptr_val_ok cx (BaseT BoolT) (BoolV F) (Var "p")
    (FEMPTY |+ ("p",(0,32))) (tn with <|t_var := FEMPTY; t_mem := {}|>)
    (s with <|vs_vars := FEMPTY |+ ("p",0w); vs_memory := []|>)
Proof
  simp[ptr_covers_def, ptr_val_ok_def, ptrDisciplineTheory.op_prov_def,
    ptrDisciplineTheory.op_taint_def, venomStateTheory.lookup_var_def,
    compileEnvTheory.is_word_type_def, val_store_size_def,
    valueEncodingTheory.type_memory_size_def, vyperValueTheory.evaluate_type_def,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY,
    empty_taint_false_bool_representation] >>
  rpt strip_tac >> gvs[] >>
  irule empty_taint_false_bool_representation >> simp[]
QED
