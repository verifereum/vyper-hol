(* Readable source windows for the nonempty bytestring conversion branch. *)
Theory bodyMemTbConvertSourceDispatch
Ancestors
  bodyMemTbConvertSourceMemory bodyMemTbConvertDynamicScalar
  bodyMemTbConvertDynamicCast bodyMemTbConvertWidenCounted
  bodyMemTbConvertScalarDispatch exprSimHyps exprSimHypsDefs
  compileEnv vyperTypeSystem vyperValue valueEncoding valueCopyBytes exprSimMemDefs

Theorem convert_nonzero_bytestring_memory_size[local]:
  is_bytestring_type t /\
  t <> BaseT (BytesT (Dynamic 0)) /\ t <> BaseT (StringT 0) ==>
  64 <= type_memory_bytes cenv t
Proof
  Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[is_bytestring_type_def]
  >- (simp[type_memory_bytes_def] >> strip_tac >>
      `1 <= (n + 31) DIV 32` by simp[arithmeticTheory.X_LE_DIV] >> decide_tac) >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_bytestring_type_def, type_memory_bytes_def] >> strip_tac >>
  `1 <= (n + 31) DIV 32` by simp[arithmeticTheory.X_LE_DIV] >> decide_tac
QED

Theorem convert_bytestring_source_window:
  expr_sim_inv cenv cx env ee /\
  is_bytestring_type t /\ is_bytestring_type lt /\
  lt <> BaseT (BytesT (Dynamic 0)) /\ lt <> BaseT (StringT 0) /\
  vv_store_bound cx t lt ee tv vv s /\
  evaluate_type (get_tenv cx) lt = SOME tvt /\
  ((?vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory /\
            p.ptr_operand = op) \/ (?vt. vv = StackValue vt op)) /\
  eval_operand op s = SOME w ==>
  w2n w + 64 <= s.vs_alloca_next
Proof
  strip_tac >>
  `~is_word_type t` by metis_tac[is_bytestring_word_type] >>
  `type_memory_bytes cenv lt = type_memory_size tvt` by
    metis_tac[expr_sim_inv_memory_size] >>
  `64 <= type_memory_bytes cenv lt` by
    (irule convert_nonzero_bytestring_memory_size >> simp[]) >>
  gvs[vv_store_bound_def] >>
  `type_memory_size tvt = 0 \/
   w2n w + type_memory_size tvt <= s.vs_alloca_next` by metis_tac[] >>
  decide_tac
QED
