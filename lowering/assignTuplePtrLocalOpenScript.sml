(* Static openness probes for compatible local stores. *)
Theory assignTuplePtrLocalOpen
Ancestors
  exprOpenCopies exprOpenPrimitives tupleLocalStoreProps stmtLowering context
  compileEnv valueEncoding list finite_map venomInst assignTuplePtrLocalContract
  tupleTargetStoreRun

Theorem tuple_empty_local_copy_no_emit_ptr:
  compile_store_memory cenv src dst (TupleT []) (TupleT []) ss = ((),ss)
Proof
  simp[compile_store_memory_def, is_word_type_def, is_bytestring_type_def,
       type_memory_bytes_def, compile_copy_memory_def, comp_return_def]
QED

Theorem compatible_local_memory_store_open_ptr:
  (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
  0 < type_memory_bytes cenv ty /\
  compile_store_memory cenv src dst vt ty ss = ((),sf) ==>
  ~block_is_terminated sf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type vt`
  >- (gvs[compile_store_memory_def] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  Cases_on `is_bytestring_type vt`
  >- (gvs[compile_store_memory_def, compile_store_bytestring_def, comp_bind_def] >>
      pairarg_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  gvs[compile_store_memory_def] >>
  Cases_on `type_memory_bytes cenv ty` >> gvs[compile_copy_memory_def] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compatible_local_tuple_store_open_ptr:
  !gs tys ops cenv ss sf.
  compile_tuple_store_all cenv tys gs ops ss = ((),sf) /\
  LENGTH gs = LENGTH tys /\ LENGTH ops = LENGTH tys /\
  (!i. i < LENGTH gs ==> ?id p sz vt.
    EL i gs = BaseTarget (NameTarget id) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vt /\ (is_word_type vt = is_word_type (EL i tys)) /\
    (~is_word_type (EL i tys) ==>
      vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys))) /\
  (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
    0 < type_memory_bytes cenv (EL i tys)) /\
  (gs <> [] \/ ~block_is_terminated ss) ==> ~block_is_terminated sf
Proof
  Induct >> rpt gen_tac
  >- (Cases_on `tys` >> Cases_on `ops` >>
      simp[compile_tuple_store_all_def, comp_return_def] >> metis_tac[]) >>
  Cases_on `tys` >- simp[] >>
  Cases_on `ops` >- simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i < LENGTH (_::_) ==> ?id p sz vt. _`
    (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >> gvs[] >>
  drule tuple_store_base_cons >> strip_tac >>
  `~block_is_terminated sm` by
    (drule_all tuple_local_compatible_singleton_code_ptr >>
     Cases_on `is_word_type h'` >> simp[] >> disch_tac
     >- (drule emit_void_terminated >> simp[is_terminator_def]) >>
     `0 < type_memory_bytes cenv h'` by
       (qpat_x_assum `!i. _ /\ ~is_word_type _ ==> _`
          (qspec_then `0` mp_tac) >> simp[]) >>
     drule_at (Pos last) compatible_local_memory_store_open_ptr >> simp[]) >>
  first_x_assum irule >>
  qexistsl_tac [`cenv`, `t'`, `sm`, `t`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. _ /\ ~is_word_type _ ==> _`
        (qspec_then `SUC i` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i. _ ==> ?id p sz vt. _`
    (qspec_then `SUC i` mp_tac) >> simp[]
QED
