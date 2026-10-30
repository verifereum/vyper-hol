(* TOP-LEVEL: compile_abi_word_tuple_frag.
   Typed scalar tuples are encoded by the actual ABI compiler's
   bulk-copy case, with exact source ABI bytes and preserved private slices. *)
Theory abiWordTupleExecution
Ancestors
  abiCopyExecution abiTupleValueEncoding createSourceCallback
  fragExec exprLowering compileEnv valueEncoding valueEncodingProps
  vyperABI vyperValue vyperTyping vyperTypeABI venomState list words

Theorem compile_abi_word_tuple_frag:
  EVERY is_word_type tys ∧ evaluate_types tenv tys [] = SOME tvs ∧
  values_have_types tvs vs ∧ 32 * LENGTH tys < 2 ** 256 ∧
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info sfields cenv (TupleT tys)) cs = (result,cs') ⇒
  ∃avs. vyper_to_abi_list tenv tys vs = SOME avs ∧
    result = Lit (n2w (32 * LENGTH tys)) ∧ cs_extends cs cs' ∧
    frag_exec ctx cs cs'
      (λs. fresh_vars_wrt cs s ∧
           eval_operand dst s = SOME d ∧ eval_operand src s = SOME p ∧
           create_live live s ∧ create_memory_snapshot regions s ∧
           EVERY (λ(off,bs). off + LENGTH bs ≤ LENGTH s.vs_memory ∧
             (off + LENGTH bs ≤ w2n d ∨ w2n d + 32 * LENGTH tys ≤ off)) regions ∧
           tuple_in_memory vs tvs (w2n p) s.vs_memory ∧
           w2n p + 32 * LENGTH tys ≤ LENGTH s.vs_memory)
      (λs. fresh_vars_wrt cs' s ∧ create_live live s ∧
           create_memory_snapshot
             ((w2n d,enc (vyper_to_abi_type tenv (TupleT tys)) (ListV avs))::regions) s)
      (K F)
Proof
  strip_tac >>
  `OPT_MMAP (evaluate_type tenv) tys = SOME tvs` by
    fs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (λty tv. evaluate_type tenv ty = SOME tv) tys tvs` by
    (irule OPT_MMAP_LIST_REL >> simp[]) >>
  drule_all (cj 2 vyper_to_abi_total) >> strip_tac >>
  qexists_tac `avs` >>
  `type_to_abi_enc_info sfields cenv (TupleT tys) = AbiCopy (32 * LENGTH tys)` by
    (irule abi_word_tuple_metadata >> simp[]) >>
  `compile_abi_encode_to_buf dst src (AbiCopy (32 * LENGTH tys)) cs =
     (result,cs')` by gvs[] >>
  mp_tac (Q.INST
    [`n` |-> `32 * LENGTH (tys : vyperAST$type list)`,
     `bytes` |-> `enc (vyper_to_abi_type tenv (TupleT tys)) (ListV avs)`]
    compile_abi_copy_frag) >>
  impl_tac >- simp[] >> strip_tac >> simp[] >>
  irule frag_exec_conseq >>
  qpat_assum `frag_exec ctx cs cs' _ _ _`
    (fn th => MAP_EVERY EXISTS_TAC (List.drop (#2 (strip_comb (concl th)),3))) >>
  simp[] >>
  rpt strip_tac >>
  `w2n p + 32 * LENGTH tys ≤ LENGTH s.vs_memory` by decide_tac >>
  drule_all abi_typed_word_tuple_encoding >> strip_tac >>
  gvs[read_memory_def, mem_bytes_at_def]
QED
