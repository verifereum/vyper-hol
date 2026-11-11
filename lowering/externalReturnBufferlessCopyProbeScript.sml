(* Task-only discrimination of bufferless Return normalization branches. *)
Theory externalReturnBufferlessCopyProbe
Ancestors
  externalReturnConsumerFit context compileEnv vyperAST
  vyperTyping vyperTypeSystem vyperTypeInvariants

Theorem return_bufferless_empty_struct_copy:
  acyclic_struct_metadata ce.ce_struct_fields /\
  get_struct_fields ce.ce_struct_fields (nsid_to_string dn) = [] ==>
  compile_store_memory_typed ce dst (StructT dn) src (StructT sn) =
    comp_return ()
Proof
  strip_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def] >>
  simp[Once compile_store_memory_typed_def]
QED

Theorem return_bufferless_none_source_copy:
  ~is_word_type dty /\ acyclic_struct_metadata ce.ce_struct_fields ==>
  compile_store_memory_typed ce dst dty src NoneT =
    compile_copy_memory dst src (type_memory_bytes ce dty)
Proof
  strip_tac >> simp[Once compile_store_memory_typed_def,
    is_bytestring_type_def] >> Cases_on `dty` >> simp[]
QED

Theorem return_bufferless_none_destination_copy:
  acyclic_struct_metadata ce.ce_struct_fields ==>
  compile_store_memory_typed ce dst NoneT src sty =
    compile_copy_memory dst src (type_memory_bytes ce NoneT)
Proof
  strip_tac >> simp[Once compile_store_memory_typed_def,
    is_word_type_def, is_bytestring_type_def] >> Cases_on `sty` >> simp[]
QED

Theorem return_bufferless_typed_intcall_decl:
  well_typed_expr env (Call ann (IntCall (sid,name)) args drv) /\
  env_consistent env cx es ==>
  ?sig ts fm nr params dflts body.
    FLOOKUP env.fn_sigs (sid,name) = SOME sig /\
    type_widens_to env.type_defs sig.ret_ty ann /\
    get_module_code cx sid = SOME ts /\
    lookup_callable_function cx.in_deploy name ts =
      SOME (fm,nr,params,dflts,sig.ret_ty,body)
Proof
  simp[Once well_typed_expr_def, env_consistent_def,
    env_context_consistent_def, fn_sigs_consistent_def] >> metis_tac[]
QED

(* The tuple's two exhausted-field cases both stop independently of memory. *)
Theorem return_bufferless_empty_tuple_copy:
  acyclic_struct_metadata ce.ce_struct_fields ==>
  compile_store_memory_typed ce dst (TupleT []) src (TupleT ts) =
    comp_return () /\
  compile_store_memory_typed ce dst (TupleT ts) src (TupleT []) =
    comp_return ()
Proof
  strip_tac >> conj_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def] >>
  Cases_on `ts` >> simp[Once compile_store_memory_typed_def]
QED

Theorem return_bufferless_none_widens:
  type_widens_to tenv NoneT ty ==> ty = NoneT
Proof
  Cases_on `ty` >> simp[type_widens_to_def, arg_type_fits_def]
QED

Theorem return_bufferless_struct_widens:
  type_widens_to tenv (StructT name) ty ==> ty = StructT name
Proof
  Cases_on `ty` >> simp[type_widens_to_def, arg_type_fits_def] >> metis_tac[]
QED

(* Applicability audit, C1.5.3.14.9 (not a general normalization theorem).

   The dispatch is contextScript.sml:671-808, not stmtLoweringScript.sml.
   Empty destination structs with struct sources are a literal no-op by
   return_bufferless_empty_struct_copy. Tuple fields stop when either list
   is exhausted (checked above); nonempty fields generate offsets and recurse.
   A static array's fast path copies count * destination-element-size, but
   only under equal element sizes and non-ABI-dynamic destination element.
   Otherwise it generates a loop and recursively copies the paired elements.
   Dynamic arrays ALWAYS read a source length even for zero-size elements;
   source layout zero does not justify this branch. Struct fields recurse by
   destination names with source-field fallback; a zero-size source struct
   alone says nothing about a different destination's fields. A NoneT source
   selects the destination-size fallback, checked by none_source_copy above.
   NoneT destination is also fallback, not a dedicated semantic no-op.

   The source typing route is partly available, with no equality-by-fiat:
   return_bufferless_typed_intcall_decl extracts a signature and actual
   module declaration through env_consistent -> env_context_consistent ->
   fn_sigs_consistent. Its guarantee is sig.ret_ty widens ann, not equality.
   return_site_cast/read_type_sound establish annotation-typed v and cast
   identity at the enclosing return type; they do not independently identify
   the declaration type with the compiler's physical tag.

   Missing provenance at this precise interface:
     get_module_code cx sid = SOME ts /\
     lookup_callable_function cx.in_deploy name ts =
       SOME (fm,nr,params,dflts,decl_ret,body) /\
     ce.ce_func_return_type = build_func_return_type tops
       ==> ce.ce_func_return_type (nsid_to_string (sid,name)) = decl_ret.
   This is NOT a theorem as written: it requires the actual selected-package
   runtime context (cx.in_deploy=F, appropriate module-source/tops agreement,
   and the internal/non-external declaration identity). The compiler table
   is built from unqualified non-external FunctionDecl names in tops
   (compileVyper:build_func_return_type_def), while fn_sigs_consistent uses
   get_module_code cx sid and lookup_callable_function, permitting namespaces
   and callable visibility. The selected table lemma alone does not bridge
   these domains. Any next bridge must derive those runtime/lookup hypotheses
   from body_inv/source context and supported_program, not assume the desired
   table agreement in expr_sim_inv or amend the frozen frame premise.

   Precise proposed consumer classification boundary (UNPROVED here):
     sfields_tenv_consistent ce.ce_struct_fields tenv /\
     type_widens_to tenv phy ann /\ type_widens_to tenv ann dst /\
     type_memory_bytes ce phy = 0
       ==> type_memory_bytes ce dst = 0.
   This is a proposal to test, not an admitted statement or a claimed proof.
   If valid, it removes a major destination-fallback risk, but does not itself
   prove copying is a no-op (static-array loop/tuple recursion remain).
   Real selected-runtime declaration provenance must supply the first
   widening fact; Return typing supplies the second. The desired provenance
   implication above is deliberately NOT offered as a valid general lemma.
   NoneT widening forces NoneT at each step (checked none_widens), and struct
   widening forces the identical name (checked struct_widens). Therefore a
   truly empty struct destination can bypass all physical memory, but that
   case is non-normalizing when phy=dst. Zero-sized nested fixed arrays and
   tuples require further structural classification/copy analysis; neither
   empty struct alone nor source size zero exhausts them. Non-normalizing
   equal-type/bytestring/word cases remain the accepted consumer-fit audit.
   No new ownership, physical value interpretation or full return simulation
   is claimed here. *)
