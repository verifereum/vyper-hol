Theory immutableRelation
Ancestors
  immutableSection immutableEncodingProofs immutableEncoding compileEnv

(* A lookup-to-declaration interface, discharged by location allocation and
   source-name uniqueness. It deliberately does not presume unshadowed keys. *)
Definition immutable_section_layout_def:
  immutable_section_layout cenv tops <=>
    !name off.
      FLOOKUP cenv.ce_vars (module_var_key (NONE,name)) =
        SOME (ImmutableLoc off) ==>
      ?pre post vis ty slot.
        tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
        off = compute_immutables_len
          (get_struct_fields (make_struct_fields_map tops)) pre
End

Definition immutable_staging_exact_def:
  immutable_staging_exact tops imms ss <=>
    TAKE (LENGTH (immutables_section tops imms))
      (ss.vs_memory ++ REPLICATE (LENGTH (immutables_section tops imms)) 0w) =
    immutables_section tops imms
End

Theorem immutable_initialized_section_slice:
  immutables_initialized tops imms /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
  immutable_value_admissible tv v /\
  type_memory_size tv =
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty /\
  TAKE (type_memory_size tv)
    (DROP (compute_immutables_len
       (get_struct_fields (make_struct_fields_map tops)) pre)
       (immutables_section tops imms)) = encode_immutable_value tv v
Proof
  strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  qpat_x_assum `immutables_initialized _ _`
    (assume_tac o REWRITE_RULE [immutables_initialized_def]) >>
  drule_all immutable_decl_bytes_initialized >> strip_tac >>
  drule immutables_section_slice >>
  disch_then (qspec_then `imms` assume_tac) >> gvs[]
QED

Theorem immutable_slice_bound:
  TAKE n (DROP off bs) = encoded /\ LENGTH encoded = n /\ off <= LENGTH bs ==>
  off + n <= LENGTH bs
Proof
  strip_tac >>
  `LENGTH (TAKE n (DROP off bs)) = n` by metis_tac[] >>
  gvs[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_DROP] >> decide_tac
QED

Theorem immutable_section_relation:
  immutable_section_layout cenv tops /\ immutables_initialized tops imms /\
  ALOOKUP vs.immutables addr = SOME imms /\
  ss.vs_data_section = immutables_section tops imms ==>
  immutables_rel cenv addr NONE F vs ss
Proof
  strip_tac >> simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutable_section_layout _ _`
    (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
  disch_then drule >> strip_tac >>
  drule_all immutable_initialized_section_slice >> strip_tac >>
  `byte_offset <= LENGTH (immutables_section tops imms)` by
    (gvs[] >> simp[compileVyperTheory.compute_immutables_len_append]) >>
  `byte_offset + type_memory_size tv <= LENGTH (immutables_section tops imms)` by
    metis_tac[immutable_slice_bound, encode_immutable_value_length] >>
  metis_tac[immutable_encoding_slice_decodes, immutables_section_length]
QED

Theorem immutable_relation_same_bytes:
  immutables_rel cenv addr src ctor vs ss /\
  ss'.vs_memory = ss.vs_memory /\ ss'.vs_data_section = ss.vs_data_section ==>
  immutables_rel cenv addr src ctor vs ss'
Proof
  strip_tac >> fs[immutables_rel_def] >> metis_tac[]
QED

Theorem immutable_base_zero_literal:
  cenv.ce_imm_alloca = SOME (Lit 0w) ==> immutable_base_zero cenv ss
Proof
  simp[immutable_base_zero_def, venomStateTheory.eval_operand_def]
QED

(* ISTORE bookkeeping is byte addressed, not a word-indexed map. *)
Theorem immutable_istore_byte_address:
  FLOOKUP (istore off w ss).vs_immutables off = SOME w /\
  (istore off w ss).vs_memory = (mstore off w ss).vs_memory
Proof
  simp[venomExecSemanticsTheory.istore_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_prefix_slice:
  off + n <= cap ==>
  TAKE n (DROP off (TAKE cap bs)) = TAKE n (DROP off bs)
Proof
  simp[listTheory.DROP_TAKE, listTheory.TAKE_TAKE_MIN] >>
  strip_tac >> `MIN n (cap - off) = n` by simp[arithmeticTheory.MIN_DEF] >> simp[]
QED

(* This boundary deliberately asks for actual region capacity. The exact
   staging predicate alone permits a short zero-padded memory. *)
Theorem immutable_staging_prefix:
  immutable_staging_exact tops imms ss /\
  LENGTH (immutables_section tops imms) <= LENGTH ss.vs_memory ==>
  TAKE (LENGTH (immutables_section tops imms)) ss.vs_memory =
    immutables_section tops imms
Proof
  strip_tac >> fs[immutable_staging_exact_def, listTheory.TAKE_APPEND1]
QED

Theorem immutable_relation_from_slices:
  (!name tv v off.
    FLOOKUP cenv.ce_vars (module_var_key (src,name)) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP vs.immutables addr of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    immutable_value_admissible tv v /\
    off + type_memory_size tv <= LENGTH (if ctor then ss.vs_memory else ss.vs_data_section) /\
    TAKE (type_memory_size tv)
      (DROP off (if ctor then ss.vs_memory else ss.vs_data_section)) =
        encode_immutable_value tv v) ==>
  immutables_rel cenv addr src ctor vs ss
Proof
  simp[immutables_rel_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  irule immutable_encoding_slice_decodes >> simp[]
QED

Theorem immutable_constructor_relation:
  immutable_section_layout cenv tops /\ immutables_initialized tops imms /\
  ALOOKUP vs.immutables addr = SOME imms /\
  immutable_staging_exact tops imms ss /\
  LENGTH (immutables_section tops imms) <= LENGTH ss.vs_memory ==>
  immutables_rel cenv addr NONE T vs ss
Proof
  strip_tac >> irule immutable_relation_from_slices >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutable_section_layout _ _`
    (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
  disch_then drule >> strip_tac >>
  drule_all immutable_initialized_section_slice >> strip_tac >>
  `off <= LENGTH (immutables_section tops imms)` by
    (gvs[] >> simp[compileVyperTheory.compute_immutables_len_append]) >>
  `off + type_memory_size tv <= LENGTH (immutables_section tops imms)` by
    metis_tac[immutable_slice_bound, encode_immutable_value_length] >>
  drule_all immutable_staging_prefix >> strip_tac >>
  `TAKE (type_memory_size tv) (DROP off ss.vs_memory) =
     encode_immutable_value tv v` by
    metis_tac[immutable_prefix_slice] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem immutable_relation_preserve_canonical_slices:
  (!name tv v off.
    FLOOKUP cenv.ce_vars (module_var_key (src,name)) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP vs.immutables addr of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    immutable_value_admissible tv v /\
    off + type_memory_size tv <= LENGTH (if ctor then ss'.vs_memory else ss'.vs_data_section) /\
    TAKE (type_memory_size tv) (DROP off (if ctor then ss.vs_memory else ss.vs_data_section)) =
      encode_immutable_value tv v /\
    TAKE (type_memory_size tv) (DROP off (if ctor then ss'.vs_memory else ss'.vs_data_section)) =
      TAKE (type_memory_size tv) (DROP off (if ctor then ss.vs_memory else ss.vs_data_section))) ==>
  immutables_rel cenv addr src ctor vs ss'
Proof
  strip_tac >> irule immutable_relation_from_slices >> metis_tac[]
QED

(* Writers must establish this byte replacement equation, including padding.
   Neither a word-only invariant nor val_in_memory supplies that equation. *)
Theorem immutable_staging_replace:
  immutable_staging_exact tops imms ss /\
  LENGTH (immutables_section tops imms) <= LENGTH ss.vs_memory /\
  LENGTH (immutables_section tops imms') = LENGTH (immutables_section tops imms) /\
  immutables_section tops imms' =
    TAKE off (immutables_section tops imms) ++ replacement ++
    DROP (off + LENGTH replacement) (immutables_section tops imms) /\
  ss'.vs_memory = TAKE off (immutables_section tops imms) ++ replacement ++
    DROP (off + LENGTH replacement) (immutables_section tops imms) ++ tail ==>
  immutable_staging_exact tops imms' ss'
Proof
  strip_tac >>
  `ss'.vs_memory = immutables_section tops imms' ++ tail` by
    metis_tac[listTheory.APPEND_ASSOC] >>
  qpat_x_assum `immutables_section tops imms' = _` kall_tac >>
  qpat_x_assum `ss'.vs_memory = _ ++ _ ++ _ ++ _` kall_tac >>
  simp[immutable_staging_exact_def, GSYM listTheory.APPEND_ASSOC,
       listTheory.TAKE_APPEND1]
QED

Theorem immutable_relation_lookup:
  immutables_rel cenv addr src ctor vs ss /\
  FLOOKUP cenv.ce_vars (module_var_key (src,name)) = SOME (ImmutableLoc off) /\
  ALOOKUP vs.immutables addr = SOME imms /\
  FLOOKUP (get_source_immutables src imms) name = SOME (tv,v) ==>
  immutable_value_admissible tv v /\
  off + type_memory_size tv <= LENGTH (if ctor then ss.vs_memory else ss.vs_data_section) /\
  val_in_memory tv v off (if ctor then ss.vs_memory else ss.vs_data_section)
Proof
  strip_tac >> fs[immutables_rel_def] >> metis_tac[]
QED

Theorem immutable_base_zero_assigned:
  cenv.ce_imm_alloca = SOME (Var out) ==>
  immutable_base_zero cenv (update_var out 0w ss)
Proof
  simp[immutable_base_zero_def, venomStateTheory.eval_operand_def,
       venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_RELATION_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable relation theorem: " ^ name)
  end) (DB.thms "immutableRelation");
