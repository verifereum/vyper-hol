(* TOP-LEVEL: the constructor's non-canonical memory invariant supplies the
   section consumed by the emitted epilogue. Source typing and complete
   declaration lookup are explicit interfaces to the ordinary source-state
   and compile-environment proofs. *)
Theory immutableStagingBridge
Ancestors
  immutableConstructorRelation immutableDeployRelation immutableSectionRel
  immutableRelation immutableValue immutableSection compileEnv compileVyper
  valueMemoryTransport valueEncoding list arithmetic

Theorem immutable_memory_prefix_bytes:
  cap <= LENGTH mem /\ off + n <= cap ==>
  mem_bytes_at off n (TAKE cap mem) = mem_bytes_at off n mem
Proof
  strip_tac >>
  `off + n <= LENGTH mem /\ off + n <= LENGTH (TAKE cap mem)` by
    (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  simp[immutable_memory_bytes_full, immutable_prefix_slice]
QED

Theorem immutable_memory_prefix_value:
  cap <= LENGTH mem /\ off + type_memory_size tv <= cap /\
  val_in_memory tv v off mem /\ val_wf tv v ==>
  val_in_memory tv v off (TAKE cap mem)
Proof
  strip_tac >>
  `mem_bytes_at off (type_memory_size tv) mem =
   mem_bytes_at off (type_memory_size tv) (TAKE cap mem)` by
    simp[immutable_memory_prefix_bytes] >>
  drule_all val_in_memory_transport >> simp[]
QED

Theorem immutable_constructor_section:
  immutables_rel cenv addr NONE T vs ss /\
  ALOOKUP vs.immutables addr = SOME imms /\
  compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops <=
    LENGTH ss.vs_memory /\
  (!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    FLOOKUP cenv.ce_module_vars (NONE,name) =
      SOME (ImmutableLoc (compute_immutables_len
        (get_struct_fields (make_struct_fields_map tops)) pre)) /\
    ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
      val_wf tv v /\ type_memory_size tv =
        type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty) ==>
  immutables_section_rel tops imms
    (TAKE (compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) tops) ss.vs_memory)
Proof
  strip_tac >> simp[immutables_section_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!pre vis name ty slot post. _`
    (qspecl_then [`pre`,`vis`,`name`,`ty`,`slot`,`post`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >> strip_tac >>
  drule_all immutable_relation_lookup >> strip_tac >>
  `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
     type_memory_size tv <=
   compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops` by
    fs[compute_immutables_len_append, compute_immutables_len_def] >>
  qexistsl [`tv`,`v`] >> gvs[] >> conj_tac
  >- (irule immutable_memory_prefix_value >> simp[]) >>
  simp[immutable_memory_prefix_bytes]
QED

Theorem immutable_constructor_staging:
  immutables_section_rel tops imms
    (TAKE (compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) tops) ss.vs_memory) /\
  compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops <=
    LENGTH ss.vs_memory ==>
  immutable_staging_rel tops imms ss
Proof
  simp[immutable_staging_rel_def, TAKE_APPEND1]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable staging bridge: " ^ name)
  end) (DB.thms "immutableStagingBridge");
