(* TOP-LEVEL: immutables_section_rel describes the actual installed bytes.
   Unused string capacity and inactive dynamic elements may vary. Sparse
   fixed-array defaults are constrained by immutable_value_bytes_rel. The
   canonical encoder remains a useful witness, not a deployment invariant. *)
Theory immutableSectionRel
Ancestors
  immutableRelation immutableSection immutableEncodingProofs immutableEncoding
  compileVyper compileEnv immutableValue valueEncoding vyperState list

Definition immutables_section_rel_def:
  immutables_section_rel tops imms (section:word8 list) <=>
    LENGTH section = compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) tops /\
    !pre vis name ty slot post.
      tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
      ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
        immutable_value_admissible tv v /\
        type_memory_size tv =
          type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty /\
        val_in_memory tv v
          (compute_immutables_len
            (get_struct_fields (make_struct_fields_map tops)) pre) section /\
        immutable_value_bytes_rel tv v
          (mem_bytes_at (compute_immutables_len
            (get_struct_fields (make_struct_fields_map tops)) pre)
            (type_memory_size tv) section)
End

Definition installed_code_rel_def:
  installed_code_rel tops runtime imms code <=>
    ?section. code = runtime ++ section /\
      immutables_section_rel tops imms section
End

Theorem installed_code_rel_section:
  installed_code_rel tops runtime imms code ==>
  code = runtime ++ DROP (LENGTH runtime) code /\
  immutables_section_rel tops imms (DROP (LENGTH runtime) code)
Proof
  rw[installed_code_rel_def] >> simp[DROP_APPEND]
QED

Theorem immutables_section_rel_length:
  immutables_section_rel tops imms section ==>
  LENGTH section = compute_immutables_len
    (get_struct_fields (make_struct_fields_map tops)) tops
Proof
  simp[immutables_section_rel_def]
QED

Theorem immutables_section_rel_lookup:
  immutables_section_rel tops imms section /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
  immutable_value_admissible tv v /\
  type_memory_size tv =
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty /\
  compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
    type_memory_size tv <= LENGTH section /\
  val_in_memory tv v
    (compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) pre) section /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at (compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) pre)
      (type_memory_size tv) section)
Proof
  strip_tac >>
  qpat_x_assum `immutables_section_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutables_section_rel_def]) >>
  qpat_x_assum `!pre vis name ty slot post. _`
    (qspecl_then [`pre`, `vis`, `name`, `ty`, `slot`, `post`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  simp[compute_immutables_len_append, compute_immutables_len_def]
QED

Theorem canonical_immutables_section_rel:
  immutables_initialized tops imms ==>
  immutables_section_rel tops imms (immutables_section tops imms)
Proof
  strip_tac >> rewrite_tac[immutables_section_rel_def, immutables_section_length] >>
  rpt gen_tac >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  `immutables_initialized_with
     (get_struct_fields (make_struct_fields_map tops)) tops imms` by
    fs[immutables_initialized_def] >>
  drule_all immutable_decl_bytes_initialized >> strip_tac >>
  rename1 `FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v)` >>
  qpat_x_assum `tops = _`
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule immutables_section_slice >>
  disch_then (qspec_then `imms` assume_tac) >>
  `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre <=
     LENGTH (immutables_section tops imms)` by
    (qpat_x_assum `tops = _` SUBST1_TAC >>
     simp[compute_immutables_len_append, compute_immutables_len_def]) >>
  qpat_x_assum `tops = _` kall_tac >>
  qexistsl [`tv`, `v`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule immutable_encoding_slice_decodes >> asm_rewrite_tac[]) >>
  qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac[GSYM th]) >>
  irule immutable_value_bytes_slice >> asm_rewrite_tac[]
QED

Theorem immutables_section_rel_runtime:
  immutable_section_layout cenv tops /\
  immutables_section_rel tops imms section /\
  ALOOKUP vs.immutables addr = SOME imms /\ ss.vs_data_section = section ==>
  immutables_rel cenv addr NONE F vs ss
Proof
  strip_tac >> simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutable_section_layout _ _`
    (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
  disch_then drule >> strip_tac >>
  drule_all immutables_section_rel_lookup >> gvs[]
QED

Theorem immutables_section_rel_empty[simp]:
  immutables_section_rel [] imms section <=> section = []
Proof
  simp[immutables_section_rel_def, compute_immutables_len_def]
QED

Theorem immutables_section_rel_runtime_fallback:
  immutable_section_layout cenv tops /\
  immutables_section_rel tops
    (case ALOOKUP vs.immutables addr of
       NONE => empty_immutables | SOME imms => imms) section /\
  ss.vs_data_section = section ==>
  immutables_rel cenv addr NONE F vs ss
Proof
  Cases_on `ALOOKUP vs.immutables addr`
  >- simp[immutables_rel_def] >>
  strip_tac >> fs[] >> drule_all immutables_section_rel_runtime >> simp[]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable section relation: " ^ name)
  end) (DB.thms "immutableSectionRel");
