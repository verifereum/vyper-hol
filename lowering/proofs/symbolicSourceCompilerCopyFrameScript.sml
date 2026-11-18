Theory symbolicSourceCompilerCopyFrame
Ancestors symbolicSourceCompilerFrame compileEnv context

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

Theorem symbolic_frame_typed_copy_mutual:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!op args outs. symbolic_frame R (emit_inst op args outs)) /\
  symbolic_frame R fresh_var /\
  (!name. symbolic_frame R (fresh_label name)) /\
  (!name. symbolic_frame R (new_block name)) /\
  (!src dst. symbolic_frame R (compile_store_bytestring src dst)) /\
  (!dst src n. symbolic_frame R (compile_copy_memory dst src n)) /\
  (!dst src n. symbolic_frame R (compile_copy_memory_dynamic dst src n)) /\
  (!p n. symbolic_frame R (compile_with_byte_offset p n)) ==>
  (!cenv dst dt src st. symbolic_frame R (compile_store_memory_typed cenv dst dt src st)) /\
  (!cenv dst src dts sts doff soff. symbolic_frame R (compile_typed_copy_fields cenv dst src dts sts doff soff)) /\
  (!cenv dst dt src st n. symbolic_frame R (compile_copy_sarray_typed cenv dst dt src st n)) /\
  (!cenv dst dt cap src st. symbolic_frame R (compile_copy_dynarray_typed cenv dst dt cap src st)) /\
  (!cenv dst src dfs sfs doff soff. symbolic_frame R (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  strip_tac >> ho_match_mp_tac compile_store_memory_typed_ind >> rpt strip_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  rpt (CHANGED_TAC (simp[comp_ignore_bind_def])) >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC)
  >- (Cases_on `is_word_type dt` >> gvs[] >>
      Cases_on `is_bytestring_type dt /\ is_bytestring_type st` >> gvs[] >>
      Cases_on `acyclic_struct_metadata cenv.ce_struct_fields` >> gvs[] >>
      Cases_on `dt` >> Cases_on `st` >> gvs[] >>
      rpt (CASE_TAC >> gvs[]) >> metis_tac[])
  >- (IF_CASES_TAC >> gvs[] >>
      rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
      simp[])
  >- (IF_CASES_TAC >> gvs[] >>
      rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]) >>
  pairarg_tac >> gvs[] >>
  rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_store_slots:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!op args outs. symbolic_frame R (emit_inst op args outs)) /\
  symbolic_frame R fresh_var /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!p n. symbolic_frame R (compile_lit_byte_offset p n)) /\
  (!p. symbolic_frame R (compile_bytestring_word_count p)) /\
  (!src dst n. symbolic_frame R (compile_memory_to_storage src dst n)) /\
  (!src dst n. symbolic_frame R (compile_memory_to_transient src dst n)) /\
  (!src dst n sl dl ctor mb. symbolic_frame R (compile_word_copy_loop_base src dst n sl dl ctor mb)) ==>
  (!cenv src slot ty trans.
    symbolic_frame R (compile_store_slots cenv src slot ty trans)) /\
  (!cenv src slot members mo so trans.
    symbolic_frame R (compile_store_slots_members cenv src slot members mo so trans)) /\
  (!cenv src slot elem count trans.
    symbolic_frame R (compile_copy_elements_to_slots cenv src slot elem count trans))
Proof
  strip_tac >>
  ho_match_mp_tac compile_store_slots_ind >> rpt strip_tac >>
  simp[Once compile_store_slots_def, comp_ignore_bind_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[compile_word_copy_loop_op_def] >>
  rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt (CASE_TAC >> gvs[]) >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields` >> gvs[] >>
  rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_iload_memory[simp]:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) ==>
  !n. symbolic_frame R (compile_iload_to_memory src dst n)
Proof
  strip_tac >>
  Induct >> simp[compile_iload_to_memory_def]
QED

Theorem symbolic_frame_gep_memory[simp]:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) ==>
  !n. symbolic_frame R (compile_gep_to_memory bp src dst n)
Proof
  strip_tac >>
  Induct >> simp[compile_gep_to_memory_def, comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_load_immutable_ctor[simp]:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_load_immutable_ctor off b wc n imm)
Proof
  strip_tac >>
  Cases_on `imm` >> Cases_on `b` >>
  simp[compile_load_immutable_ctor_def, comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED
