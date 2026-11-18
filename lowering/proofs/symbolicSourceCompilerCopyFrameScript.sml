Theory symbolicSourceCompilerCopyFrame
Ancestors symbolicSourceCompilerFrame context

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
  >- (Cases_on `type_memory_bytes cenv dt = type_memory_bytes cenv st /\ ~is_abi_dynamic cenv.ce_struct_fields dt` >> gvs[] >> disj2_tac >>
      rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
      simp[] >> metis_tac[])
  >- (IF_CASES_TAC >> gvs[] >>
      rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]) >>
  pairarg_tac >> gvs[] >>
  rpt (irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED
