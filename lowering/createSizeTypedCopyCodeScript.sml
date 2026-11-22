(* Branch confinement for the layout-changing memory-store family. *)
Theory createSizeTypedCopyCode
Ancestors
  createSizeDynarrayCopyCode createSizeSarrayCopyCode createSizeCutCode createSizeCutOpens
  context compileEnv emitHelper venomInst pair alist

fun typed_copy_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_op,
                  create_cut_code_emit_void, create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac]);

val _ = augment_srw_ss [rewrites [create_cut_copy_memory]];

Theorem create_copy_byte_offset[local,simp]:
  create_cut_code {} a (SND (compile_with_byte_offset base_op off a))
Proof
  Cases_on `off = 0` >> typed_copy_steps [compile_with_byte_offset_def]
QED

Theorem create_store_bytestring_code[local,simp]:
  create_cut_code {} a (SND (compile_store_bytestring src dst a))
Proof
  typed_copy_steps [compile_store_bytestring_def, compile_bytestring_copy_len_def]
QED

Theorem create_typed_copy_family:
  (!ce dst dt src st a.
    create_cut_code {} a (SND (compile_store_memory_typed ce dst dt src st a))) /\
  (!ce dst src dts sts doff soff a.
    create_cut_code {} a
      (SND (compile_typed_copy_fields ce dst src dts sts doff soff a))) /\
  (!ce dst dt src st n a.
    create_cut_code {} a (SND (compile_copy_sarray_typed ce dst dt src st n a))) /\
  (!ce dst dt cap src st a.
    create_cut_code {} a (SND (compile_copy_dynarray_typed ce dst dt cap src st a))) /\
  (!ce dst src dfs sfs doff soff a.
    create_cut_code {} a
      (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff a)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def]
  >- simp[Once compile_store_memory_typed_def]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def]
  >> suspend "struct"
QED

Resume create_typed_copy_family[dispatch]:
  rpt strip_tac >> pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `is_word_type dt` >- typed_copy_steps [] >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st` >- simp[] >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (simp[] >> Cases_on `dt` >> Cases_on `st` >> gvs[] >>
      rename1 `~is_word_type (ArrayT _ dst_bound)` >>
      Cases_on `dst_bound` >>
      qmatch_goalsub_rename_tac `case src_bound of Fixed _ => _ | Dynamic _ => _` >>
      Cases_on `src_bound` >> gvs[]) >>
  typed_copy_steps []
QED

Resume create_typed_copy_family[fields]:
  rpt strip_tac >> pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  typed_copy_steps []
QED

Resume create_typed_copy_family[sarray]:
  rpt strip_tac >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\
            ~is_abi_dynamic ce.ce_struct_fields dt`
  >- simp[Once compile_store_memory_typed_def] >>
  irule create_sarray_copy_case >> gvs[]
QED

Resume create_typed_copy_family[dynarray]:
  rpt strip_tac >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st`
  >- (simp[Once compile_store_memory_typed_def] >>
      typed_copy_steps [compile_copy_memory_dynamic_def]) >>
  irule create_dynarray_copy_case >> gvs[]
QED

Resume create_typed_copy_family[struct]:
  rpt strip_tac >> pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name`
  >- (gvs[] >> typed_copy_steps []) >>
  qmatch_goalsub_rename_tac `SOME source_field_pair` >>
  PairCases_on `source_field_pair` >>
  gvs[] >> typed_copy_steps []
QED

Finalise create_typed_copy_family[local]

Theorem create_store_memory_typed_cut_code:
  create_cut_code {} a (SND (compile_store_memory_typed ce dst dt src st a))
Proof
  simp[create_typed_copy_family]
QED

Theorem create_store_memory_cut_code:
  create_cut_code {} a (SND (compile_store_memory ce src dst dt st a))
Proof
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[create_cut_code_emit_void, create_cut_targets_def,
       create_store_memory_typed_cut_code]
QED
