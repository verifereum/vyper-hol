(* Block history and label boundaries for expression helper traversals. *)
Theory bodyIntCallExprLabels
Ancestors
  bodyIntCallMaterialLabels bodyIntCallLabelFrame bodyIntCallContextLabels
  bodyIntCallLabelReservations exprLowering compileEnv list pred_set

Theorem compiler_block_tail_unwrap_value:
  compiler_block_tail (unwrap_value cenv vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, compiler_block_tail_primitives] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >>
  simp[compiler_block_tail_primitives] >> Cases_on `p.ptr_location` >>
  simp[compiler_block_tail_primitives, compiler_block_tail_ensure_in_memory]
QED

Theorem unwrap_value_label_bounds:
  unwrap_value cenv vv st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, comp_return_def]
  >- (rpt strip_tac >> gvs[]) >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >> simp[]
  >- (strip_tac >> drule_all compile_ptr_load_label_bounds >> simp[]) >>
  Cases_on `p.ptr_location` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all compile_ensure_in_memory_label_bounds >> simp[]
QED

Theorem compiler_block_tail_lower_value:
  compiler_block_tail (cfn cenv ty e) ==>
  compiler_block_tail (lower_value cfn cenv ty e)
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_unwrap_value]
QED

Theorem compiler_label_hoare_unwrap_value:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (unwrap_value cenv vv) (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[unwrap_value_label_bounds]
QED

Theorem compiler_label_hoare_lower_value:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (lower_value cfn cenv ty e) (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_unwrap_value]
QED

Theorem compiler_block_tail_multi_vvs:
  !es. EVERY (\e. compiler_block_tail (cfn cenv (expr_type e) e)) es ==>
  compiler_block_tail (compile_multi_vvs cfn cenv es)
Proof
  Induct >> simp[compile_multi_vvs_def, compiler_block_tail_primitives] >> rpt strip_tac >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_multi_vvs:
  !es. EVERY (\e. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type e) e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_multi_vvs cfn cenv es) (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- simp[compile_multi_vvs_def, compiler_label_hoare_def, comp_return_def] >>
  gen_tac >> simp[compile_multi_vvs_def] >> strip_tac >> ntac 2 gen_tac >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[] >> simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_block_tail_multi_exprs:
  !es. EVERY (\e. compiler_block_tail (cfn cenv (expr_type e) e)) es ==>
  compiler_block_tail (compile_multi_exprs cfn cenv es)
Proof
  Induct >> simp[compile_multi_exprs_def, compiler_block_tail_primitives] >> rpt strip_tac >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_multi_exprs:
  !es. EVERY (\e. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type e) e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_multi_exprs cfn cenv es) (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- simp[compile_multi_exprs_def, compiler_label_hoare_def, comp_return_def] >>
  gen_tac >> simp[compile_multi_exprs_def] >> strip_tac >> ntac 2 gen_tac >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[] >> simp[compiler_label_hoare_def, comp_return_def]
QED

Theorem compiler_block_tail_make_tuple:
  !es off. EVERY (\e. compiler_block_tail (cfn cenv (expr_type e) e)) es ==>
  compiler_block_tail (compile_make_tuple cfn cenv es buf off)
Proof
  Induct >> simp[compile_make_tuple_def, comp_ignore_bind_def, compiler_block_tail_primitives] >> rpt strip_tac >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_unwrap_value,
               compiler_block_tail_store_memory] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_label_hoare_store_memory:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_store_memory cenv v dst ty src_ty)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_store_memory_label_bounds]
QED

Theorem compiler_label_hoare_make_tuple:
  !es off. EVERY (\e. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type e) e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_make_tuple cfn cenv es buf off) (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- simp[compile_make_tuple_def, compiler_label_hoare_def, comp_return_def] >>
  ntac 2 gen_tac >> simp[compile_make_tuple_def, comp_ignore_bind_def] >>
  strip_tac >> ntac 2 gen_tac >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_unwrap_value,
               compiler_label_hoare_typed_primitives, compiler_label_hoare_store_memory] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_block_tail_make_array_elems:
  !es idx. EVERY (\e. compiler_block_tail (cfn cenv (expr_type e) e)) es ==>
  compiler_block_tail (compile_make_array_elems cfn cenv es ty sz has_len buf idx)
Proof
  Induct >> simp[compile_make_array_elems_def, comp_ignore_bind_def,
                 compiler_block_tail_primitives] >> rpt strip_tac >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_unwrap_value,
               compiler_block_tail_store_memory] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_label_hoare_make_array_elems:
  !es idx. EVERY (\e. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type e) e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_make_array_elems cfn cenv es ty sz has_len buf idx)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- simp[compile_make_array_elems_def, compiler_label_hoare_def, comp_return_def] >>
  ntac 2 gen_tac >> simp[compile_make_array_elems_def, comp_ignore_bind_def] >>
  strip_tac >> ntac 2 gen_tac >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_unwrap_value,
               compiler_label_hoare_typed_primitives, compiler_label_hoare_store_memory] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_block_tail_make_array:
  EVERY (\e. compiler_block_tail (cfn cenv (expr_type e) e)) es ==>
  compiler_block_tail (compile_make_array cfn cenv es ty sz has_len buf)
Proof
  strip_tac >> rewrite_tac[compile_make_array_def, comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `has_len` >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_make_array_elems >> simp[]
QED

Theorem compiler_label_hoare_make_array:
  EVERY (\e. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type e) e) (\r out. compiler_label_reservation origin pending out)) es ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_make_array cfn cenv es ty sz has_len buf)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_make_array_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `has_len` >> simp[compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_make_array_elems >> simp[]
QED

Theorem compiler_block_tail_lower_value_with_loc:
  compiler_block_tail (cfn cenv ty e) ==>
  compiler_block_tail (lower_value_with_loc cfn cenv ty e)
Proof
  strip_tac >> rewrite_tac[lower_value_with_loc_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_unwrap_value, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_lower_value_with_loc:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (lower_value_with_loc cfn cenv ty e) (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lower_value_with_loc_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_unwrap_value, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_store_abi_tuple:
  !vs off. compiler_block_tail (compile_store_abi_tuple cenv buf off vs)
Proof
  Induct >> simp[compile_store_abi_tuple_def, compiler_block_tail_primitives] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `is_word_type h1` >>
      simp[compiler_block_tail_primitives, compiler_block_tail_copy_memory]) >>
  simp[]
QED

Theorem compiler_label_hoare_store_abi_tuple:
  !vs off. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_store_abi_tuple cenv buf off vs) (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_store_abi_tuple_def, compiler_label_hoare_typed_primitives] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `is_word_type h1` >> simp[compiler_label_hoare_typed_primitives]) >>
  simp[]
QED

Theorem compiler_block_tail_struct_lit:
  !fields off. EVERY (\fe. compiler_block_tail
    (cfn cenv (expr_type (SND fe)) (SND fe))) fields ==>
  compiler_block_tail (compile_struct_lit cfn cenv ty fields buf off)
Proof
  Induct >> simp[compile_struct_lit_def, compiler_block_tail_primitives] >>
  ntac 2 gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
  simp[compile_struct_lit_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_unwrap_value,
               compiler_block_tail_store_memory] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_label_hoare_struct_lit:
  !fields off. EVERY (\fe. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type (SND fe)) (SND fe))
      (\r out. compiler_label_reservation origin pending out)) fields ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_struct_lit cfn cenv ty fields buf off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_struct_lit_def, compiler_label_hoare_typed_primitives] >>
  ntac 2 gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >> ntac 2 gen_tac >>
  simp[compile_struct_lit_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_unwrap_value,
               compiler_label_hoare_store_memory] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_block_tail_concat:
  !es infos off. EVERY (\e. compiler_block_tail (cfn cenv (expr_type e) e)) es ==>
  compiler_block_tail (compile_concat cfn cenv es dst infos off)
Proof
  Induct >> simp[compile_concat_def, compiler_block_tail_primitives] >>
  ntac 3 gen_tac >> Cases_on `infos` >>
  simp[compile_concat_def, compiler_block_tail_primitives] >>
  PairCases_on `h'` >> Cases_on `h'0` >>
  simp[compile_concat_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_lower_value] >>
       gen_tac >> BETA_TAC) >> first_x_assum irule >> simp[]
QED

Theorem compiler_label_hoare_concat:
  !es infos off. EVERY (\e. !origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv (expr_type e) e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_concat cfn cenv es dst infos off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_concat_def, compiler_label_hoare_typed_primitives] >>
  ntac 3 gen_tac >> Cases_on `infos` >>
  simp[compile_concat_def, compiler_label_hoare_typed_primitives] >>
  PairCases_on `h'` >> Cases_on `h'0` >>
  simp[compile_concat_def, comp_ignore_bind_def] >> strip_tac >> ntac 2 gen_tac >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
               compiler_label_hoare_lower_value] >> gen_tac >> BETA_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_block_tail_store_byte_chunks:
  !dst bs off. compiler_block_tail (compile_store_byte_chunks dst bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_store_byte_chunks_def] >>
  simp[comp_ignore_bind_def, compiler_block_tail_primitives] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  first_x_assum mp_tac >> simp[]
QED

Theorem compiler_label_hoare_store_byte_chunks:
  !dst bs off. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_store_byte_chunks dst bs off) (\r out. compiler_label_reservation origin pending out)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_store_byte_chunks_def] >>
  simp[comp_ignore_bind_def, compiler_label_hoare_typed_primitives] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >> first_x_assum mp_tac >> simp[]
QED

Theorem compiler_block_tail_bytelike_literal:
  compiler_block_tail (compile_bytelike_literal bs n)
Proof
  simp[compile_bytelike_literal_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_store_byte_chunks] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_bytelike_literal:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_bytelike_literal bs n) (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_bytelike_literal_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_store_byte_chunks,
               compiler_label_hoare_storage_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_literal_vv:
  compiler_block_tail (compile_literal_vv ty lit)
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, compiler_block_tail_primitives]
  >- (Cases_on `b` >> simp[compile_literal_vv_def, compiler_block_tail_primitives])
  >- (Cases_on `ty` >> simp[] >>
      irule compiler_block_tail_bind >>
      simp[compiler_block_tail_bytelike_literal, compiler_block_tail_primitives]) >>
  Cases_on `ty` >> simp[compiler_block_tail_primitives] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compiler_block_tail_primitives] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_bytelike_literal, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_literal_vv:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_literal_vv ty lit) (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, compiler_label_hoare_typed_primitives]
  >- (Cases_on `b` >> simp[compile_literal_vv_def, compiler_label_hoare_typed_primitives])
  >- (Cases_on `ty` >> simp[] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_bytelike_literal, compiler_label_hoare_typed_primitives]) >>
  Cases_on `ty` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_bytelike_literal, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_name_vv:
  compiler_block_tail (compile_name_vv cenv ty name)
Proof
  rewrite_tac[compile_name_vv_def] >> Cases_on `FLOOKUP cenv.ce_vars name` >>
  simp[comp_ignore_bind_def, compiler_block_tail_primitives]
  >- (irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >> Cases_on `loc` >>
  simp[comp_ignore_bind_def, compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_name_vv:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_name_vv cenv ty name) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_name_vv_def] >> Cases_on `FLOOKUP cenv.ce_vars name` >>
  simp[comp_ignore_bind_def, compiler_label_hoare_typed_primitives]
  >- (irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >> Cases_on `loc` >>
  simp[comp_ignore_bind_def, compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_clamp:
  compiler_block_tail (compile_clamp v ty)
Proof
  rewrite_tac[compile_clamp_def] >> Cases_on `type_bounds ty` >> simp[] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_clamp:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_clamp v ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_clamp_def] >> Cases_on `type_bounds ty` >> simp[] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_clamp_and_return:
  compiler_block_tail (clamp_and_return v ty)
Proof
  rewrite_tac[clamp_and_return_def, comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_clamp, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_clamp_and_return:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (clamp_and_return v ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[clamp_and_return_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_clamp, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_safe_add:
  compiler_block_tail (compile_safe_add x y ty)
Proof
  rewrite_tac[compile_safe_add_def, LET_THM] >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  Cases_on `type_bits ty < 256` >> simp[compiler_block_tail_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_safe_add:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_add x y ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_add_def, LET_THM] >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
  Cases_on `type_bits ty < 256` >> simp[compiler_label_hoare_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_typed_primitives]
QED
