Theory abiEncodeValuesMetadata
Ancestors
  abiEncodeValuesCode abiEncodeValuesLayout abiEncoderChildCode abiTupleEncodeLayout abiDecodeRanges
  exprSimAbiEncodePlanMetadata exprSimUnwrap exprLoweringProps
  externalEntryShape abiEncoderAppend emitHelperProps
  compileEnv fragExec exprLowering context emitHelper venomInst words
  contractABI vyperABI vyperValue list rich_list pair combin

Theorem abi_encode_value_rows_head_total:
  LIST_REL (\row at. abi_embedded_static_size sf (SND row) = abi_member_head_size at)
    rows ats ==>
  SUM (MAP (abi_embedded_static_size sf o SND) rows) = head_lengths ats 0 /\
  abi_static_size sf (TupleT (MAP SND rows)) = head_lengths ats 0
Proof
  `!rs ts. LIST_REL
      (\row at. abi_embedded_static_size sf (SND row) = abi_member_head_size at) rs ts ==>
    MAP (abi_embedded_static_size sf o SND) rs = MAP abi_member_head_size ts` by
    (Induct >> Cases_on `ts` >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `MAP (abi_embedded_static_size sf o SND) rows = MAP abi_member_head_size ats` by metis_tac[] >>
  `abi_static_size sf (TupleT (MAP SND rows)) =
    SUM (MAP (abi_embedded_static_size sf o SND) rows)` by
    (PURE_ONCE_REWRITE_TAC [abi_static_size_def] >>
     simp_tac bool_ss [MAP_MAP_o, abi_embedded_static_size_def, o_DEF]) >>
  simp[head_lengths_acc]
QED

Theorem abi_encode_values_static_cuts:
  compile_abi_encode_value_rows ce dst cursor h [(saved,ty)] st = ((),en) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ fn_has_code st en func ==>
  ?head prepared src ready.
    emit_op ADD [dst; Lit (n2w h)] st = (head,prepared) /\
    unwrap_value ce saved prepared = (src,ready) /\
    compile_store_memory ce src head ty ty ready = ((),en) /\
    ci_mono st prepared /\ ci_mono prepared ready /\ ci_mono ready en /\
    fn_has_code st prepared func /\ fn_has_code prepared ready func /\ fn_has_code ready en func
Proof
  strip_tac >> drule_all abi_encode_value_rows_static_trace >> strip_tac >>
  qpat_x_assum `compile_abi_encode_value_rows _ _ _ _ [] _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_abi_encode_value_rows_def, comp_return_def]) >>
  `ci_mono st prepared /\ ci_mono prepared ready /\ ci_mono ready en` by
    metis_tac[ci_mono_emit_op, ci_mono_unwrap_value, ci_mono_compile_store_memory, SND] >>
  `fn_has_code st prepared func /\ fn_has_code prepared en func` by
    metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
  `fn_has_code prepared ready func /\ fn_has_code ready en func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  qexistsl_tac [`head`,`prepared`,`src`,`ready`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_values_dynamic_cuts:
  compile_abi_encode_value_rows ce dst cursor h [(saved,ty)] st = ((),en) /\
  is_abi_dynamic ce.ce_struct_fields ty /\ fn_has_code st en func ==>
  ?head off tail prepared src ready len encoded.
    abi_encode_child_prefix dst h cursor st = ((head,off,tail),prepared) /\
    unwrap_value ce saved prepared = (src,ready) /\
    compile_abi_encode_to_buf tail src
      (type_to_abi_enc_info ce.ce_struct_fields ce ty) ready = (len,encoded) /\
    abi_encode_child_suffix head cursor off len encoded = (len,en) /\
    ci_mono st prepared /\ ci_mono prepared ready /\
    ci_mono ready encoded /\ ci_mono encoded en /\
    fn_has_code st prepared func /\ fn_has_code prepared ready func /\
    fn_has_code ready encoded func /\ fn_has_code encoded en func
Proof
  strip_tac >> drule_all abi_encode_value_rows_dynamic_trace >> strip_tac >>
  qpat_x_assum `compile_abi_encode_value_rows _ _ _ _ [] _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_abi_encode_value_rows_def, comp_return_def]) >>
  drule abi_encode_child_prefix_shape >> drule abi_encode_child_suffix_shape >> strip_tac >> strip_tac >>
  qpat_x_assum `advanced = en` SUBST_ALL_TAC >>
  `cs_extends st prepared /\ cs_extends encoded en` by
    (map_every (fn args => mp_tac (Q.SPECL args cs_extends_same_block))
       [[`st`,`prepared`],[`encoded`,`en`]] >>
     fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `ci_mono st prepared /\ ci_mono encoded en` by
    (simp[ci_mono_def] >> decide_tac) >>
  `ci_mono prepared ready /\ ci_mono ready encoded` by
    metis_tac[ci_mono_unwrap_value, cj 2 ci_mono_compile_abi_encode, SND] >>
  `fn_has_code st prepared func /\ fn_has_code prepared en func` by
    metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
  `fn_has_code prepared ready func /\ fn_has_code ready en func` by
    metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
  `fn_has_code ready encoded func /\ fn_has_code encoded en func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  qexistsl_tac [`head`,`tail_ofst`,`tail_ptr`,`prepared`,`src`,`ready`,`len`,`encoded`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Index the emitted rows in the original argument vector. This lets a
   caller use its saved row at i through all three compiler cuts. *)
Theorem abi_encode_values_to_buf_indexed:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) /\
  (!cursor a b last.
    emit_op ALLOCA [Lit 32w] st = (cursor,a) /\
    emit_void MSTORE [cursor;Lit (n2w (abi_static_size ce.ce_struct_fields
      (TupleT (MAP SND rows))))] a = ((),b) /\
    compile_abi_encode_value_rows ce dst cursor 0 rows b = ((),last) /\
    emit_op MLOAD [cursor] last = (out,en) ==>
    ?u. row_step st b x u /\ row_inv cursor 0 b u) /\
  (!cursor i a b last u.
    i < LENGTH rows /\ row_inv cursor i a u /\
    compile_abi_encode_value_rows ce dst cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),b) /\
    compile_abi_encode_value_rows ce dst cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE (SUC i) rows)))
      (DROP (SUC i) rows) b = ((),last) /\
    emit_op MLOAD [cursor] last = (out,en) ==>
    ?v. row_step a b u v /\ row_inv cursor (SUC i) b v) /\
  (!cursor a u.
    row_inv cursor (LENGTH rows) a u /\ emit_op MLOAD [cursor] a = (out,en) ==>
    ?v. row_step a en u v /\ Q out v) /\
  (!a u. row_step a a u u) /\
  (!a b c u v z. row_step a b u v /\ row_step b c v z ==> row_step a c u z) ==>
  ?y. row_step st en x y /\ Q out y
Proof
  strip_tac >>
  mp_tac (Q.INST [`P` |-> `\cursor h rest a u.
    ?i. i <= LENGTH rows /\ rest = DROP i rows /\
      h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)) /\
      (row_inv: operand -> num -> compile_state -> 'a -> bool) cursor i a u`]
    abi_encode_values_to_buf_ind) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!cursor a b last. emit_op ALLOCA _ _ = _ /\ _ ==> _`
            (drule_all_then strip_assume_tac) >>
          qexists_tac `u` >> asm_rewrite_tac[] >>
          qexists_tac `0` >> simp[])
      >- (rpt gen_tac >> strip_tac >>
          `DROP i rows <> []` by metis_tac[NOT_CONS_NIL] >>
          `i < LENGTH rows` by (fs[DROP_EQ_NIL] >> decide_tac) >>
          `EL i rows = (vv,ty) /\ rest = DROP (SUC i) rows` by
            (qpat_assum `_ = DROP i rows` mp_tac >>
             drule_then (fn th => PURE_REWRITE_TAC [th]) DROP_EL_CONS >>
             simp[arithmeticTheory.ADD1]) >>
          `TAKE (SUC i) rows = TAKE i rows ++ [EL i rows]` by
            simp[TAKE_SUC, TAKE1_DROP] >>
          `SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE (SUC i) rows)) =
            h + abi_embedded_static_size ce.ce_struct_fields ty` by
            asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, o_THM, SND, arithmeticTheory.ADD_0] >>
          qpat_assum `!cursor i a b last u. i < LENGTH rows /\ _ ==> _`
            (qspecl_then [`cursor`,`i`,`a`,`b`,`last`,`u`] mp_tac) >>
          impl_tac
          >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
              >- (qpat_assum `EL i rows = (vv,ty)` (fn el =>
                    qpat_assum `h = SUM _` (fn off =>
                      PURE_REWRITE_TAC [el, GSYM off])) >>
                  first_assum ACCEPT_TAC) >>
              qpat_assum `SUM (MAP _ (TAKE (SUC i) rows)) = _` (fn sum_eq =>
                qpat_assum `rest = DROP (SUC i) rows` (fn rest_eq =>
                  PURE_REWRITE_TAC [sum_eq, GSYM rest_eq])) >>
              first_assum ACCEPT_TAC) >>
          strip_tac >> qexists_tac `v` >> asm_rewrite_tac[] >>
          qexists_tac `SUC i` >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      `DROP i rows = []` by metis_tac[] >>
      `i = LENGTH rows` by (fs[DROP_EQ_NIL] >> decide_tac) >>
      metis_tac[]) >>
  disch_then ACCEPT_TAC
QED

(* This instantiates the prefix bounds at the same index as the saved
   operand package. Both lengths use the ABI member layouts. *)
Theorem abi_encode_values_index_bounds:
  LIST_REL (\row at. abi_embedded_static_size sf (SND row) = abi_member_head_size at)
    rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\ i < LENGTH rows /\
  h = SUM (MAP (abi_embedded_static_size sf o SND) (TAKE i rows)) /\
  hl = head_lengths ats 0 /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  n = LENGTH (enc (Tuple ats) (ListV avs)) /\
  at = EL i ats /\ av = EL i avs ==>
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  hl <= off /\ off <= n /\ h + abi_member_head_size at <= hl /\
  (is_dynamic at ==> off + LENGTH (enc at av) <= n) /\
  (~is_dynamic at ==> LENGTH (enc at av) = abi_member_head_size at) /\
  abi_encoder_layout_valid at av /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH rows = LENGTH ats /\ LENGTH ats = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `i < LENGTH ats /\ i < LENGTH avs` by decide_tac >>
  `LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    metis_tac[LIST_REL_TAKE] >>
  `abi_encoder_layout_valid at av` by
    (qpat_assum `LIST_REL _ ats avs` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[]) >>
  `h = SUM (MAP abi_member_head_size (TAKE i ats))` by
    (qpat_assum `LIST_REL _ rows ats` (mp_tac o MATCH_MP LIST_REL_TAKE) >>
     disch_then (qspec_then `i` (mp_tac o MATCH_MP abi_encode_value_rows_head_total)) >>
     simp[head_lengths_acc]) >>
  `ats = TAKE i ats ++ at::DROP (SUC i) ats /\
    avs = TAKE i avs ++ av::DROP (SUC i) avs` by
    (conj_tac
     >- (`DROP i ats = at::DROP (SUC i) ats` by
           (qpat_assum `i < LENGTH ats` (mp_tac o MATCH_MP DROP_EL_CONS) >>
            asm_rewrite_tac[arithmeticTheory.ADD1]) >>
         qpat_assum `DROP i ats = _` (SUBST1_TAC o SYM) >> simp[])
     >- (`DROP i avs = av::DROP (SUC i) avs` by
           (qpat_assum `i < LENGTH avs` (mp_tac o MATCH_MP DROP_EL_CONS) >>
            asm_rewrite_tac[arithmeticTheory.ADD1]) >>
         qpat_assum `DROP i avs = _` (SUBST1_TAC o SYM) >> simp[])) >>
  mp_tac (Q.INST [`pre` |-> `TAKE i ats`, `pvs` |-> `TAKE i avs`,
    `ty` |-> `at`, `v` |-> `av`, `post` |-> `DROP (SUC i) ats`,
    `rest` |-> `DROP (SUC i) avs`, `ho` |-> `h`]
    abi_encode_values_member_bounds) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_assum `ats = TAKE i ats ++ _` (fn a =>
      qpat_assum `avs = TAKE i avs ++ _` (fn b =>
        PURE_REWRITE_TAC [GSYM a, GSYM b])) >>
    simp[abiCanonicalWindowsTheory.abi_tuple_tails_length, LENGTH_TAKE_EQ]) >>
  simp[]
QED
