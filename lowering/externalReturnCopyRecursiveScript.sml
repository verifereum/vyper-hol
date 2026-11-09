(* Rank assembly for task-owned, footprint-sensitive typed copying. *)
Theory externalReturnCopyRecursive
Ancestors
  externalReturnCopyAdapter externalReturnCopyFields externalReturnCopyLayout
  externalReturnCopyArrays externalReturnCopyBulk externalReturnCopyFrame
  context compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  venomExecSemantics venomState venomInst words arithmetic
  immutableMemoryFrame valueEncoding valueEncodingProps valueEncodingProofs valueCopy
  vyperTypeSystem vyperTyping vyperValue entryDecodeProps finite_map list pair
  structFieldsProps vyperTypeABI vyperTypeExprSoundness typedCopyDomain

Theorem return_copy_word_run_seq[local]:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n d) (mload (w2n a) s)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s) s))
Proof
  strip_tac >>
  `!w. eval_operand dst
       (update_var (STRING #"%" (toString sa.cs_next_var)) w s) = SOME d` by
    (Cases_on `dst` >> gvs[eval_operand_def, update_var_def, lookup_var_def] >>
     rpt strip_tac >>
     `s' <> STRING #"%" (toString sa.cs_next_var)` by
       (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
     simp[FLOOKUP_UPDATE]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[eval_operand_def, exec_read1_def, exec_write2_def, lookup_var_update_var]
QED

Theorem return_copy_word_raw_frag[local]:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = (mstore (w2n d) (mload (w2n a) s0)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s0) s0))
      with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F)
Proof
  strip_tac >> drule_all return_copy_word_run_seq >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[]
QED

Theorem return_copy_word_frame[local]:
  return_copy_frame sa dst 32 s
    ((mstore dst w (update_var (STRING #"%" (toString sa.cs_next_var)) w s))
      with vs_inst_idx := idx)
Proof
  simp[return_copy_frame_def] >> conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def, update_var_def,
          venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
      simp[mstore_def, write_memory_with_expansion_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE]) >>
  `(mstore dst w (update_var (STRING #"%" (toString sa.cs_next_var)) w s)).vs_memory =
   (mstore dst w s).vs_memory` by simp[mstore_def, update_var_def] >>
  simp[return_copy_memory_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[immutable_mstore_capacity, update_var_def, MAX_DEF]
QED

Theorem return_copy_word_frag:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  mem_word_at (w2n a) s0.vs_memory = typed_val_to_w256 tv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         return_copy_frame sa (w2n d) (type_memory_size tv) s0 t) (\r. F)
Proof
  strip_tac >> drule_all return_copy_word_raw_frag >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >> simp[] >>
  conj_tac
  >- (drule_all exprSimPropsTheory.val_in_memory_word >> strip_tac >>
      simp[mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  simp[return_copy_word_frame]
QED

Theorem return_copy_word_layout[local]:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  type_memory_size tv = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def]
  >~ [`FlagT`]
  >- (rw[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[type_memory_size_def]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, evaluate_type_def, type_memory_size_def] >>
  rpt strip_tac >> gvs[type_memory_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Theorem return_copy_word_entry:
  is_word_type dty ==> return_copy_entry cenv ctx tenv dty sty dtv stv v
Proof
  rw[return_copy_entry_def] >>
  `sty = dty` by metis_tac[type_widens_to_word] >> gvs[] >>
  `type_memory_size dtv = 32` by metis_tac[return_copy_word_layout] >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[exprSimPropsTheory.val_in_memory_word] >>
  drule_all return_copy_word_frag >> simp[]
QED

Theorem return_recursive_bytes_widen_shape[local]:
  type_widens_to tenv (BaseT (BytesT (Dynamic n))) dty ==>
  ?m. dty = BaseT (BytesT (Dynamic m))
Proof
  Cases_on `dty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[arg_type_fits_def] >>
  qmatch_goalsub_rename_tac `arg_type_fits _ (BaseT (BytesT bd))` >>
  Cases_on `bd` >> simp[arg_type_fits_def]
QED

Theorem return_recursive_string_widen_shape[local]:
  type_widens_to tenv (BaseT (StringT n)) dty ==>
  ?m. dty = BaseT (StringT m)
Proof
  Cases_on `dty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[arg_type_fits_def]
QED

Theorem return_copy_bytestring_entry:
  is_bytestring_type dty ==> return_copy_entry cenv ctx tenv dty sty dtv stv v
Proof
  rw[return_copy_entry_def] >>
  `is_bytestring_type sty` by
    metis_tac[type_widens_to_def, arg_type_fits_bytestring_source] >>
  Cases_on `sty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >- (drule return_recursive_string_widen_shape >> strip_tac >> gvs[] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      irule return_copy_string >>
      qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
      simp[]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
  drule return_recursive_bytes_widen_shape >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  irule return_copy_dynamic_bytes >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >> simp[]
QED

Theorem return_copy_struct_size_list[local]:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(name, ty, sz). !tv. evaluate_type tenv ty = SOME tv ==>
                                  sz = type_memory_size tv) fields ==>
    SUM (MAP (SND o SND) fields) = type_memory_size_list tvs
Proof
  Induct >> simp[type_memory_size_def] >>
  Cases >> rename1 `(name, info)` >> Cases_on `info` >>
  simp[type_memory_size_def] >> rpt strip_tac >> gvs[type_memory_size_def]
QED

Theorem return_copy_struct_size_zip[local]:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_memory_size_fields (ZIP (names, tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED

Theorem return_copy_memory_size:
  !cenv ty tenv tv.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv
Proof
  ho_match_mp_tac type_memory_bytes_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def, type_memory_size_def] >>
      qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
      simp[sfields_tenv_consistent_def] >> strip_tac >>
      qpat_x_assum `!nsid args. _` drule >> strip_tac >>
      gvs[get_struct_fields_def, evaluate_types_OPT_MMAP] >>
      `LENGTH tvs = LENGTH (MAP FST args)` by
        (drule OPT_MMAP_LENGTH >> simp[]) >>
      simp[return_copy_struct_size_zip] >>
      irule return_copy_struct_size_list >>
      qexists_tac `tenv \\ nsid` >> conj_tac >- gvs[] >>
      qpat_x_assum `!name fields. _ ==> EVERY _ _` drule >>
      simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
      drule (cj 1 evaluate_type_mono) >> metis_tac[])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
          type_memory_size_def, evaluate_types_OPT_MMAP] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule tuple_memory_bytes_size >>
      qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
      type_memory_size_def, vfmConstantsTheory.word_size_def] >> metis_tac[]
QED

Theorem return_copy_none_entry:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  return_copy_entry cenv ctx tenv NoneT sty dtv stv v
Proof
  rw[return_copy_entry_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> gvs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[evaluate_type_def, value_has_type_def] >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  irule frag_exec_refl >> simp[val_in_memory_def]
QED

Theorem return_copy_array_widening[local]:
  type_widens_to tenv (ArrayT se sb) (ArrayT de db) ==>
  (se = de \/ arg_type_fits se de) /\
  ((?n m. sb = Dynamic n /\ db = Dynamic m /\ n <= m) \/
   (?n. sb = Fixed n /\ db = Fixed n))
Proof
  Cases_on `sb` >> Cases_on `db` >>
  rw[type_widens_to_def, arg_type_fits_def] >> simp[arg_type_fits_def]
QED

Theorem return_copy_array_source[local]:
  type_widens_to tenv sty (ArrayT de db) ==>
  ?se sb. sty = ArrayT se sb
Proof
  Cases_on `sty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  Cases_on `b` >> Cases_on `db` >> simp[arg_type_fits_def] >> metis_tac[]
QED

Theorem return_copy_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      return_copy_entry cenv ctx tenv cd cs cdt cst cv) ==>
    return_copy_entry cenv ctx tenv (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all return_copy_array_source >> strip_tac >> gvs[] >>
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule return_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule return_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH l ==> return_copy_entry cenv ctx tenv de se tv' tv (EL i l)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once type_rank_def] >>
     gvs[return_copy_dynarray_wf, vyperTypingTheory.all_have_type_EVERY,
         EVERY_EL]) >>
  simp[return_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule return_copy_dynarray_frag >>
  qpat_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sw`, `tv`, `scap`] >> simp[type_memory_size_def] >>
  (conj_tac >- gvs[type_memory_size_def, ADD_COMM]) >>
  (conj_tac >-
    (rpt strip_tac >> irule return_copy_entry_actual_footprint >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     qexists_tac `tenv` >> simp[] >>
     gvs[return_copy_dynarray_wf, vyperTypingTheory.all_have_type_EVERY, EVERY_EL])) >>
  reverse conj_tac >- (strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `val_footprint tv (EL i l) <= type_memory_size tv` by
    (irule externalReturnCopyTransportTheory.return_footprint_le_layout >>
     gvs[return_copy_dynarray_wf, EVERY_EL]) >>
  `i < scap` by decide_tac >>
  `i * type_memory_size tv + type_memory_size tv <= scap * type_memory_size tv` by
    (`SUC i <= scap` by decide_tac >>
     qpat_x_assum `SUC i <= scap` mp_tac >>
     disch_then (mp_tac o Q.SPEC `type_memory_size tv` o MATCH_MP LESS_MONO_MULT) >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  gvs[type_memory_size_def] >> decide_tac
QED

Theorem return_copy_sarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      return_copy_entry cenv ctx tenv cd cs cdt cst cv) ==>
    return_copy_entry cenv ctx tenv (ArrayT de (Fixed cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all return_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule return_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule return_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by metis_tac[return_copy_default_widening] >>
  `!i. i < cap ==> return_copy_entry cenv ctx tenv de se tv' tv
      (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (rpt strip_tac >> first_x_assum irule >> simp[Once type_rank_def] >>
     `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (irule return_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule return_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[vyperTypingTheory.default_value_well_typed,
                 cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  simp[return_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule return_copy_at_start >> strip_tac >>
  irule return_copy_sarray_frag >>
  qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`tenv`, `sw`, `tv`,
    `\i. case ALOOKUP l i of NONE => default_value tv | SOME v => v`] >>
  simp[type_memory_size_def] >>
  (conj_tac >- gvs[type_memory_size_def, ADD_COMM]) >>
  (conj_tac >-
    (rpt strip_tac >> irule return_copy_entry_actual_footprint >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     qexists_tac `tenv` >> simp[] >>
     qpat_x_assum `!i. i < cap ==> return_copy_entry _ _ _ _ _ _ _ _`
       (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule return_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[vyperTypingTheory.default_value_well_typed,
                 cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup])) >>
  rpt strip_tac >>
  `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (irule return_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
  drule externalReturnCopyTransportTheory.return_footprint_le_layout >> strip_tac >>
  `i * type_memory_size tv + type_memory_size tv <= cap * type_memory_size tv` by
    (`SUC i <= cap` by decide_tac >>
     qpat_x_assum `SUC i <= cap` mp_tac >>
     disch_then (mp_tac o Q.SPEC `type_memory_size tv` o MATCH_MP LESS_MONO_MULT) >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  gvs[type_memory_size_def] >> decide_tac
QED

Theorem return_copy_entries_from_semantics[local]:
  !dtys stys dtvs stvs vs.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) stys dtys /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    (!cd cs cdt cst cv. MEM cd dtys ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      return_copy_entry cenv ctx tenv cd cs cdt cst cv) ==>
    return_copy_entries cenv ctx tenv dtys stys dtvs stvs vs
Proof
  Induct >> Cases_on `stys` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[return_copy_entries_def, OPT_MMAP_def, AllCaseEqs(),
       value_has_type_def, val_in_memory_def, val_wf_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[return_copy_memory_size]
QED

Theorem return_copy_tuple_children_widen[local]:
  !stys dtys dtvs.
    (stys = dtys \/ arg_types_fit stys dtys) /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs ==>
    LIST_REL (type_widens_to tenv) stys dtys
Proof
  Induct >> Cases_on `dtys` >>
  simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]
QED

Theorem return_copy_tuple_widening[local]:
  type_widens_to tenv sty (TupleT dtys) ==>
  ?stys. sty = TupleT stys /\ (stys = dtys \/ arg_types_fit stys dtys)
Proof
  Cases_on `sty` >> simp[type_widens_to_def, arg_type_fits_def] >> metis_tac[]
QED

Theorem return_copy_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      return_copy_entry cenv ctx tenv cd cs cdt cst cv) ==>
    return_copy_entry cenv ctx tenv (TupleT dtys) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[return_copy_tuple_widening] >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (irule return_copy_tuple_children_widen >>
     (conj_tac >- metis_tac[]) >>
     drule return_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
  `return_copy_entries cenv ctx tenv dtys stys tvs' tvs l` by
    (irule return_copy_entries_from_semantics >> gvs[val_wf_def] >>
     (conj_tac >- metis_tac[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[member_rank_lt_tuple]) >>
  simp[return_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  simp[val_in_memory_def, type_memory_size_def] >>
  irule (return_copy_tuple_suffix_frag |> SPEC_ALL |>
    Q.INST [`doff` |-> `0`, `soff` |-> `0`] |> SRULE []) >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`tenv`, `sw`, `tvs`] >>
  gvs[val_wf_def, type_memory_size_def, val_in_memory_def, ADD_COMM]
QED

Theorem return_copy_struct_values[local]:
  !names tvs fields.
    LENGTH names = LENGTH tvs /\
    struct_has_type (ZIP (names,tvs)) fields /\
    fields_val_wf fields (ZIP (names,tvs)) ==>
    ?vs. fields = ZIP (names,vs) /\ LENGTH vs = LENGTH names /\
         values_have_types tvs vs /\ tuple_val_wf vs tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fields` >>
  simp[value_has_type_def, val_wf_def] >>
  PairCases_on `h'` >> simp[value_has_type_def, val_wf_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule_all >> strip_tac >>
  qexists_tac `h'1::vs` >> simp[value_has_type_def, val_wf_def]
QED

Theorem return_copy_struct_field_bytes[local]:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv) ==>
    EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[OPT_MMAP_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[]
QED

Theorem return_copy_struct_widening[local]:
  type_widens_to tenv sty (StructT name) ==> sty = StructT name
Proof
  Cases_on `sty` >> simp[type_widens_to_def, arg_type_fits_def] >> metis_tac[]
QED

Theorem return_copy_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      return_copy_entry cenv ctx tenv cd cs cdt cst cv) ==>
    return_copy_entry cenv ctx tenv (StructT name) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule return_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >> drule OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    metis_tac[return_copy_struct_values, LENGTH_MAP] >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    (irule return_copy_tuple_children_widen >> simp[] >> metis_tac[]) >>
  `return_copy_entries cenv ctx tenv (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) tvs tvs vs` by
    (irule return_copy_entries_from_semantics >> simp[] >>
     gvs[evaluate_types_OPT_MMAP] >>
     (conj_tac >- metis_tac[]) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     `MEM cd (MAP (FST o SND) fields)` by metis_tac[] >>
     qpat_x_assum `MEM cd (MAP SND args)` kall_tac >>
     fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,cd,y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[get_struct_fields_def] >>
     drule_all member_rank_lt_struct >> simp[type_rank_def, nsid_to_string_def]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    ((conj_tac >- metis_tac[]) >>
     irule return_copy_struct_field_bytes >> qexistsl_tac [`tenv`, `tvs`] >> simp[] >>
     (conj_tac >- (rpt strip_tac >> irule return_copy_memory_size >>
       qexists_tac `tenv` >> simp[] >> metis_tac[])) >> metis_tac[]) >>
  simp[return_copy_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule MAP_CONG >> simp[FORALL_PROD]) >>
  simp[type_memory_size_def, val_in_memory_def,
       return_copy_struct_size_zip, return_copy_fields_tuple_zip] >>
  irule (return_copy_struct_suffix_frag |> SPEC_ALL |>
    Q.INST [`n` |-> `0`, `doff` |-> `0`, `soff` |-> `0`] |> SRULE []) >>
  qpat_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`tenv`, `sw`] >>
  gvs[type_memory_size_def, val_in_memory_def,
      return_copy_struct_size_zip, return_copy_fields_tuple_zip, ADD_COMM]
QED

Theorem return_copy_rank_entry:
  !n cenv tenv ctx dty sty dtv stv v.
    type_rank cenv.ce_struct_fields dty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v ==>
    return_copy_entry cenv ctx tenv dty sty dtv stv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty` >- simp[return_copy_word_entry] >>
  Cases_on `is_bytestring_type dty` >- simp[return_copy_bytestring_entry] >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (irule return_copy_sarray_entry >> simp[] >> (conj_tac >- metis_tac[]) >>
          rpt strip_tac >>
          qpat_x_assum `!k. k < _ ==> _`
            (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
          simp[] >> disch_then irule >> simp[] >> metis_tac[]) >>
      irule return_copy_dynarray_entry >> simp[] >> (conj_tac >- metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> metis_tac[])
  >~ [`TupleT dtys`]
  >- (irule return_copy_tuple_entry >> simp[] >> (conj_tac >- metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> metis_tac[])
  >~ [`StructT name`]
  >- (irule return_copy_struct_entry >> simp[] >> (conj_tac >- metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> metis_tac[]) >>
  gvs[is_word_type_def, evaluate_type_def] >> simp[return_copy_none_entry]
QED

Theorem return_copy_recursive_entry:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v ==>
  return_copy_entry cenv ctx tenv dty sty dtv stv v
Proof
  strip_tac >> irule return_copy_rank_entry >> simp[] >> metis_tac[]
QED
