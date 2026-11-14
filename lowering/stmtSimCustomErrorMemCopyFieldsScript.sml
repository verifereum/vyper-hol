Theory stmtSimCustomErrorMemCopyFields
Ancestors
  stmtSimCustomErrorMemCopyInterface placeTypedCopyRecursivePath
  placeTypedCopyPath typedMemoryCopy fragGasMode fragGasPathMem
  context emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs valueEncodingProps venomState venomExecSemantics
  words list arithmetic pair memSafeRun venomMemDefs contextCodegenRel fragExec

Theorem typed_copy_offset_checked:
  typed_copy_checked_entry cenv ctx dty sty dtv stv v /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  w2n sw + soff + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
   w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb` by
    metis_tac[typed_copy_offset_mono, cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
   cs_extends s1 sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 sb func` by metis_tac[fn_has_code_split] >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. dp = Var x ==> not_fresh_at s1 x) /\
   (!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x) /\
   (!x. src = Var x ==> not_fresh_at s1 x)` by
    metis_tac[typed_copy_offset_fresh, typed_copy_operand_fresh_mono] >>
  drule_all compile_with_byte_offset_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `alloca_inv t /\ t.vs_memory = s.vs_memory /\
   typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, typed_copy_frame_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `eval_operand src t = SOME sw` by metis_tac[typed_copy_state_frame_operand] >>
  drule_all compile_with_byte_offset_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `alloca_inv t' /\ t'.vs_memory = t.vs_memory /\
   typed_copy_state_frame s1 (w2n dw + doff) (type_memory_size dtv) t t'` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, typed_copy_frame_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `eval_operand dp t' = SOME (dw + n2w doff)` by
    metis_tac[typed_copy_state_frame_operand] >>
  drule typed_copy_checked_entry_run >> disch_then drule >>
  disch_then (qspecl_then [`sw + n2w soff`, `t'`, `func`, `dw + n2w doff`] mp_tac) >>
  (impl_tac >- gvs[arithmeticTheory.ADD_COMM]) >> strip_tac >>
  `typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t''` by
    (gvs[] >>
     `typed_copy_state_frame sa (doff + w2n dw) (type_memory_size dtv) t t'` by
       (irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[]) >>
     `ci_mono sa s2` by (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
     `typed_copy_state_frame sa (doff + w2n dw) (type_memory_size dtv) t' t''` by
       (irule typed_copy_state_frame_mono >> qexists_tac `s2` >> simp[]) >>
     simp[arithmeticTheory.ADD_COMM] >>
     irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_trans >> qexists_tac `t'` >> simp[]) >>
  gvs[gas_marked_path_def] >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t')`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t''` >> gvs[]
QED

Definition typed_copy_checked_entries_def:
  (typed_copy_checked_entries cenv ctx [] stys dtvs stvs vs <=>
     stys = [] /\ dtvs = [] /\ stvs = [] /\ vs = []) /\
  (typed_copy_checked_entries cenv ctx (dty::dtys) stys dtvs stvs vs <=>
     case (stys,dtvs,stvs,vs) of
       (sty::stys,dtv::dtvs,stv::stvs,v::vs) =>
         type_memory_bytes cenv dty = type_memory_size dtv /\
         type_memory_bytes cenv sty = type_memory_size stv /\
         typed_copy_checked_entry cenv ctx dty sty dtv stv v /\
         typed_copy_checked_entries cenv ctx dtys stys dtvs stvs vs
     | _ => F)
End

Theorem typed_copy_checked_entries_lengths:
  !dtys stys dtvs stvs vs.
    typed_copy_checked_entries cenv ctx dtys stys dtvs stvs vs ==>
    LENGTH dtys = LENGTH vs /\ LENGTH stys = LENGTH vs /\
    LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs
Proof
  Induct >> simp[typed_copy_checked_entries_def] >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[typed_copy_checked_entries_def] >> metis_tac[]
QED

Theorem typed_copy_fields_checked:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw func.
    typed_copy_checked_entries cenv ctx dtys stys dtvs stvs vs /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next /\
    w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw + doff)
          (type_memory_size_list dtvs) s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[typed_copy_checked_entries_def, compile_store_memory_typed_def,
          comp_return_def, val_in_memory_def, type_memory_size_def] >>
      qexists_tac `s` >> simp[typed_copy_state_frame_refl,
        gas_marked_path_def, gas_path_mem_rules]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[typed_copy_checked_entries_def] >>
  rename1 `typed_copy_checked_entry cenv ctx dty sty dtv stv v` >>
  rename1 `typed_copy_checked_entries cenv ctx dtys stys dtvs stvs vs` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dst_ptr dty src_ptr sty cs'' = (u,sc)` >>
  Cases_on `u` >> suspend "cons"
QED

Resume typed_copy_fields_checked[cons]:
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst' src' doff' soff' sa' sb' s'' dw' sw' func'. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs''` by metis_tac[typed_copy_offset_mono] >>
     `ci_mono cs'' sc` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
     `ci_mono sc sb` by metis_tac[cj 2 ci_mono_typed_memory_family, pairTheory.SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends sa sc /\ cs_extends sc sb` by gvs[ci_mono_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
      typed_copy_offset_checked) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`sw`, `s`, `func`, `dw`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> decide_tac)) >>
  strip_tac >> suspend "suffix"
QED

Resume typed_copy_fields_checked[suffix]:
  `LENGTH vs = LENGTH stvs` by metis_tac[typed_copy_checked_entries_lengths] >>
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `typed_copy_checked_entry _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[typed_copy_state_frame_def]) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `!stys dtvs stvs vs dst' src' doff' soff' sa' sb' s'' dw' sw' func'. _` drule >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`, `func`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> decide_tac)) >>
  strip_tac >> suspend "finish"
QED

Resume typed_copy_fields_checked[finish]:
  `val_in_memory dtv v (doff + w2n dw) t'.vs_memory` by
    (irule typed_copy_frame_preserves_source >>
     conj_tac >- (gvs[arithmeticTheory.ADD_COMM]) >>
     qexistsl_tac [`type_memory_size_list dtvs`,
       `doff + (type_memory_size dtv + w2n dw)`, `t.vs_memory`] >>
     qpat_assum `typed_copy_state_frame sc _ _ t t'`
       (mp_tac o cj 3 o REWRITE_RULE [typed_copy_state_frame_def]) >>
     simp[GSYM ADD_ASSOC] >> strip_tac >>
     gvs[arithmeticTheory.ADD_COMM]) >>
  `typed_copy_state_frame sa (doff + w2n dw)
     (type_memory_size dtv + type_memory_size_list dtvs) s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >>
     conj_tac
     >- (irule typed_copy_state_frame_subinterval >>
         qexistsl_tac [`w2n dw + doff`, `type_memory_size dtv`] >> simp[]) >>
     irule typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[] >>
     irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`doff + type_memory_size dtv + w2n dw`,
       `type_memory_size_list dtvs`] >> simp[]) >>
  qpat_assum `gas_marked_path T ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[GSYM ADD_ASSOC] >>
  gvs[GSYM ADD_ASSOC]
QED

Finalise typed_copy_fields_checked

Theorem typed_copy_checked_entries_from_semantics:
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
      typed_copy_checked_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_checked_entries cenv ctx dtys stys dtvs stvs vs
Proof
  Induct >> Cases_on `stys` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[typed_copy_checked_entries_def, OPT_MMAP_def, AllCaseEqs(),
       vyperTypingTheory.value_has_type_def, val_in_memory_def, val_wf_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[typed_copy_memory_size]
QED

Theorem typed_copy_tuple_checked:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  typed_copy_checked_entries cenv ctx dtys stys dtvs stvs vs /\
  tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
  compile_store_memory_typed cenv dst (TupleT dtys) src (TupleT stys) sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory (TupleTV stvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (TupleTV stvs) < dimword (:256) /\
  w2n dw + type_memory_size (TupleTV dtvs) < dimword (:256) /\
  w2n sw + type_memory_size (TupleTV stvs) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (TupleTV dtvs) <= s.vs_alloca_next /\
  (w2n sw + type_memory_size (TupleTV stvs) <= w2n dw \/
   w2n dw + type_memory_size (TupleTV dtvs) <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory (TupleTV dtvs) (ArrayV (TupleV vs)) (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size (TupleTV dtvs)) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_fields_checked >> disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`, `func`] mp_tac) >>
  gvs[val_in_memory_def, type_memory_size_def]
QED

Theorem typed_copy_struct_checked:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string name) /\
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,ty,sz). sz = type_memory_bytes cenv ty) fields /\
  typed_copy_checked_entries cenv ctx
    (MAP (FST o SND) fields) (MAP (FST o SND) fields) tvs tvs vs /\
  tuple_val_wf vs tvs /\
  compile_store_memory_typed cenv dst (StructT name) src (StructT name) sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  tuple_in_memory vs tvs (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size_list tvs < dimword (:256) /\
  w2n dw + type_memory_size_list tvs < dimword (:256) /\
  w2n sw + type_memory_size_list tvs <= s.vs_alloca_next /\
  w2n dw + type_memory_size_list tvs <= s.vs_alloca_next /\
  (w2n sw + type_memory_size_list tvs <= w2n dw \/
   w2n dw + type_memory_size_list tvs <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      tuple_in_memory vs tvs (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size_list tvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  `compile_struct_typed_copy cenv dst src fields fields 0 0 =
   compile_typed_copy_fields cenv dst src
     (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0` by
    (qpat_assum `MAP _ fields = MAP (FST o SND) fields`
       (fn th => rewrite_tac[GSYM th]) >>
     irule typed_copy_struct_fields_producer >> simp[EVERY_MEM]) >>
  gvs[] >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_fields_checked >> disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`, `func`] mp_tac) >> simp[]
QED
