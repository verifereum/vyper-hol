(* Conditional tuple and struct pointer-copy assembly. *)
Theory widenedAssignPtrCopyFields
Ancestors
  widenedAssignPtrCopyFieldList widenedAssignPtrCopyOffsets
  placeTypedCopyRecursivePath typedCopyDomain typedMemoryCopy
  valueEncodingDefs valueEncoding valueEncodingProps vyperTyping
  vyperTypeExprSoundness vyperTypeABI compileEnv emitHelper
  bodyPtrDefs ptrDiscipline fragGasPathPtr fragExec
  words finite_map pred_set list arithmetic vyperTypeSystem vyperTypeArgFits
  vyperValue exprLoweringProps exprLowering context loweringStateRelDefs

Theorem widened_assign_field_eligibility[local]:
  !dtys stys dtvs stvs vs.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) stys dtys /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    (!cd cs cdt cst cv. MEM cd dtys ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      R cd cs cdt cst cv) ==>
    LENGTH dtys = LENGTH stys /\ LENGTH dtys = LENGTH dtvs /\
    LENGTH dtys = LENGTH stvs /\ LENGTH dtys = LENGTH vs /\
    (!i. i < LENGTH dtys ==>
      R (EL i dtys) (EL i stys) (EL i dtvs) (EL i stvs) (EL i vs) /\
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs))
Proof
  Induct >> Cases_on `stys` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[OPT_MMAP_def, AllCaseEqs(), value_has_type_def, val_wf_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  gen_tac >> Cases_on `i` >> simp[] >>
  metis_tac[typed_copy_memory_size]
QED

Theorem widened_assign_typed_fields_counted:
  !cenv tenv ctx D PG dty sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    ((?dtys. dty = TupleT dtys) \/ (?name. dty = StructT name)) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields dty ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      !a b dst src dw sw fn G tn s.
        compile_store_memory_typed cenv dst cd src cs a = ((),b) /\
        (!x. dst = Var x ==> not_fresh_at a x) /\
        (!x. src = Var x ==> not_fresh_at a x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        op_taint tn dst = {} /\ op_taint tn src = {} /\
        (0 < type_memory_size cdt ==>
          ?x. dst = Var x /\ ptr_covers G tn x s (type_memory_size cdt)) /\
        (0 < type_memory_size cst ==>
          ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size cst)) /\
        w2n dw + type_memory_size cdt < dimword (:256) /\
        w2n sw + type_memory_size cst < dimword (:256) /\
        (w2n dw + type_memory_size cdt <= w2n sw \/
         w2n sw + type_memory_size cst <= w2n dw) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory cst cv (w2n sw) m) /\
        fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
        s.vs_current_bb = a.cs_current_bb /\
        s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
        ~ctx_has_dalloca ctx ==>
        ?G' tn' t.
          gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
          t.vs_current_bb = b.cs_current_bb /\
          t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
          (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
            val_in_memory cdt cv (w2n dw) m) /\
          typed_copy_state_frame a (w2n dw) (type_memory_size cdt) s t /\
          (!x. not_fresh_at a x ==>
            lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
            op_taint tn' (Var x) = op_taint tn (Var x)) /\
          tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
          tn'.t_imm = tn.t_imm /\
          (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size cdt) ==>
            (i IN tn'.t_mem <=> i IN tn.t_mem))) ==>
    !a b dst src dw sw fn G tn s.
      compile_store_memory_typed cenv dst dty src sty a = ((),b) /\
      (!x. dst = Var x ==> not_fresh_at a x) /\
      (!x. src = Var x ==> not_fresh_at a x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      op_taint tn dst = {} /\ op_taint tn src = {} /\
      (0 < type_memory_size dtv ==>
        ?x. dst = Var x /\ ptr_covers G tn x s (type_memory_size dtv)) /\
      (0 < type_memory_size stv ==>
        ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv)) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      (w2n dw + type_memory_size dtv <= w2n sw \/
       w2n sw + type_memory_size stv <= w2n dw) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (w2n sw) m) /\
      fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx ==>
      ?G' tn' t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
        (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n dw) m) /\
        typed_copy_state_frame a (w2n dw) (type_memory_size dtv) s t /\
        (!x. not_fresh_at a x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
          op_taint tn' (Var x) = op_taint tn (Var x)) /\
        tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
        tn'.t_imm = tn.t_imm /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
          (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume widened_assign_typed_fields_counted[tuple]:
  gvs[] >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (`!ss ds. (ss = ds \/ arg_types_fit ss ds) /\
         (?tvs. OPT_MMAP (evaluate_type tenv) ds = SOME tvs) ==>
         LIST_REL (type_widens_to tenv) ss ds` suffices_by
       (strip_tac >> drule typed_copy_tuple_widening >>
        gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
        metis_tac[]) >>
     Induct >> Cases_on `ds` >>
     simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  `compile_typed_copy_fields cenv dst src dtys stys 0 0 a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  gvs[type_memory_size_def, val_in_memory_def] >>
  qspecl_then [`\cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields (TupleT dtys) /\
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv`,
      `cenv`, `ctx`, `D`, `PG`] mp_tac widened_assign_typed_copy_fields_counted >>
  (impl_tac
   >- (conj_tac
       >- (BETA_TAC >> rpt gen_tac >> strip_tac >>
           qpat_x_assum `!cd cs cdt cst cv. _`
             (qspecl_then [`dty`, `sty`, `dtv`, `stv`, `v`] mp_tac) >>
           simp[AC ADD_ASSOC ADD_COMM]) >>
       (rpt gen_tac >> strip_tac >>
        irule widened_assign_with_byte_offset_counted >>
        metis_tac[]))) >>
  disch_then (qspecl_then [`dtys`, `stys`, `tvs'`, `tvs`, `l`] mp_tac) >>
  disch_then (qspecl_then [`dst`, `src`, `0`, `0`] mp_tac) >>
  disch_then (qspecl_then [`type_memory_size_list tvs'`,
                          `type_memory_size_list tvs`] mp_tac) >>
  disch_then (irule o SRULE [ADD_0, AC ADD_ASSOC ADD_COMM]) >>
  simp[AC ADD_ASSOC ADD_COMM, val_wf_def] >>
  mp_tac (Q.INST [`R` |-> `\cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields (TupleT dtys) /\
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv`]
    widened_assign_field_eligibility) >>
  disch_then (qspecl_then [`dtys`, `stys`, `tvs'`, `tvs`, `l`] mp_tac) >>
  (impl_tac >- (gvs[val_wf_def] >>
    qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
    metis_tac[member_rank_lt_tuple])) >>
  strip_tac >> gvs[val_wf_def]
QED

Resume widened_assign_typed_fields_counted[struct]:
  gvs[] >> drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    suspend "struct_values" >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    (irule EVERY2_refl >> simp[EVERY_MEM] >> rpt strip_tac >>
     simp[type_widens_to_def, well_formed_type_def]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    suspend "struct_bytes" >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `tvs` >>
     Induct_on `args` >> Cases_on `tvs` >> simp[type_memory_size_def]) >>
  rpt gen_tac >> strip_tac >>
  `compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) 0 0 a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def,
          is_bytestring_type_def, compileEnvTheory.get_struct_fields_def] >>
     `compile_struct_typed_copy cenv dst src fields fields 0 0 =
       compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields)
         (MAP (FST o SND) fields) 0 0` by
       (`MAP (\(nm,ty,sz). ty) fields = MAP (FST o SND) fields` by
          (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
        mp_tac (Q.SPECL [`fields`, `fields`, `cenv`, `dst`, `src`, `0`, `0`]
          typed_copy_struct_fields_producer) >> simp[EVERY_MEM]) >> simp[]) >>
  gvs[type_memory_size_def, val_in_memory_def, typed_copy_fields_tuple_zip] >>
  qspecl_then [`\cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields (StructT name) /\
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv`,
      `cenv`, `ctx`, `D`, `PG`] mp_tac widened_assign_typed_copy_fields_counted >>
  (impl_tac
   >- (conj_tac
       >- (BETA_TAC >> rpt gen_tac >> strip_tac >>
           qpat_x_assum `!cd cs cdt cst cv. _`
             (qspecl_then [`dty`, `sty`, `dtv`, `stv`, `v`] mp_tac) >>
           simp[AC ADD_ASSOC ADD_COMM]) >>
       (rpt gen_tac >> strip_tac >>
        irule widened_assign_with_byte_offset_counted >> metis_tac[]))) >>
  disch_then (qspecl_then [`MAP SND args`, `MAP SND args`, `tvs`, `tvs`, `vs`] mp_tac) >>
  disch_then (qspecl_then [`dst`, `src`, `0`, `0`] mp_tac) >>
  disch_then (qspecl_then [`type_memory_size_list tvs`,
                          `type_memory_size_list tvs`] mp_tac) >>
  disch_then (irule o SRULE [ADD_0, AC ADD_ASSOC ADD_COMM]) >>
  simp[AC ADD_ASSOC ADD_COMM] >>
  mp_tac (Q.INST [`R` |-> `\cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd < type_rank cenv.ce_struct_fields (StructT name) /\
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv`]
    widened_assign_field_eligibility) >>
  disch_then (qspecl_then [`MAP SND args`, `MAP SND args`, `tvs`, `tvs`, `vs`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- metis_tac[] >>
    rpt strip_tac >>
    `MEM cd (MAP (FST o SND) fields)` by metis_tac[] >>
    qpat_x_assum `MEM cd (MAP SND args)` kall_tac >>
    fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
    `MEM (y0,cd,y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[compileEnvTheory.get_struct_fields_def] >>
    drule_all typedCopyDomainTheory.member_rank_lt_struct >>
    simp[typedCopyDomainTheory.type_rank_def, nsid_to_string_def])) >>
  strip_tac >> gvs[]
QED

Resume widened_assign_typed_fields_counted[struct_values]:
  qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
  qpat_x_assum `struct_has_type _ l` mp_tac >>
  qpat_x_assum `fields_val_wf l _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  qid_spec_tac `l` >> qid_spec_tac `tvs` >>
  Induct_on `args` >> Cases_on `tvs` >> Cases_on `l` >>
  simp[value_has_type_def, val_wf_def] >>
  PairCases_on `h'` >> simp[value_has_type_def, val_wf_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule_all >> strip_tac >>
  qexists_tac `h'1::vs` >> simp[value_has_type_def, val_wf_def]
QED

Resume widened_assign_typed_fields_counted[struct_bytes]:
  (conj_tac >- metis_tac[]) >>
  `!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  qpat_x_assum `OPT_MMAP _ (MAP (FST o SND) fields) = SOME tvs` mp_tac >>
  qpat_x_assum `EVERY _ fields` mp_tac >>
  qpat_x_assum `!ty tv. evaluate_type tenv ty = SOME tv ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  qid_spec_tac `tvs` >> Induct_on `fields` >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[OPT_MMAP_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[]
QED

Finalise widened_assign_typed_fields_counted
