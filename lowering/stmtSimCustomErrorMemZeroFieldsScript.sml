Theory stmtSimCustomErrorMemZeroFields
Ancestors
  stmtSimCustomErrorMemCopyFields placeTypedCopyRecursivePath
  placeTypedCopyPath typedMemoryCopy fragGasMode fragGasPathMem
  context emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs valueEncodingProps venomState venomExecSemantics
  words list arithmetic pair memSafeRun venomMemDefs contextCodegenRel fragExec

Theorem typed_copy_zero_fields_checked:
  !dtys stys dtvs stvs vs dst src sa sb s dw sw func.
    LENGTH dtys = LENGTH vs /\ LENGTH stys = LENGTH vs /\
    LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs /\
    EVERY (\(ty,tv). type_memory_bytes cenv ty = type_memory_size tv /\
                      type_memory_size tv = 0) (ZIP (dtys,dtvs)) /\
    EVERY (\(ty,tv). type_memory_bytes cenv ty = type_memory_size tv /\
                      type_memory_size tv = 0) (ZIP (stys,stvs)) /\
    (!dty sty dtv stv v.
      MEM (dty,sty,dtv,stv,v)
        (ZIP (dtys,ZIP (stys,ZIP (dtvs,ZIP (stvs,vs))))) ==>
      !func dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory /\
        w2n dw < dimword (:256) /\ w2n dw <= s.vs_alloca_next /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        alloca_inv s /\ alloca_history func s /\
        ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
        s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        ?t. gas_marked_path T ctx func s 0 (OK t) /\
            val_in_memory dtv v (w2n dw) t.vs_memory /\
            typed_copy_state_frame sa (w2n dw) 0 s t /\
            ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next) /\
    type_memory_size_list stvs = 0 /\ type_memory_size_list dtvs = 0 /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv dst src dtys stys 0 0 sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw) s.vs_memory /\
    w2n dw < dimword (:256) /\ w2n dw <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        tuple_in_memory vs dtvs (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) 0 s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_store_memory_typed_def, comp_return_def,
          val_in_memory_def] >>
      qexists_tac `s` >> simp[typed_copy_state_frame_refl,
        gas_marked_path_def, gas_path_mem_rules]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gvs[] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, compile_with_byte_offset_def,
       comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory_typed cenv dst dty src sty sa = (u,sc)` >>
  Cases_on `u` >>
  rename1 `tuple_val_wf (v::vs) (stv::stvs)` >>
  rename1 `tuple_val_wf (v::vs) (dtv::dtvs)` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  rename1 `val_in_memory stv v (w2n sw) s.vs_memory` >>
  rename1 `tuple_in_memory vs stvs (w2n sw) s.vs_memory` >>
  rename1 `compile_typed_copy_fields cenv dst src dtys stys 0 0 sc = ((),sb)` >>
  suspend "cons"
QED

Resume typed_copy_zero_fields_checked[cons]:
  `ci_mono sa sc /\ ci_mono sc sb` by
    metis_tac[cj 1 ci_mono_typed_memory_family,
              cj 2 ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends sa sc /\ cs_extends sc sb` by gvs[ci_mono_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split] >>
  qpat_assum `!dty sty dtv stv v. _`
    (qspecl_then [`dty`, `sty`, `dtv`, `stv`, `v`] mp_tac) >>
  simp[] >> disch_then drule >>
  disch_then (qspecl_then [`func`, `s`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "suffix"
QED

Resume typed_copy_zero_fields_checked[suffix]:
  rename1 `gas_marked_path T ctx func s 0 (OK mid)` >>
  `eval_operand dst mid = SOME dw /\ eval_operand src mid = SOME sw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `alloca_inv mid` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `tuple_in_memory vs stvs (w2n sw) mid.vs_memory` by
    (irule typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`w2n dw`, `0`, `s.vs_memory`] >>
     gvs[typed_copy_state_frame_def]) >>
  qpat_x_assum `!stys dtvs stvs vs' dst' src' sa' sb' s'' dw' sw' func'. _`
    (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`dtvs`, `stvs`, `vs`] mp_tac) >>
  disch_then (qspecl_then [`mid`, `dw`, `sw`, `func`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt gen_tac >> disch_tac >> rpt strip_tac >>
    qpat_x_assum `!dty sty dtv stv v. _` irule >> simp[] >>
    goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
    metis_tac[])) >> strip_tac >>
  `val_in_memory dtv v (w2n dw) t.vs_memory` by
    (irule typed_copy_frame_preserves_source >> simp[] >>
     qexistsl_tac [`0`, `w2n dw`, `mid.vs_memory`] >>
     gvs[typed_copy_state_frame_def]) >>
  `typed_copy_state_frame sa (w2n dw) 0 mid t` by
    (irule typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[]) >>
  `typed_copy_state_frame sa (w2n dw) 0 s t` by
    (irule typed_copy_state_frame_trans >> qexists_tac `mid` >> simp[]) >>
  qpat_assum `gas_marked_path T ctx func s 0 (OK mid)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Finalise typed_copy_zero_fields_checked
