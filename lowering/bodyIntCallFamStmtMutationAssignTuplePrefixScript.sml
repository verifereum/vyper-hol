(* Counted tuple staging and load-all at one resource endpoint. *)
Theory bodyIntCallFamStmtMutationAssignTuplePrefix
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore
  bodyIntCallJointPurePath
  tuplePlaceHead tuplePlaceRhsCert tuplePlaceLoad tuplePlaceStage
  tupleStageProps exprLoweringProps stmtLoweringMono compileEnv
  loweringStateRelDefs loweringPosts valueEncoding valueEncodingProofs
  valueEncodingProps vyperValue vyperTyping venomState
  vyperTypeABI tupleTypedLoad fragGasSeq fragGasMode
  fragExec context valueEncodingDefs loweringHalt tuplePlacePrefixCert
  exprSimCopy exprSimProps stmtSimDefs localPtrsProps intCallFrame
Libs monadsyntax

Theorem intcall_assign_tuple_prefix:
  expr_type e = TupleT tys /\ lowered_value_type ce e = TupleT ltys /\
  value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
  evaluate_type (get_tenv fp.jc_cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  LIST_REL (\t tv. type_memory_bytes ce t = type_memory_size tv) ltys ltvs /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es0 si su s0 es
    (ArrayV (TupleV vs)) op s /\
  (!x. op = Var x ==> not_fresh_at su x) /\ si.cs_next_id <= su.cs_next_id /\
  (if flag then
     do buf <- compile_alloc_buffer (type_memory_bytes ce (TupleT ltys));
        emit_void MCOPY [buf.buf_operand; op;
          Lit (n2w (type_memory_bytes ce (TupleT ltys)))];
        comp_return buf.buf_operand od
   else comp_return op) su = (staged,sl) /\
  compile_tuple_load_all ce staged ltys 0 sl = (elems,ss) /\
  cs_extends sl ss /\ fn_has_code su sl fp.jc_func /\
  fn_has_code sl ss fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es su s /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?t w. tuple_place_head fp.jc_ctx fp.jc_func ce fp.jc_cx es
      si.cs_next_id ss tys ltys ltvs vs elems w 0 t /\
    gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es su s es ss t /\
    intcall_joint_res fp ce env es ss t
Proof
  strip_tac >>
  drule_all tuple_place_rhs_certificate >> strip_tac >>
  `values_have_types ltvs vs` by fs[value_has_type_def] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv fp.jc_cx) t = SOME tv) ltys ltvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT ltys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes ce (TupleT ltys) = type_memory_size_list ltvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `w2n w + type_memory_size_list ltvs < dimword (:256)` by
    (Cases_on `type_memory_size_list ltvs = 0`
     >- simp[wordsTheory.w2n_lt] >>
     `0 < type_memory_size_list ltvs` by decide_tac >>
     drule_all expr_tuple_memory_owned >> strip_tac >>
     `b + sz < dimword (:256)` by
       (irule tuple_container_bound >> metis_tac[]) >> decide_tac) >>
  `?a aw. eval_operand staged a = SOME aw /\
     tuple_in_memory vs ltvs (w2n aw) a.vs_memory /\
     w2n aw + type_memory_size_list ltvs < dimword (:256) /\
     tuple_place_snapshot ce fp.jc_cx es si.cs_next_id sl.cs_next_id
       tys ltys ltvs aw a /\
     gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK a) /\
     intcall_expr_cont fp ce env es su s es sl a /\
     (!x. staged = Var x ==> not_fresh_at sl x)` by
    (Cases_on `flag`
     >- (gvs[] >>
         `val_in_memory (TupleTV ltvs) (ArrayV (TupleV vs)) (w2n w) s.vs_memory /\
          val_wf (TupleTV ltvs) (ArrayV (TupleV vs)) /\
          val_footprint (TupleTV ltvs) (ArrayV (TupleV vs)) <=
            type_memory_size_list ltvs /\
          type_memory_size_list ltvs < dimword (:256)` by
           (simp[val_in_memory_def,val_wf_def,val_footprint_def,
                 type_memory_size_def] >> decide_tac) >>
         `local_ptrs_reserved ce su` by fs[intcall_joint_res_def,intcall_expr_res_def] >>
         mp_tac (Q.SPECL [`fp.jc_ctx`,`fp.jc_func`,`ce`,`fp.jc_cx`,`es`,
           `su`,`sl`,`staged`,`op`,`s`,`w`,`type_memory_size_list ltvs`,
           `TupleTV ltvs`,`ArrayV (TupleV vs)`] tuple_place_stage_effect) >>
         simp[] >>
         disch_then (qx_choosel_then [`a`,`aw`] strip_assume_tac) >>
         `su.cs_next_var <= sl.cs_next_var /\ su.cs_next_id < sl.cs_next_id` by
           (drule_all tuple_stage_copy_parts >> strip_tac >>
            gvs[emitHelperTheory.emit_void_def,emitHelperTheory.emit_inst_def,
                fresh_id_def,emit_def,comp_bind_def,comp_ignore_bind_def,
                comp_return_def]) >>
         `allocas_above fp.jc_lo a` by
           (irule gas_marked_path_allocas_above >>
            goal_assum (drule_at Any) >>
            fs[intcall_joint_res_def,intcall_expr_res_def]) >>
         `s.vs_alloca_next <= a.vs_alloca_next` by
           (irule gas_marked_path_alloca_next_mono >>
            goal_assum (drule_at Any)) >>
         `fp.jc_lo <= w2n aw` by
           (fs[allocas_above_def] >> metis_tac[]) >>
         `!name b sz. local_region ce es.scopes a name b sz <=>
                      local_region ce es.scopes s name b sz` by
           (rpt gen_tac >> irule copy_buffer_local_region_frame >>
            qexists `su` >> simp[]) >>
         `!b k. fp.jc_prot b k ==>
            mem_bytes_at b k a.vs_memory = mem_bytes_at b k s.vs_memory` by
           (rpt strip_tac >>
            `b+k <= fp.jc_lo` by fs[intcall_frame_ok_def] >>
            first_x_assum irule >> decide_tac) >>
         `!operand x. fp.jc_reserved operand /\ operand = Var x ==>
            not_fresh_at su x` by
           (qpat_assum `intcall_joint_res fp ce env es su s` mp_tac >>
            simp_tac (srw_ss()) [intcall_joint_res_def,intcall_expr_res_def] >>
            strip_tac >> asm_rewrite_tac[]) >>
         `!operand. fp.jc_reserved operand ==>
            eval_operand operand a = eval_operand operand s` by
           (rpt strip_tac >>
            qpat_assum `!operand. (!x. operand = Var x ==> not_fresh_at su x) ==>
              eval_operand operand a = _` irule >>
            rpt strip_tac >> metis_tac[]) >>
         `intcall_expr_res fp ce env es sl a` by
           (irule intcall_joint_res_frame >> simp[] >>
            qexistsl [`s`,`su`] >> fs[intcall_joint_res_def] >> metis_tac[]) >>
         `locals_kept ce es es s a` by
           (irule locals_kept_regions >> rpt strip_tac >>
            qpat_assum `!off len. (_ \/ _) ==>
              mem_bytes_at off len a.vs_memory = _` irule >>
            metis_tac[]) >>
         `intcall_expr_cont fp ce env es su s es sl a` by
           (simp[intcall_expr_cont_def] >>
            fs[stmtSimDefsTheory.alloca_frame_def] >> metis_tac[]) >>
         `w2n aw + type_memory_size_list ltvs < dimword (:256)` by
           (irule tuple_container_bound >> goal_assum (drule_at Any) >> metis_tac[]) >>
         `tuple_place_snapshot ce fp.jc_cx es si.cs_next_id sl.cs_next_id
            tys ltys ltvs aw a` by
           (irule tuple_place_snapshot_owned >>
            qexistsl [`su.cs_next_id`,`w2n aw`,`type_memory_size_list ltvs`] >>
            simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
         qexistsl [`a`,`aw`] >> fs[val_in_memory_def]) >>
     gvs[comp_return_def] >> qexistsl [`s`,`w`] >>
     simp[gas_marked_path_def,fragGasPathTheory.gas_path_rules,
          intcall_expr_cont_def,intcall_joint_res_def,locals_kept_refl] >>
     fs[intcall_joint_res_def]) >>
  `local_ptrs_reserved ce sl /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es a /\
   ~a.vs_halted /\ a.vs_current_bb = sl.cs_current_bb /\
   a.vs_inst_idx = LENGTH sl.cs_current_insts` by
    fs[intcall_expr_cont_def,intcall_expr_res_def] >>
  drule tuple_place_load_snapshot_effect >>
  disch_then (drule_at (Pat `tuple_place_snapshot _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`vs`, `get_tenv fp.jc_cx`] mp_tac) >>
  simp[] >> strip_tac >>
  `intcall_expr_cont fp ce env es sl a es ss t` by
    (`sl.cs_next_var <= ss.cs_next_var` by
       (mp_tac (cj 4 ci_mono_list_helpers) >>
        disch_then (qspecl_then [`ce`,`staged`,`ltys`,`0`,`sl`] mp_tac) >>
        gvs[ci_mono_def]) >>
     `intcall_expr_cont fp ce env es sl a es sl a` by
       fs[intcall_expr_cont_def,locals_kept_refl] >>
     irule intcall_expr_cont_readonly >> simp[] >>
     qexistsl [`a`,`sl`] >> simp[] >>
     fs[venom_state_component_equality]) >>
  qexistsl [`t`,`aw`] >>
  conj_tac >-
    (irule tuple_place_head_intro >> simp[] >>
     metis_tac[listTheory.LIST_REL_LENGTH,arithmeticTheory.ADD_COMM]) >>
  conj_tac >-
    (`gas_marked_path F fp.jc_ctx fp.jc_func s (0+0) (OK t)` suffices_by simp[] >>
     irule gas_marked_path_then >> qexists `a` >> simp[]) >>
  conj_tac >-
    (`su.cs_next_var <= sl.cs_next_var /\ su.cs_next_id <= sl.cs_next_id` by
       (Cases_on `flag` >>
        gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        Cases_on `compile_alloc_buffer (type_memory_size_list ltvs) su` >>
        gvs[] >>
        qspecl_then [`type_memory_size_list ltvs`,`su`] mp_tac
          ci_mono_compile_alloc_buffer >>
        gvs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def,
            emit_def, fresh_id_def, comp_bind_def, comp_return_def, ci_mono_def]) >>
     irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     conj_tac >- fs[intcall_joint_res_def] >>
     qexistsl [`es`,`sl`,`a`] >> simp[]) >>
  fs[intcall_expr_cont_def,intcall_joint_res_def]
QED

