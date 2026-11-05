(* The counted value judgment of a struct field read, for any base:
   compile_attribute adds the field's offset to the base's pointer, and the
   source selects the field of the base's result.  The base's counted
   outcome carries the source run that reached its end state, so the
   field read's admissibility rules out a type error in the selection; the
   selection reads no gas, so it runs alike under every gas tail. *)
Theory bodyAttributeMemory
Ancestors
  bodyFieldMemoryProps exprSimAttribute exprSimAttributeFields
  exprSimAttributeProps exprSimFieldLayout stmtSimForced
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimSource exprSimUnwrap
  exprSimDefs loweringPosts gasOutcome gasSummary gasContext fragGasMode
  bodySimStmtCases exprLowering exprLoweringProps compileEnv context
  vyperAST vyperInterpreter vyperState vyperTypeExprSoundness fragExec
  exprSimProps valueTypingMemoryProps valueEncoding vyperTyping

(* The counted outcome of a source also gives, at its normal end, a run of
   the source that reached the end state. *)
Theorem gas_outcome_link[local]:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R ==>
  gas_outcome memory tops (ctx,func) source (es,s0)
    (\res ee t. Q res ee t /\ ?gs. source (es with gas_obs := gs) = (res, ee))
    R
Proof
  rw[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `source (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (res, es_end with gas_obs := [])` by
        (fs[gas_marked_exec_def] >>
         first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
      metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem eval_attr_bind[local]:
  eval_expr cx (Attribute ann obj fld) =
  bind (eval_expr cx obj)
    (\r. select_result cx (expr_type obj) r (AttrSubscript fld))
Proof
  simp[FUN_EQ_THM, eval_expr_attribute]
QED

(* A field selection reads no gas observation. *)
Theorem select_attr_gas_obs[local]:
  !cx ty tv fld ee tail.
    select_result cx ty tv (AttrSubscript fld) (ee with gas_obs := tail) =
    (FST (select_result cx ty tv (AttrSubscript fld) ee),
     ee with gas_obs := tail)
Proof
  rpt gen_tac >> Cases_on `tv`
  >- (simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
           return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
  >- (Cases_on `p`
      >- (rename1 `StoragePlace tr slot stv` >> Cases_on `stv` >>
          simp[select_result_def, extend_place_def, extend_storage_place_def,
               bind_def, lift_option_type_def, return_def, raise_def,
               pairTheory.UNCURRY] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
      >- (simp[select_result_def, extend_place_def, place_type_value_def,
               read_place_def, get_scopes_def, bind_def, ignore_bind_def,
               lift_option_type_def, lift_sum_def, return_def, raise_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
      simp[select_result_def, extend_place_def, place_type_value_def,
           read_place_def, get_immutables_def, get_address_immutables_def,
           bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
           return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >>
           gvs[bind_def, return_def, raise_def])) >>
  simp[select_result_def, extend_place_def, raise_def]
QED

(* The source side of the field read: the selection from the base's
   result succeeds, under every gas tail, with the field's value. *)
Theorem attr_select_field[local]:
  expr_body_pre cenv cx env (Attribute ann obj fld) es /\
  expr_type obj = StructT sid /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME ann /\
  vv_post ctx func cenv cx obj es sa sm s0 ee tv bvv t /\
  eval_expr cx obj (es with gas_obs := gs) = (INL tv, ee) ==>
  ?fs ftv vals fv tv'.
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    read_result cx tv ee = (INL (StructV vals), ee) /\
    (!v. read_result cx tv ee = (INL v, ee) ==>
         value_has_type (StructTV fs) v) /\
    ALOOKUP vals fld = SOME fv /\ read_result cx tv' ee = (INL fv, ee) /\
    !tail. select_result cx (StructT sid) tv (AttrSubscript fld)
             (ee with gas_obs := tail) = (INL tv', ee with gas_obs := tail)
Proof
  strip_tac >> drule attr_pre_base >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env obj (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  qpat_x_assum `evaluate_type _ (expr_type obj) = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all attribute_type_evaluates >> strip_tac >>
  rename1 `ALOOKUP fs fld = SOME ftv` >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (rr, ee1)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `rr`
  >- (rename1 `read_result cx tv ee = (INL v, ee)` >>
      `value_has_type (StructTV fs) v` by metis_tac[] >>
      drule struct_value_shape >> strip_tac >> gvs[] >>
      `~popped_at_field tv fld ee` by
        (irule popped_keys_indexed_not_at_field >>
         qspecl_then [`cenv`, `cx`, `env`, `obj`, `es with gas_obs := gs`,
                      `INL tv`, `ee`] mp_tac expr_body_pre_eval_result >>
         simp[expr_sim_inv_def]) >>
      Cases_on `select_result cx (StructT sid) tv (AttrSubscript fld) ee` >>
      rename1 `_ = (sr, ee2)` >>
      `gas_admissible (eval_expr cx (Attribute ann obj fld)) expr_vv_res_ok es`
        by metis_tac[expr_body_pre_vv_gas_admissible] >>
      `expr_vv_res_ok sr` by
        (qpat_x_assum `gas_admissible _ _ _`
           (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
         disch_then (qspecl_then [`gs`, `sr`, `ee2`] mp_tac) >>
         impl_tac >- fs[eval_expr_attribute, bind_def] >> simp[]) >>
      `!m. sr <> INR (Error (TypeError m))` by
        (rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
      drule_all select_attr_read >> strip_tac >> gvs[] >>
      qexists_tac `tv'` >> simp[select_attr_gas_obs]) >>
  drule vv_post_failed_read >> metis_tac[]
QED

(* The field's sizes, at the field's address, from the struct's: the field
   lies inside the struct, which lies below the frontier unless it is empty,
   and then the field is empty too. *)
Theorem attr_field_bound_arith[local]:
  !fields fs fld ftv fv (w:bytes32) next.
  fields_layout fields fs /\ ALOOKUP fs fld = SOME ftv /\ val_wf ftv fv /\
  (type_memory_size_fields fs = 0 \/
   w2n w + type_memory_size_fields fs <= next) /\
  next < dimword (:256) ==>
  (val_store_size ftv fv = 0 \/
   w2n (w + n2w (struct_field_offset fields fld)) + val_store_size ftv fv
     <= next) /\
  (type_memory_size ftv = 0 \/
   w2n (w + n2w (struct_field_offset fields fld)) + type_memory_size ftv
     <= next)
Proof
  rpt gen_tac >> strip_tac >> drule_all struct_field_offset_le >> strip_tac >>
  drule val_store_size_le >> strip_tac
  >- (`type_memory_size ftv = 0` by decide_tac >> simp[]) >>
  `w2n (w + n2w (struct_field_offset fields fld)) =
   w2n w + struct_field_offset fields fld` by
    (irule field_ptr_w2n >>
     qexistsl_tac [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
     simp[]) >>
  simp[]
QED

(* The field's store bound, from the base's: a struct base in memory is
   either a located struct or a stack pointer to one. *)
Theorem attr_field_store_bound[local]:
  !ctx func cenv cx ann obj fld es sa sb s0 ee tv' dst bvv u
   tv sid fs ftv vals fv w t.
    vv_post ctx func cenv cx (Attribute ann obj fld) es sa sb s0 ee tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u /\
    vv_store_bound cx (StructT sid) (lowered_value_type cenv obj) ee tv bvv t /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    read_result cx tv ee = (INL (StructV vals), ee) /\
    (!v. read_result cx tv ee = (INL v, ee) ==>
         value_has_type (StructTV fs) v) /\
    ALOOKUP vals fld = SOME fv /\ read_result cx tv' ee = (INL fv, ee) /\
    eval_operand (vv_operand bvv) t = SOME w /\
    eval_operand dst u =
      SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
    u.vs_alloca_next = t.vs_alloca_next ==>
    vv_store_bound cx ann ann ee tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vv_loc bvv = LocMemory`
  >- (`type_memory_size_fields fs = 0 \/
       w2n w + type_memory_size_fields fs <= t.vs_alloca_next` by
        (qpat_x_assum `vv_store_bound _ (StructT _) _ _ _ _ _`
           (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_store_bound_def]) >>
         Cases_on `bvv` >>
         gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def,
             val_store_size_def, type_memory_size_def] >>
         metis_tac[]) >>
      `value_has_type (StructTV fs) (StructV vals)` by metis_tac[] >>
      drule value_has_type_memory_wf >> strip_tac >>
      `val_wf ftv fv` by
        (irule fields_val_wf_field >> gvs[val_wf_def, value_has_type_def] >>
         metis_tac[]) >>
      `u.vs_alloca_next < dimword (:256)` by
        metis_tac[vv_post_def, stmt_state_rel_def, alloca_room_next_lt] >>
      qspecl_then
        [`get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)`,
         `fs`, `fld`, `ftv`, `fv`, `w`, `u.vs_alloca_next`]
        mp_tac attr_field_bound_arith >>
      impl_tac >- gvs[] >>
      strip_tac >>
      gvs[vv_store_bound_def, mk_ptr_def, attr_offset_def]) >>
  irule vv_store_bound_nonmem >> simp[mk_ptr_def]
QED

(* The field read's code after the base's: the ADD of the field offset,
   and the field's value judgment at its end. *)
Theorem attr_step[local]:
  expr_body_pre cenv cx env (Attribute ann obj fld) es /\
  expr_type obj = StructT sid /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME ann /\
  compile_expr cenv ty obj sa = (bvv, sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv;
               Lit (n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld))]
    sm = (dst, sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx obj es sa sm s0 ee tv bvv t /\
  vv_store_bound cx (StructT sid) (lowered_value_type cenv obj) ee tv bvv t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\
  eval_expr cx obj (es with gas_obs := gs) = (INL tv, ee) ==>
  ?tv' u.
    (!tail. select_result cx (StructT sid) tv (AttrSubscript fld)
              (ee with gas_obs := tail) = (INL tv', ee with gas_obs := tail)) /\
    gas_path_mem ctx func t 0 (OK u) /\
    vv_post ctx func cenv cx (Attribute ann obj fld) es sa sb s0 ee tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u /\
    vv_store_bound cx ann ann ee tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule_all attr_select_field >> strip_tac >>
  `?w. eval_operand (vv_operand bvv) t = SOME w` by
    (gvs[vv_post_def] >> Cases_on `bvv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  drule_all attr_add_counted_post >> strip_tac >>
  rename1 `gas_path_mem ctx func t 0 (OK u)` >>
  `vv_post ctx func cenv cx (Attribute ann obj fld) es sa sb s0 ee tv'
     (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u` by
    (irule attr_vv_post >> simp[] >> qexists_tac `tv` >> gvs[]) >>
  qexistsl_tac [`tv'`, `u`] >> simp[] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ann`, `obj`, `fld`, `es`, `sa`,
               `sb`, `s0`, `ee`, `tv'`, `dst`, `bvv`, `u`, `tv`, `sid`, `fs`,
               `ftv`, `vals`, `fv`, `w`, `t`]
    mp_tac attr_field_store_bound >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem compile_attribute_vv_sim_mem:
  !ctx func cenv cx env ty ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_vv_sim_mem ctx func cenv cx ty obj es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ obj _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (assume_tac o MATCH_MP gas_outcome_link) >>
  simp[eval_attr_bind] >>
  irule forced_vv_then_outcome >> simp[] >>
  qexists_tac `\tv ee t.
    vv_post ctx func cenv cx obj es sa sm s0 ee tv bvv t /\
    vv_store_bound cx (StructT sid) (lowered_value_type cenv obj) ee tv bvv t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ?gs. eval_expr cx obj (es with gas_obs := gs) = (INL tv, ee)` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      `ee with gas_obs := [] = ee` by
        simp[vyperStateTheory.evaluation_state_component_equality] >>
      drule_all attr_step >> strip_tac >>
      qexistsl_tac [`INL tv'`, `ee`, `OK u`] >>
      fs[gas_marked_path_def, expr_type_def,
         exprLoweringTheory.lowered_value_type_def]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                         gas_outcome_post_mono)) >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
