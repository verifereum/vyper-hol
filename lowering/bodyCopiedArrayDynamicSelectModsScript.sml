(* Select from the saved dynamic array, including its own length header. *)
Theory bodyCopiedArrayDynamicSelectMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyCopiedArrayDynamicSelectAdapterMods
  bodyFullSubscriptCapturedDynamicRun
  bodyPtrBopInMemoryContents bodyForRangeScalarFrameMods gasOutcomeFullPostMods
  bodyPtrSignedConvertSourceFrame bodyFullUnwrapRun exprSimWordArgs
  exprSimSubscriptArraySource exprLoweringProps targetSubscriptStorage
  vyperAST vyperTyping vyperTypeValues valueEncodingTyping bodyFullTargetArrayLoad exprSimMemDefs
  bodyPtrDefs ptrDiscipline compileEnv context venomState exprLowering valueEncoding
  fragExec gasExplicitSites words loweringPosts loweringStateRelDefs bodyFullPostsMods
  exprSimProps bodyFullShadowBodyInv finite_map vyperState pred_set
  vyperValueOperation exprSimDefs bodyFullHashKeccakFixed freshWrites
  valueTypingMemoryProps exprSimCopy pair arithmetic
Libs
  monadsyntax

Theorem copied_dynamic_layout[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME atv /\
  value_has_type atv saved ==>
  ?tv vs. atv = ArrayTV tv (Dynamic cap) /\ saved = ArrayV (DynArrayV vs) /\
    evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs < dimword (:256)
Proof
  strip_tac >> drule_then strip_assume_tac evaluate_type_ArrayT_cases >> gvs[] >>
  drule_then strip_assume_tac target_storage_array_type_bound >>
  qpat_x_assum `value_has_type _ saved` mp_tac >>
  Cases_on `saved` >> simp[value_has_type_inv] >>
  qmatch_goalsub_rename_tac `ArrayV av` >> Cases_on `av` >>
  simp[value_has_type_inv,bound_length_def] >> gvs[]
QED

Theorem copied_dynamic_run[local]:
  copied_select_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,ArrayV (DynArrayV vs),et,Dynamic cap,ArrayTV tv (Dynamic cap))
    (ann,idx,fin,IntV i,iop,dst,vv) (sm,sc,cvv) (si,z,Gi,ti) sb (q,w) /\
  type_memory_bytes ce et = type_memory_size tv /\ LENGTH vs < dimword (:256) /\
  is_word_type (post_value_type ce idx) /\ (!x. iop = Var x ==> not_fresh_at si x) /\
  eval_operand iop z = SOME iw /\ i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) ==>
  ?bnd sz u Gu tu.
    bnd <= w2n w /\ w2n w + (32 + cap * type_memory_size tv) <= bnd + sz /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
      (z,Gi,ti) []
      (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))
        then OK u else Abort Revert_abort u,Gu,tu)) /\
    (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs)) then
       0 <= i /\ Num i < LENGTH vs /\
       evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
         [ValueSubscript (IntV i)] = INL (EL (Num i) vs) /\
       value_has_type tv (EL (Num i) vs) /\
       ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn u /\
       eval_operand dst u = SOME (w + 32w + iw * n2w (type_memory_size tv)) /\
       w2n (w + 32w + iw * n2w (type_memory_size tv)) =
         w2n w + 32 + Num i * type_memory_size tv /\
       op_prov Gu dst = SOME (bnd,sz) /\ op_taint tu dst = {} /\
       w2n w + 32 + Num i * type_memory_size tv + type_memory_size tv <= bnd + sz /\
       array_length_frame si z Gi ti u Gu tu /\
       (!m. mem_agree_outside tu.t_mem u.vs_memory m ==>
         val_in_memory tv (EL (Num i) vs) (w2n w + 32 + Num i * type_memory_size tv) m)
     else evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
            [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index"))
Proof
  strip_tac >>
  drule_all_then assume_tac copied_select_compile_dynamic_mload >>
  qhdtm_x_assum `copied_select_cut_mods`
    (strip_assume_tac o REWRITE_RULE [copied_select_cut_mods_def]) >>
  qhdtm_x_assum `copied_array_type_mods`
    (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  qhdtm_x_assum `copied_snapshot_dest_mods`
    (strip_assume_tac o SRULE [copied_snapshot_dest_mods_def,type_memory_size_def]) >>
  qhdtm_x_assum `copied_cursor_mods`
    (strip_assume_tac o REWRITE_RULE [copied_cursor_mods_def]) >>
  `mem_word_taint ti.t_mem (w2n w) = {}` by
    (drule_then ACCEPT_TAC dynarray_memory_header_clean) >>
  qhdtm_x_assum `ptr_covers` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  `w' = w` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `w' = w` SUBST_ALL_TAC >>
  `w2n w + 32 <= z.vs_alloca_next` by decide_tac >>
  rename1 `FLOOKUP Gi q = SOME (pbase,plen)` >>
  `eval_operand (Var q) z = SOME w /\ op_prov Gi (Var q) = SOME (pbase,plen) /\
   op_taint ti (Var q) = {} /\ (!x. Var q = Var x ==> not_fresh_at si x)` by
    simp[eval_operand_def,op_prov_def,op_taint_def] >>
  `op_prov Gi iop = NONE /\ op_taint ti iop = {}` by fs[ptr_val_ok_def] >>
  drule_all (subscript_captured_dynamic_execution |> Q.INST [`cnt` |-> `0`]) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`]
    (qx_choosel_then [`send`,`Gend`,`tend`] strip_assume_tac)) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qexistsl_tac [`pbase`,`plen`,`send`,`Gend`,`tend`] >> asm_rewrite_tac[]
QED

Theorem copied_array_dynamic_select_mods:
  copied_select_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,Dynamic cap,atv)
    (et,idx,fin,IntV i,iop,dst,vv) (sm,sc,cvv) (si,z,Gi,ti) sb (q,w) /\
  sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  type_memory_bytes ce et = type_memory_size etv /\ evaluate_type (get_tenv cx) et = SOME etv /\
  is_word_type (post_value_type ce idx) /\
  eval_operand iop z = SOME iw /\ i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  (!x. iop = Var x ==> not_fresh_at si x) /\ (!l. iop <> Label l) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shctx,ctx,fn,PG) ce.ce_modules cx st0
    (select_result cx (ArrayT et (Dynamic cap)) (Value saved) (ValueSubscript (IntV i))) (fin,z,Gi,ti)
    (copied_located_post_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (et,obj,idx) (es,sa,s0,G0,tn0) (sb,vv)) (copied_vv_exit_mods cx ctx)
Proof
  strip_tac >>
  qhdtm_assum `copied_select_cut_mods`
    (strip_assume_tac o REWRITE_RULE [copied_select_cut_mods_def]) >>
  qhdtm_x_assum `copied_array_type_mods`
    (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  drule_all_then (qx_choosel_then [`tv`,`vs`] strip_assume_tac) copied_dynamic_layout >>
  `tv = etv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tv = etv` SUBST_ALL_TAC >>
  qpat_x_assum `saved = ArrayV _` SUBST_ALL_TAC >>
  qpat_x_assum `atv = _` SUBST_ALL_TAC >>
  drule_all_then (qx_choosel_then [`bnd`,`sz`,`u`,`Gu`,`tu`] strip_assume_tac) copied_dynamic_run >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qhdtm_assum `copied_cursor_mods`
    (strip_assume_tac o REWRITE_RULE [copied_cursor_mods_def]) >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))`)
  >- (fs[] >>
      `!tail. select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
          (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
        (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)` by
        (qpat_assum `evaluate_type _ (ArrayT _ _) = SOME _`
           (mp_then Any (fn th => simp[th,bind_def,lift_sum_def,raise_def]) select_value_result)) >>
      irule gas_outcome_full_mods_exit >> simp[] >>
      qexistsl_tac [`Gu`,`fin`,`Abort Revert_abort u`,
        `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tu`] >>
      simp[exit_result_def,copied_vv_exit_mods_def,expr_exit_def,halt_exit_def]) >>
  fs[] >> suspend "selected"
QED

Resume copied_array_dynamic_select_mods[selected]:
  qabbrev_tac `v = EL (Num i) vs` >>
  `!tail. select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
        (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
      (INL (Value v),fin with gas_obs := tail)` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = SOME _`
      (mp_then Any (fn th => simp[th,bind_def,lift_sum_def,return_def]) select_value_result)) >>
  qhdtm_x_assum `array_length_frame`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  `u = z with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
   u.vs_memory = z.vs_memory /\ u.vs_allocas = z.vs_allocas /\
   u.vs_alloca_next = z.vs_alloca_next /\ u.vs_data_section = z.vs_data_section /\
   u.vs_call_ctx = z.vs_call_ctx /\ u.vs_accounts = z.vs_accounts /\
   u.vs_transient = z.vs_transient /\ u.vs_immutables = z.vs_immutables` by
    (qpat_assum `(u with vs_inst_idx := _) with vs_vars := _ = z` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at si x ==> lookup_var x u = lookup_var x z /\
        FLOOKUP Gu x = FLOOKUP Gi x /\ op_taint tu (Var x) = op_taint ti (Var x)` by
    simp[op_taint_def] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gu`,`fin`,`INL (Value v)`,`u`,`tu`] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[] >> rpt strip_tac >> suspend "post"
QED

Resume copied_array_dynamic_select_mods[post]:
  qhdtm_x_assum `copied_parent_frame_mods`
    (strip_assume_tac o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx fn ce cx fin u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`z`,`si`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ u`
      (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `!x. not_fresh_at sa x ==> not_fresh_at si x` by metis_tac[not_fresh_at_mono] >>
  `wb_frame ce es fin sa s0 u` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`si`,`z`] >> simp[]) >>
  `~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u` by
    (strip_tac >> irule pure_frame_mem_tail >> qexists_tac `z` >> simp[]) >>
  `immutable_frame_mods fn ce cx fin u` by
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     qexists_tac `si` >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d ce cx fin Gu tu u` by
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at si x ==> _` drule >> simp[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`Gi`,`ti`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at si x ==> _` drule >> simp[]) >>
  suspend "element"
QED

Resume copied_array_dynamic_select_mods[element]:
  qhdtm_x_assum `copied_snapshot_dest_mods`
    (strip_assume_tac o REWRITE_RULE [copied_snapshot_dest_mods_def]) >>
  `si.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     pure_rewrite_tac[SND] >> disch_then (SUBST1_TAC o SYM) >>
     irule (cj 3 (iffLR ci_mono_def)) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `sm.cs_next_id < sb.cs_next_id` by decide_tac >>
  `!name b len. local_region ce fin.scopes u name b len ==>
       regions_disjoint (w2n w) (type_memory_size (ArrayTV etv (Dynamic cap))) b len` by
    (rpt strip_tac >>
     `local_region ce fin.scopes u name b len <=> local_region ce fin.scopes z name b len` by
       (irule copy_buffer_local_region_frame >> qexists_tac `si` >> simp[]) >>
     `local_region ce fin.scopes z name b len` by fs[] >>
     qpat_assum `!n b len. local_region _ _ z n b len ==> _` (drule_then ACCEPT_TAC)) >>
  `LENGTH vs <= cap` by fs[value_has_type_def] >>
  `(Num i + 1) * type_memory_size etv <= cap * type_memory_size etv` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  `Num i * type_memory_size etv + type_memory_size etv <= cap * type_memory_size etv` by
    (qpat_x_assum `(Num i + 1) * _ <= _` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB,MULT_LEFT_1] >> simp[]) >>
  `val_wf etv v` by simp[value_has_type_memory_wf] >>
  `val_footprint etv v <= type_memory_size etv /\ val_store_size etv v <= type_memory_size etv` by
    simp[val_store_size_le,val_footprint_le] >>
  qabbrev_tac `dw = w + 32w + iw * n2w (type_memory_size etv)` >>
  `w2n w <= w2n dw /\
   w2n dw + type_memory_size etv <= w2n w + type_memory_size (ArrayTV etv (Dynamic cap))` by
    (simp[type_memory_size_def] >> decide_tac) >>
  `w2n dw + val_footprint etv v <= w2n w + type_memory_size (ArrayTV etv (Dynamic cap))` by
    decide_tac >>
  `vv_at ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) u /\
   vv_own ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) u` by
    (simp[vv_at_def,vv_own_def,mk_ptr_def,read_result_def,return_def] >>
     conj_tac >> disj1_tac >>
     qexistsl_tac [`sm.cs_next_id`,`w2n w`,`type_memory_size (ArrayTV etv (Dynamic cap))`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!n b len. local_region _ _ u n b len ==> _`
       (drule_then (mp_tac o REWRITE_RULE [regions_disjoint_def])) >> simp[]) >>
  suspend "bytes"
QED

Resume copied_array_dynamic_select_mods[bytes]:
  `!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory etv v (w2n dw) m` by simp[] >>
  `val_in_memory etv v (w2n dw) z.vs_memory` by simp[mem_agree_outside_def] >>
  `w2n dw + type_memory_size etv <= u.vs_alloca_next` by decide_tac >>
  `w2n dw + type_memory_size etv <= bnd + sz /\ bnd <= w2n dw` by decide_tac >>
  `vv_holds_mods ce cx et (Value v) (LocatedValue et (mk_ptr dst LocMemory)) fin u` by
    (simp[vv_holds_mods_def,vv_holds_def,mk_ptr_def,read_result_def,return_def] >>
     strip_tac >> drule_all val_in_memory_word_type >> simp[]) >>
  `vv_store_bound cx et et fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) u` by
    (simp[vv_store_bound_def,mk_ptr_def,read_result_def,return_def] >> decide_tac) >>
  `?x. dst = Var x /\ FLOOKUP Gu x = SOME (bnd,sz)` by
    (Cases_on `dst` >> fs[op_prov_def]) >>
  `ptr_vv_ok cx et (Value v) (LocatedValue et (mk_ptr dst LocMemory)) fin Gu tu u /\
   ptr_buf_ok ce (Subscript et obj idx) dst Gu u` by
    (qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
     simp[ptr_vv_ok_def,ptr_mem_ok_def,ptr_buf_ok_def,mk_ptr_def,read_result_def,return_def,
          lowered_value_type_def,vyperASTTheory.expr_type_def] >>
     decide_tac) >>
  `vv_post_mods H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
     (Value v) (LocatedValue et (mk_ptr dst LocMemory)) u` by
    (fs[vv_post_mods_def,wb_frame_def,vv_place_ptr_mods_def,vv_place_ptr_def,mk_ptr_def,
        vyperASTTheory.expr_type_def] >> first_assum ACCEPT_TAC) >>
  rename1 `dst = Var dstvar` >>
  qpat_x_assum `dst = Var dstvar` SUBST_ALL_TAC >>
  simp[copied_located_post_mods_def,vyperASTTheory.expr_type_def,lowered_value_type_def] >>
  qexists_tac `Var dstvar` >> simp[]
QED

Finalise copied_array_dynamic_select_mods
