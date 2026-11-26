(* Select from the saved value, not from the original source place. *)
Theory bodyCopiedArrayFixedSelectMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyArrayFramedMemoryAddressMods
  bodyFullSubscriptArrayCodeBounds bodyFullPathHistory bodyForRangeScalarFrameMods
  gasOutcomeFullPostMods exprSimSubscriptArrayFramed exprSimSubscriptArraySource
  exprSimSubscriptArraySuffix exprSimWordArgs exprSimHash exprSimCopy
  exprLoweringProps loweringStateRelDefs vyperArray stmtSimForArray
  overflowElimHelpers vyperValueOperation valueTypingMemoryProps
  words integer_word finite_map pair exprSimArrayIndex compileEnv fragExec loweringShapeRules
  bodyPtrDefs ptrDiscipline venomState vyperState vyperTyping context
  loweringPosts bodyFullPostsMods bodyFullShadowBodyInv fragGasOriginPtr exprSimDefs
  vyperAssignPreservesType vyperTypeValues arithmetic valueEncoding exprSimBopRestWordLoads exprSimProps
  exprSimMemDefs exprLowering vyperAST stateRelProj freshWrites bodyFullUnwrapRun
  bodyFullHashKeccakFixed
Libs
  monadsyntax

Theorem copied_fixed_code[local]:
  compile_array_subscript bop iop F n ws sz signed loader si = (dst,sb) /\
  fn_has_code si sb fn ==>
  ?sc sm offset out.
    array_bounds_check iop (Lit (n2w n)) signed si = ((),sc) /\
    fn_has_code si sc fn /\
    emit_op MUL [iop;Lit (n2w sz)] sc = (Var offset,sm) /\
    emit_op ADD [bop;Var offset] sm = (Var out,sb) /\ dst = Var out
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  rename1 `array_bounds_check _ _ _ si = ((),sc)` >>
  `ci_mono si sc` by
    (qpat_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
     Cases_on `signed` >> simp[NoAsms, array_bounds_check_def, array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_emit_void, irule ci_mono_comp_return])) >>
  `ci_mono sc sb` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
     simp[NoAsms, array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op, irule ci_mono_comp_return])) >>
  `fn_has_code si sc fn` by metis_tac[fn_has_code_split, ci_mono_def] >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[]
QED

Theorem copied_fixed_key_range[local]:
  n < dimword (:256) /\ i = (if signed then w2i iw else &(w2n iw)) ==>
  (idx_in_range signed iw (n2w n) <=> 0 <= i /\ Num i < n) /\
  (idx_in_range signed iw (n2w n) ==> w2n iw = Num i)
Proof
  strip_tac >>
  `idx_in_range signed iw (n2w n) <=> 0 <= i /\ i < &n` by
    (drule idx_in_range_integer >> disch_then (qspecl_then [`iw`,`signed`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `i = _` kall_tac >> simp[] >> intLib.COOPER_TAC) >>
  disch_tac >> `0 <= i` by fs[] >>
  Cases_on `signed` >> gvs[] >>
  drule overflowElimHelpersTheory.nonneg_w2i_eq_w2n >> simp[]
QED

Theorem copied_fixed_reject[local]:
  copied_cursor_mods ctx fn si z /\ allocas_from lo z /\ fin.gas_obs = [] /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  ~valid_index (ArrayTV etv (Fixed n)) av i /\
  array_bounds_check iop (Lit (n2w n)) signed si = ((),sc) /\ fn_has_code si sc fn /\
  eval_operand iop z = SOME iw /\ ~idx_in_range signed iw (n2w n) /\
  op_taint ti iop = {} /\ op_prov Gi iop = NONE /\
  (!x. iop = Var x ==> not_fresh_at si x) /\ (!l. iop <> Label l) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (select_result cx (ArrayT et (Fixed n)) (Value (ArrayV av)) (ValueSubscript (IntV i)))
    (fin,z,Gi,ti) Q (copied_vv_exit_mods cx ctx)
Proof
  simp[copied_cursor_mods_def] >> strip_tac >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV av) [ValueSubscript (IntV i)] =
     INR (RuntimeError "evaluate_subscripts array_index")` by
    (irule evaluate_array_subscript_oob >> simp[]) >>
  `!tail. select_result cx (ArrayT et (Fixed n)) (Value (ArrayV av)) (ValueSubscript (IntV i))
      (fin with gas_obs := tail) =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)` by
    (drule select_value_result >> simp[bind_def,lift_sum_def,raise_def]) >>
  `eval_operand (Lit (n2w n)) z = SOME (n2w n) /\
   op_taint ti (Lit (n2w n)) = {} /\ op_prov Gi (Lit (n2w n)) = NONE /\
   (!x. iop = Var x \/ Lit (n2w n) = Var x ==> not_fresh_at si x) /\
   (!l. iop <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  drule_all array_bounds_check_joint_oob_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tf`,`t`] strip_assume_tac)) >>
  irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`Gf`,`fin`,`Abort Revert_abort t`,
    `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tf`] >>
  simp[exit_result_def,copied_vv_exit_mods_def,expr_exit_def,halt_exit_def]
QED

Theorem copied_fixed_element_memory[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v /\
  0 <= i /\ Num i < n /\ k = Num i * type_memory_size etv /\
  w2n (w:bytes32) + type_memory_size (ArrayTV etv (Fixed n)) < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
      val_in_memory (ArrayTV etv (Fixed n)) (ArrayV av) (w2n w) m) ==>
  value_has_type etv v /\ val_wf etv v /\
  w2n (w + n2w k) = w2n w + k /\
  k + type_memory_size etv <= type_memory_size (ArrayTV etv (Fixed n)) /\
  (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
      val_in_memory etv v (w2n w + k) m)
Proof
  strip_tac >>
  drule_then assume_tac evaluate_type_well_formed_type_value >>
  `value_has_type etv v` by
    (irule array_index_has_type >> simp[] >> qexistsl_tac [`av`,`Fixed n`,`i`] >> simp[]) >>
  `val_wf etv v /\ val_wf (ArrayTV etv (Fixed n)) (ArrayV av)` by
     simp[value_has_type_memory_wf] >>
  simp[] >> rpt conj_tac
  >- (irule fixed_array_element_nonwrapping >>
      goal_assum (drule_at (Pat `array_index _ _ _ = _`)) >> simp[val_footprint_def])
  >- (`(Num i + 1) * type_memory_size etv <= n * type_memory_size etv` by
        (irule LESS_MONO_MULT >> decide_tac) >>
      qpat_x_assum `(Num i + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB,MULT_LEFT_1,type_memory_size_def] >> decide_tac) >>
  rpt strip_tac >>
  `&(Num i) = i` by intLib.COOPER_TAC >>
  `array_index (ArrayTV etv (Fixed n)) av (&(Num i)) = SOME v` by simp[] >>
  `val_in_memory (ArrayTV etv (Fixed n)) (ArrayV av) (w2n w) m` by simp[] >>
  drule_all rest_word_array_memory_index >> simp[]
QED

Theorem copied_fixed_element_own[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\ val_wf etv v /\
  lookup_var out t = SOME dw /\ w2n dw = w2n (w:bytes32) + k /\
  k + type_memory_size etv <= bytes /\
  FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,bytes) /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  (!name b len. local_region ce fin.scopes t name b len ==>
      regions_disjoint (w2n w) bytes b len) ==>
  vv_at ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) t /\
  vv_own ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) t
Proof
  strip_tac >> `val_footprint etv v <= type_memory_size etv` by simp[val_footprint_le] >>
  simp[vv_at_def,vv_own_def,read_result_def,return_def,mk_ptr_def,eval_operand_def] >>
  conj_tac >> disj1_tac >> qexistsl_tac [`sm.cs_next_id`,`w2n w`,`bytes`] >>
  fs[regions_disjoint_def, ADD_COMM] >> first_assum ACCEPT_TAC
QED

Theorem copied_fixed_element_bytes[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\ value_has_type etv v /\ val_wf etv v /\
  lookup_var out t = SOME dw /\ w2n dw = w2n w + k /\
  (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory etv v (w2n dw) m) /\
  k + type_memory_size etv <= bytes /\ w2n w + bytes <= t.vs_alloca_next /\
  op_prov Gf (Var out) = op_prov Gi (Var q) /\ op_taint tf (Var out) = {} /\
  ptr_covers Gi ti q z bytes /\ lookup_var q z = SOME w /\
  type_memory_bytes ce et = type_memory_size etv ==>
  vv_holds_mods ce cx et (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) fin t /\
  vv_store_bound cx et et fin (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) t /\
  ptr_vv_ok cx et (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) fin Gf tf t /\
  ptr_buf_ok ce (Subscript et obj idx) (Var out) Gf t
Proof
  strip_tac >>
  `val_footprint etv v <= type_memory_size etv /\ val_store_size etv v <= type_memory_size etv` by
    simp[val_store_size_le,val_footprint_le] >>
  `val_in_memory etv v (w2n dw) t.vs_memory` by fs[mem_agree_outside_def] >>
  `ptr_covers Gf tf out t (type_memory_size etv)` by
    (fs[ptr_covers_def,op_prov_def] >> goal_assum (drule_at (Pat `FLOOKUP Gf out = _`)) >>
     simp[] >> decide_tac) >>
  conj_tac
  >- (simp[vv_holds_mods_def,vv_holds_def,mk_ptr_def,read_result_def,return_def,eval_operand_def] >>
      strip_tac >> drule_all val_in_memory_word_type >> simp[]) >>
  conj_tac
  >- (simp[vv_store_bound_def,mk_ptr_def,read_result_def,return_def,eval_operand_def] >> decide_tac) >>
  qpat_x_assum `ptr_covers Gf _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  fs[ptr_vv_ok_def,ptr_mem_ok_def,ptr_buf_ok_def,mk_ptr_def,read_result_def,return_def,
     eval_operand_def,lowered_value_type_def,vyperASTTheory.expr_type_def] >>
  gvs[] >> rpt strip_tac >> decide_tac
QED

Theorem copied_fixed_linked_post[local]:
  copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) fin (Subscript et obj idx) (si,z,Gi,ti) /\
  sa.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x z /\
       FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x)) /\
  t.vs_memory = z.vs_memory /\ t.vs_allocas = z.vs_allocas /\
  t.vs_alloca_next = z.vs_alloca_next /\ t.vs_data_section = z.vs_data_section /\
  t.vs_call_ctx = z.vs_call_ctx /\ t.vs_accounts = z.vs_accounts /\
  t.vs_transient = z.vs_transient /\ t.vs_immutables = z.vs_immutables /\
  tf.t_mem = ti.t_mem /\ tf.t_stor = ti.t_stor /\ tf.t_trans = ti.t_trans /\ tf.t_imm = ti.t_imm /\
  stmt_state_rel H ctx fn ce cx fin t /\ valid_horizon cx st0 H fin.storage_trace /\
  vv_holds_mods ce cx et (Value v) (LocatedValue et (mk_ptr dst LocMemory)) fin t /\
  vv_at ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr dst LocMemory)) t ==>
  vv_post_mods H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
    (Value v) (LocatedValue et (mk_ptr dst LocMemory)) t /\
  ghost_inv_at_mods (DF H) lo d ce cx fin Gf tf t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  simp[copied_parent_frame_mods_def] >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _` (drule_then strip_assume_tac) >>
  `wb_frame ce es fin sa s0 t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`si`,`z`] >> simp[]) >>
  `~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 t` by
    (simp[] >> strip_tac >> irule pure_frame_mem_tail >> qexists_tac `z` >> simp[]) >>
  conj_tac
  >- (`immutable_frame_mods fn ce cx fin t` by
        (irule immutable_frame_mods_exterior_frame >>
         goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >> qexists_tac `si` >> simp[]) >>
      fs[vv_post_mods_def, wb_frame_def, vv_place_ptr_mods_def, vv_place_ptr_def,
         mk_ptr_def, expr_type_def] >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> not_fresh_at si x` by metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `sa` >> simp[] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at si x ==> _` drule >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`Gi`,`ti`] >> simp[] >> rpt strip_tac >>
  qpat_assum `!x. not_fresh_at si x ==> _` drule >> simp[]
QED

Theorem copied_array_fixed_select_mods:
  copied_select_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,Fixed n,atv)
    (et,idx,fin,IntV i,iop,dst,vv) (sm,sc,cvv) (si,z,Gi,ti) sb (q,w) /\
  sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  type_memory_bytes ce et = type_memory_size etv /\ evaluate_type (get_tenv cx) et = SOME etv /\
  is_word_type (post_value_type ce idx) /\
  eval_operand iop z = SOME iw /\ i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  (!x. iop = Var x ==> not_fresh_at si x) /\ (!l. iop <> Label l) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shctx,ctx,fn,PG) ce.ce_modules cx st0
    (select_result cx (ArrayT et (Fixed n)) (Value saved) (ValueSubscript (IntV i))) (fin,z,Gi,ti)
    (copied_located_post_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (et,obj,idx) (es,sa,s0,G0,tn0) (sb,vv)) (copied_vv_exit_mods cx ctx)
Proof
  strip_tac >>
  qpat_x_assum `copied_select_cut_mods _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [copied_select_cut_mods_def]) >>
  qpat_x_assum `copied_array_type_mods _ _ _` (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  `n < dimword (:256)` by (drule evaluated_fixed_array_bound >> simp[]) >>
  drule_all_then strip_assume_tac copied_fixed_key_range >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `atv = ArrayTV etv (Fixed n)` by
    (drule_then strip_assume_tac evaluate_type_ArrayT_cases >> gvs[]) >>
  gvs[elem_size_in_location_def,is_slot_addressed_def] >>
  `?av. saved = ArrayV av` by (Cases_on `saved` >> fs[value_has_type_def]) >>
  qpat_x_assum `saved = ArrayV _` SUBST_ALL_TAC >>
  `valid_index (ArrayTV etv (Fixed n)) av i <=> idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)` by
    (Cases_on `av` >> fs[value_has_type_def,valid_index_def,vyperValueOperationTheory.array_length_def] >>
     intLib.COOPER_TAC) >>
  drule_all_then strip_assume_tac copied_fixed_code >>
  `op_taint ti iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)`
  >- suspend "in_bounds" >>
  `~valid_index (ArrayTV etv (Fixed n)) av i` by fs[] >>
  irule copied_fixed_reject >> simp[] >>
  qpat_assum `array_bounds_check _ _ _ _ = _` (irule_at Any) >>
  qexists_tac `iw` >> fs[valid_index_def]
QED

Resume copied_array_fixed_select_mods[in_bounds]:
  `valid_index (ArrayTV etv (Fixed n)) av i /\ 0 <= i /\ Num i < n /\ w2n iw = Num i` by fs[] >>
  `?v. array_index (ArrayTV etv (Fixed n)) av i = SOME v` by
    (drule array_index_valid >> simp[optionTheory.IS_SOME_EXISTS]) >>
  pop_assum strip_assume_tac >>
  `!tail. select_result cx (ArrayT et (Fixed n)) (Value (ArrayV av)) (ValueSubscript (IntV i))
      (fin with gas_obs := tail) = (INL (Value v),fin with gas_obs := tail)` by
    (drule select_value_result >> simp[evaluate_array_subscript_result,bind_def,lift_sum_def,return_def]) >>
  qpat_assum `copied_snapshot_dest_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_snapshot_dest_mods_def]) >>
  qpat_assum `copied_cursor_mods _ _ _ _` (strip_assume_tac o REWRITE_RULE [copied_cursor_mods_def]) >>
  `eval_operand (Var q) z = SOME w /\ op_taint ti (Var q) = {}` by
    (simp[eval_operand_def] >> fs[ptr_covers_def]) >>
  `!x. Var q = Var x ==> not_fresh_at si x` by simp[] >>
  `!l. Var q <> Label l` by simp[] >>
  drule_all (framed_memory_fixed_address_run
    |> INST_TYPE [Type.alpha |-> ``:256``]
    |> Q.INST [`i` |-> `w2n (iw:bytes32)`] |> SRULE []) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tf`,`t`] strip_assume_tac)) >>
  pop_assum (mk_asm "selector_state") >>
  suspend "element"
QED

Resume copied_array_fixed_select_mods[element]:
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  qabbrev_tac `k = Num i * type_memory_size etv` >>
  `k = Num i * type_memory_size etv` by simp[Abbr `k`] >>
  drule_all_then strip_assume_tac copied_fixed_element_memory >>
  qpat_x_assum `lookup_var out t = SOME _` (mp_tac) >>
  qpat_assum `w2n iw = Num i` (fn th => pure_once_rewrite_tac[th]) >>
  qpat_assum `k = Num i * _` (fn th => pure_once_rewrite_tac[GSYM th]) >> strip_tac >>
  `si.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     pure_rewrite_tac[SND] >> disch_then (SUBST1_TAC o SYM) >>
     irule (cj 3 (iffLR ci_mono_def)) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `sm.cs_next_id < sb.cs_next_id` by decide_tac >>
  `!name b len. local_region ce fin.scopes t name b len ==>
       regions_disjoint (w2n w) (type_memory_size (ArrayTV etv (Fixed n))) b len` by
    (rpt strip_tac >>
     `local_region ce fin.scopes z name b len` suffices_by
       (qpat_assum `!nm a sz. local_region _ _ z nm a sz ==> _` (qspecl_then [`name`,`b`,`len`] ACCEPT_TAC)) >>
     `local_ptrs_reserved ce si` by fs[copied_parent_frame_mods_def] >>
     `local_region ce fin.scopes t name b len <=> local_region ce fin.scopes z name b len` suffices_by simp[] >>
     irule copy_buffer_local_region_frame >> qexists_tac `si` >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at si x ==> _` drule >> simp[]) >>
  `FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size (ArrayTV etv (Fixed n)))` by simp[] >>
  `vv_at ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) t /\
   vv_own ce cx et sa sb fin (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) t` by
    (irule copied_fixed_element_own >>
     qexistsl_tac [`type_memory_size (ArrayTV etv (Fixed n))`,`w + n2w k`,`etv`,`k`,`sm`,`w`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `k = Num i * _` kall_tac >>
  `!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory etv v (w2n (w + n2w k)) m` by
    (asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  `vv_holds_mods ce cx et (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) fin t /\
   vv_store_bound cx et et fin (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) t /\
   ptr_vv_ok cx et (Value v) (LocatedValue et (mk_ptr (Var out) LocMemory)) fin Gf tf t /\
   ptr_buf_ok ce (Subscript et obj idx) (Var out) Gf t` by
    (`w2n w + type_memory_size (ArrayTV etv (Fixed n)) <= t.vs_alloca_next` by asm_rewrite_tac[] >>
     irule copied_fixed_element_bytes >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gi`,`type_memory_size (ArrayTV etv (Fixed n))`,`w + n2w k`,
                  `etv`,`k`,`q`,`ti`,`w`,`z`] >> asm_rewrite_tac[]) >>
  suspend "outcome"
QED

Resume copied_array_fixed_select_mods[outcome]:
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`,`fin`,`INL (Value v)`,`t`,`tf`] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[] >> rpt strip_tac >>
  qpat_assum `copied_parent_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx fn ce cx fin t` by
    (asm "selector_state" irule >> asm_rewrite_tac[]) >>
  `alloca_inv z` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ z`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fn,PG) (z,Gi,ti) [] (OK t,Gf,tf)` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ t` (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  drule_all_then strip_assume_tac copied_fixed_linked_post >>
  simp[copied_located_post_mods_def,expr_type_def,lowered_value_type_def] >>
  qexists_tac `Var out` >> simp[]
QED

Finalise copied_array_fixed_select_mods
