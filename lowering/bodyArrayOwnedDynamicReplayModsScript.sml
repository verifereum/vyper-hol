(* Dynamic array selection from an owned, already reached Value. *)
Theory bodyArrayOwnedDynamicReplayMods
Ancestors
  bodyArrayOwnedSelectViewMods bodyFullSubscriptCapturedDynamicRun
  exprSimSubscriptArraySource typedCopyLayoutPtr exprSimVVFrame exprSimCopy
  exprSimIfExpWidenedOwnedProvenance valueEncoding valueEncodingProps valueEncodingTyping
  loweringPosts bodyPtrDefs ptrDiscipline bodyFullTargetArrayLoad
  exprLowering exprSimProps exprSimMemDefs compileEnv context
  vyperInterpreter vyperState vyperAST vyperTyping words fragExec venomState

Theorem owned_dynamic_child_region[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type tv (EL j vs) /\ j < LENGTH vs /\
  vv_own ce cx (ArrayT et (Dynamic cap)) sa sn fin
    (Value (ArrayV (DynArrayV vs)))
    (LocatedValue (ArrayT et (Dynamic cap)) (mk_ptr bop LocMemory)) u /\
  eval_operand bop u = SOME a /\ eval_operand bop q = SOME a /\
  eval_operand dst q = SOME w /\ w2n w = w2n a + (32 + j * type_memory_size tv) /\
  q.vs_allocas = u.vs_allocas /\ sn.cs_next_id <= sb.cs_next_id /\
  (!nm b sz. local_region ce fin.scopes q nm b sz ==> local_region ce fin.scopes u nm b sz) ==>
  vv_own ce cx et sa sb fin (Value (EL j vs)) (LocatedValue et (mk_ptr dst LocMemory)) q /\
  vv_at ce cx et sa sb fin (Value (EL j vs)) (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  strip_tac >>
  `vv_own ce cx (ArrayT et (Dynamic cap)) sa sb fin
      (Value (ArrayV (DynArrayV vs)))
      (LocatedValue (ArrayT et (Dynamic cap)) (mk_ptr bop LocMemory)) q` by
    (irule vv_own_vars_frame >> qexistsl [`u`,`sn`] >> simp[vv_operand_def,mk_ptr_def]) >>
  drule_all_then assume_tac dynarray_live_child_footprint >>
  `vv_own ce cx et sa sb fin (Value (EL j vs)) (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (irule vv_own_memory_slice >>
     qpat_assum `vv_own _ _ _ _ sb _ _ _ _` (irule_at Any) >>
     simp[read_result_def,return_def] >> rpt (goal_assum (drule_at Any)) >> decide_tac) >>
  simp[] >> irule vv_own_memory_transport >>
  qpat_assum `vv_own _ _ et _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`EL j vs`,`tv`,`tv`] >>
  simp[read_result_def,return_def,value_has_type_val_wf]
QED

Theorem owned_dynamic_child_bytes[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\ value_has_type tv child /\
  eval_operand dst q = SOME w /\ op_taint tm dst = {} /\
  op_prov H dst = SOME (b,sz) /\ b <= w2n w /\
  w2n w + type_memory_size tv <= b + sz /\
  w2n w + type_memory_size tv <= q.vs_alloca_next /\
  type_memory_bytes ce et = type_memory_size tv /\
  (!m. mem_agree_outside tm.t_mem q.vs_memory m ==> val_in_memory tv child (w2n w) m) ==>
  vv_holds ce cx et (Value child) (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  vv_store_bound cx et et fin (Value child) (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_vv_ok cx et (Value child) (LocatedValue et (mk_ptr dst LocMemory)) fin H tm q /\
  ptr_buf_ok ce (Subscript et obj idx) dst H q
Proof
  strip_tac >>
  `val_wf tv child` by simp[value_has_type_val_wf] >>
  `val_store_size tv child <= type_memory_size tv` by simp[val_store_size_le] >>
  `val_in_memory tv child (w2n w) q.vs_memory` by simp[mem_agree_outside_def] >>
  conj_tac
  >- (simp[vv_holds_def, mk_ptr_def, read_result_def, return_def] >>
      strip_tac >> drule_all val_in_memory_word_type >> simp[]) >>
  Cases_on `dst` >> gvs[op_prov_def] >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, mk_ptr_def,
       vv_store_bound_def, lowered_value_type_def, expr_type_def, read_result_def, return_def]
QED

Theorem array_owned_dynamic_replay_mods:
  array_owned_memory_view_mods ce cx (et,Dynamic cap,etv) (sa,st2)
      (fin,v) (bop,it,Gi,tni,a) /\
  compile_array_subscript bop iop T cnt 32 (type_memory_size etv)
      (is_signed_type (expr_type idx)) (\op. emit_op MLOAD [op]) st2 = (dst,sb) /\
  fn_has_code st2 sb func /\
  eval_operand iop it = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  cap < dimword (:256) /\
  op_prov Gi iop = NONE /\ op_taint tni iop = {} /\
  (!x. bop = Var x ==> not_fresh_at st2 x) /\
  (!x. iop = Var x ==> not_fresh_at st2 x) /\
  allocas_from lo it /\ alloca_history func it /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp it) /\ ~it.vs_halted /\
  it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size etv /\
  local_ptrs_reserved ce st2 /\ st2.cs_next_id <= sb.cs_next_id ==>
  array_owned_select_run_mods (lo,explicit,ctx,func,PG) ce cx
    (et,Dynamic cap,obj,idx) (sa,st2,sb,dst) (v,IntV i) (fin,it,Gi,tni)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `array_owned_memory_view_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [array_owned_memory_view_mods_def,LET_THM,type_memory_size_def]) >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  `LENGTH vs < dimword (:256) /\ w2n a + 32 <= it.vs_alloca_next` by decide_tac >>
  drule_all subscript_captured_dynamic_execution >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `!s. select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
         (ValueSubscript (IntV i)) s =
       bind (lift_sum (evaluate_subscripts (ArrayTV etv (Dynamic cap))
         (ArrayV (DynArrayV vs)) [ValueSubscript (IntV i)])) (\w. return (Value w)) s` by
    simp[select_value_result] >>
  rewrite_tac[array_owned_select_run_mods_def] >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))`)
  >- (qexistsl [`INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
                `Abort Revert_abort q`,`H`,`tm`] >>
      fs[bind_def,lift_sum_def,raise_def]) >>
  fs[] >>
  qexistsl [`INL (Value (EL (Num i) vs))`,`OK q`,`H`,`tm`] >>
  simp[bind_def,lift_sum_def,return_def] >>
  qabbrev_tac `w = a + 32w + iw * n2w (type_memory_size etv)` >>
  `q.vs_allocas = it.vs_allocas /\ q.vs_alloca_next = it.vs_alloca_next` by
    (qpat_assum `array_length_frame _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [array_length_frame_def]) >>
     strip_tac >> qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = it`
       (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_allocas,s.vs_alloca_next)`) >> simp[]) >>
  `!x. not_fresh_at st2 x ==> lookup_var x q = lookup_var x it` by
    fs[array_length_frame_def] >>
  `eval_operand bop q = SOME a` by (Cases_on `bop` >> fs[eval_operand_def,op_prov_def]) >>
  `!nm b sz. local_region ce fin.scopes q nm b sz ==> local_region ce fin.scopes it nm b sz` by
    (drule_all copy_buffer_local_region_frame >> simp[]) >>
  `w2n w = w2n a + (32 + Num i * type_memory_size etv)` by decide_tac >>
  drule_all_then strip_assume_tac owned_dynamic_child_region >>
  `SUC (Num i) * type_memory_size etv <= cap * type_memory_size etv` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `base' <= w2n w /\ w2n w + type_memory_size etv <= base' + len /\
   w2n w + type_memory_size etv <= q.vs_alloca_next` by
    (qpat_assum `SUC (Num i) * _ <= _` mp_tac >>
     rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
       val_in_memory etv (EL (Num i) vs) (w2n w) m` by simp[] >>
  drule_all_then (qspecl_then [`obj`,`idx`,`fin`] strip_assume_tac) owned_dynamic_child_bytes >>
  simp[]
QED
