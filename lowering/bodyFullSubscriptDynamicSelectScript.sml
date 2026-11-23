(* Selection at the counted dynamic-memory array suffix. *)
Theory bodyFullSubscriptDynamicSelect
Ancestors
  bodyFullSubscriptCapturedDynamicRun bodyFullTargetArrayLoad
  exprSimSubscriptArraySource typedCopyLayoutPtr loweringPosts
  loweringStateRelDefs context venomState vyperState words
  exprSimProps exprSimHash exprSimMemDefs exprSimWordArgs
  bodyPtrSignedConvertSourceFrame bodyFullTargetAttribute bodyFullUnwrapRun
  exprLowering compileEnv vyperAST valueEncodingProps ptrDiscipline
  bodyPtrDefs gasOutcomeFullCompose freshWrites exprLoweringProps
  gasContext vyperStorageFootprint exprSimDefs exprOperandVar exprSimSubscriptArraySuffix
  venomInst exprSimIfExpWidenedOwnedProvenance

(* The owned window tracks the live footprint, not the declared capacity.
   Selecting an element preserves that same allocation witness. *)
Theorem dynamic_value_child_own[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  j < LENGTH vs /\
  vv_own ce cx (ArrayT et (Dynamic cap)) sa sm fin
    (Value (ArrayV (DynArrayV vs))) (LocatedValue bt (mk_ptr bop LocMemory)) u /\
  eval_operand bop u = SOME a /\
  eval_operand dst q = SOME w /\
  w2n w = w2n a + 32 + j * type_memory_size tv /\
  sm.cs_next_id <= sb.cs_next_id /\
  array_length_frame sn u G tn q H tm /\
  (!x id sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sn x) ==>
  vv_own ce cx et sa sb fin (Value (EL j vs)) (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  strip_tac >>
  `q.vs_allocas = u.vs_allocas` by
    (qpat_assum `array_length_frame _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [array_length_frame_def]) >>
     disch_then (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_allocas`) >> simp[]) >>
  `!id lb lsz. local_region ce fin.scopes q id lb lsz ==>
               local_region ce fin.scopes u id lb lsz` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at sn p` by metis_tac[] >>
     qexistsl [`entry`,`p`,`w'`] >> fs[array_length_frame_def] >> metis_tac[]) >>
  drule_all_then assume_tac typedCopyLayoutPtrTheory.dynarray_live_child_footprint >>
  qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_own_def, contextTheory.mk_ptr_def, read_result_def, return_def] >>
  `val_footprint (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) <> 0` by
    (mp_tac (Q.SPECL [`tv`,`cap`,`vs`] typedCopyLayoutPtrTheory.dynarray_length_footprint_contained) >> decide_tac) >>
  simp[] >> strip_tac >> disj1_tac >> qexistsl [`aid`,`b`,`sz`] >>
  simp[] >> rpt conj_tac >> metis_tac[]
QED

(* Success fields shared by an owned Value and an extended place, once
   the source read has been related to the selected bytes. *)
Theorem dynamic_selected_memory_fields[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ read_result cx r fin = (INL v,fin) /\
  eval_operand dst q = SOME w /\ op_taint tm dst = {} /\
  op_prov H dst = SOME (b,sz) /\ b <= w2n w /\
  w2n w + type_memory_size tv <= b + sz /\
  w2n w + type_memory_size tv <= q.vs_alloca_next /\
  type_memory_bytes ce et = type_memory_size tv /\
  (!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
       val_in_memory tv v (w2n w) m) ==>
  vv_holds ce cx et r (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  ptr_vv_ok cx et r (LocatedValue et (mk_ptr dst LocMemory)) fin H tm q /\
  vv_store_bound cx et et fin r (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_buf_ok ce (Subscript et obj idx) dst H q
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_store_size tv v <= type_memory_size tv` by simp[val_store_size_le] >>
  `val_in_memory tv v (w2n w) q.vs_memory` by simp[mem_agree_outside_def] >>
  conj_tac
  >- (simp[vv_holds_def, mk_ptr_def] >> metis_tac[val_in_memory_word_type]) >>
  Cases_on `dst` >> gvs[op_prov_def] >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, mk_ptr_def,
       vv_store_bound_def, lowered_value_type_def, expr_type_def]
QED

(* The tail does not write the original variables, memory, or frame.
   Its input frame is already composed, also for a copied base. *)
Theorem dynamic_select_frame[local]:
  array_length_frame sn u G tn q H tm /\
  sa.cs_next_var <= sn.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel hor ctx fn ce cx fin u /\ wb_frame ce es fin sa s0 u /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  ghost_inv_at D lo d ce cx fin G tn u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  stmt_state_rel hor ctx fn ce cx fin q /\ wb_frame ce es fin sa s0 q /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 q) /\
  ghost_inv_at D lo d ce cx fin H tm q /\
  ghost_kept_at lo ce es sa G0 tn0 s0 H tm
Proof
  strip_tac >> fs[array_length_frame_def] >>
  `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  `q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas` by
    (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`u`,`sn`] >>
      simp[] >> metis_tac[local_ptrs_reserved_next_var]) >>
  conj_tac
  >- (irule wb_frame_readonly_tail >> qexistsl [`sn`,`u`] >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[pure_frame_mem_tail] >>
  conj_tac
  >- (irule ghost_inv_at_fresh_write >> qexistsl [`G`,`u`,`sa`,`tn`] >>
      qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => once_rewrite_tac [th]) >> simp[op_taint_def] >>
      rpt strip_tac >> metis_tac[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >>
  simp[op_taint_def] >> metis_tac[]
QED

(* The dynamic Value and MemoryPlace selections have the same post shape. *)
Definition subscript_dynamic_select_post_def:
  subscript_dynamic_select_post DF lo d ctx fn ce cx et obj idx es sa sb s0 G0 tn0 dst
      hor res ee Gz tnz z <=>
    ?r. res = INL r /\
       vv_post hor ctx fn ce cx (Subscript et obj idx) es sa sb s0 ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       vv_store_bound cx (post_value_type ce (Subscript et obj idx))
         (lowered_value_type ce (Subscript et obj idx)) ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF hor) lo d ce cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type ce (Subscript et obj idx))
         r (LocatedValue et (mk_ptr dst LocMemory)) ee Gz tnz z /\
       (!v. r = Value v /\ ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) ==>
          vv_own ce cx (post_value_type ce (Subscript et obj idx)) sa sb ee
            r (LocatedValue et (mk_ptr dst LocMemory)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocCode ==>
        ?v. read_result cx r ee = (INL v,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocMemory))) z = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocMemory) = StackValue t' op /\
          ~is_word_type (post_value_type ce (Subscript et obj idx)) ==>
          ptr_buf_ok ce (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok ce (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gz tnz
End

(* The captured Value may have come from a snapshot before the index. *)
Theorem subscript_dynamic_value_select_observed:
  captured_dynamic_scalar_rule tail_obs /\
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv)
    (is_signed_type (expr_type idx)) (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (b,sz) /\ op_prov G iop = NONE /\ b <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= b + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + (32 + cap * type_memory_size tv) <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size tv /\
  vv_own ce cx (ArrayT et (Dynamic cap)) sa sm fin
    (Value (ArrayV (DynArrayV vs))) (LocatedValue bt (mk_ptr bop LocMemory)) u /\
  sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  wb_frame ce es fin sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d ce cx fin G tn u) ==>
  ?res r q H tm.
    r = (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))
         then OK q else Abort Revert_abort q) /\
    captured_dynamic_itinerary tail_obs fn bop iop dst (type_memory_size tv)
      (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs)) sn sb (u,G,tn) (q,H,tm) /\
    (!tail. select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
      (ValueSubscript (IntV i)) (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!hor. valid_horizon cx st0 hor fin.storage_trace ==>
      gas_origin_ptr_path (DF hor,lo,explicit,ctx,fn,PG) (u,G,tn) [] (r,H,tm) /\
      ((?z. r = OK z /\
           subscript_dynamic_select_post DF lo d ctx fn ce cx et obj idx es sa sb s0 G0 tn0 dst
             hor res (fin with gas_obs := []) H tm z) \/
       (exit_result r /\ expr_exit res r /\ halt_exit hor cx (fin with gas_obs := []) res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))))
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  `w2n a + 32 <= u.vs_alloca_next` by decide_tac >>
  drule_all subscript_captured_dynamic_execution_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `!s. select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
           (ValueSubscript (IntV i)) s =
       if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs)) then
         (INL (Value (EL (Num i) vs)),s)
       else (INR (Error (RuntimeError "evaluate_subscripts array_index")),s)` by
    (drule_then assume_tac (Q.INST [`ty` |-> `ArrayT et (Dynamic cap)`] select_value_result) >>
     Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))` >>
     gvs[bind_def, return_def, lift_sum_def, raise_def]) >>
  qexistsl [`FST (select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
      (ValueSubscript (IntV i)) fin)`,
    `if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))
     then OK q else Abort Revert_abort q`,`q`,`H`,`tm`] >>
  simp[] >>
  conj_tac
  >- (gen_tac >>
      Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))` >> simp[]) >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))`)
  >- gvs[fragExecTheory.exit_result_def, expr_exit_def, halt_exit_def] >>
  fs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `array_length_frame _ u _ _ q _ _`
       (strip_assume_tac o SRULE [] o
        Q.AP_TERM `\st. (st.vs_allocas,st.vs_initial_fmp,st.vs_fmp)` o
        cj 1 o REWRITE_RULE[array_length_frame_def]) >>
     strip_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` drule >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `read_result cx (Value (EL (Num i) vs)) fin = (INL (EL (Num i) vs),fin)` by
    simp[read_result_def, return_def] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `LENGTH vs <= cap` by gs[vyperTypingTheory.value_has_type_def] >>
  `SUC (Num i) * type_memory_size tv <= cap * type_memory_size tv` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `w2n a + 32 + Num i * type_memory_size tv + type_memory_size tv <= u.vs_alloca_next` by
    (qpat_assum `SUC (Num i) * _ <= _` mp_tac >>
     rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `q.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `array_length_frame _ _ _ _ _ _ _`
       (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_alloca_next` o CONJUNCT1 o
        REWRITE_RULE [array_length_frame_def]) >> simp[]) >>
  `(!x id sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sn x)` by
    metis_tac[environment_var_not_fresh, local_ptrs_reserved_next_var] >>
  `w2n (a + 32w + iw * n2w (type_memory_size tv)) =
     w2n a + 32 + Num i * type_memory_size tv` by decide_tac >>
  drule_all_then assume_tac dynamic_value_child_own >>
  `b <= w2n (a + 32w + iw * n2w (type_memory_size tv)) /\
   w2n (a + 32w + iw * n2w (type_memory_size tv)) + type_memory_size tv <= b + sz /\
   w2n (a + 32w + iw * n2w (type_memory_size tv)) + type_memory_size tv <= q.vs_alloca_next`
    by (rpt conj_tac >> decide_tac) >>
  `!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
    val_in_memory tv (EL (Num i) vs) (w2n (a + 32w + iw * n2w (type_memory_size tv))) m`
    by simp[] >>
  drule_all_then strip_assume_tac dynamic_selected_memory_fields >>
  `vv_at ce cx et sa sb fin (Value (EL (Num i) vs))
     (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (irule exprSimIfExpWidenedOwnedProvenanceTheory.vv_own_memory_transport >>
     qexistsl [`tv`, `tv`, `et`, `et`, `EL (Num i) vs`] >>
     simp[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  simp[subscript_dynamic_select_post_def, fragExecTheory.exit_result_def,
       lowered_value_type_def, expr_type_def, vv_location_def, mk_ptr_def] >>
  qx_gen_tac `hor` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `hor` (strip_assume_tac o UNDISCH)) >>
  drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) [] dynamic_select_frame) >>
  `vv_post hor ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
     (Value (EL (Num i) vs)) (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (irule vv_post_frame_intro >> gvs[expr_type_def, vv_place_ptr_def, mk_ptr_def]) >>
  gvs[lowered_value_type_def, expr_type_def, mk_ptr_def]
QED

(* Use the actual in-range read of the extended place. Its history key
   need not be the key from which the parent array was read. *)
Theorem subscript_dynamic_memory_select_observed:
  captured_dynamic_scalar_rule tail_obs /\
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv)
    (is_signed_type (expr_type idx)) (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  lookup_scopes id fin.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (b,sz) /\ op_prov G iop = NONE /\ b <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= b + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + (32 + cap * type_memory_size tv) <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size tv /\
  (0 <= i /\ Num i < LENGTH vs ==>
    ?v root ssz base rt k.
      read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
        (INL v,fin) /\ value_has_type tv v /\
      (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n a + 32 + Num i * type_memory_size tv) m) /\
      FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
      lookup_var root u = SOME base /\
      ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
      mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,tv) /\
      w2n a + 32 + Num i * type_memory_size tv = w2n base + k /\
      k + type_memory_size tv <= ssz) /\
  sa.cs_next_var <= sn.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  wb_frame ce es fin sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d ce cx fin G tn u) ==>
  ?res r q H tm.
    r = (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))
         then OK q else Abort Revert_abort q) /\
    captured_dynamic_itinerary tail_obs fn bop iop dst (type_memory_size tv)
      (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs)) sn sb (u,G,tn) (q,H,tm) /\
    (!tail. select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!hor. valid_horizon cx st0 hor fin.storage_trace ==>
      gas_origin_ptr_path (DF hor,lo,explicit,ctx,fn,PG) (u,G,tn) [] (r,H,tm) /\
      ((?z. r = OK z /\
           subscript_dynamic_select_post DF lo d ctx fn ce cx et obj idx es sa sb s0 G0 tn0 dst
             hor res (fin with gas_obs := []) H tm z) \/
       (exit_result r /\ expr_exit res r /\ halt_exit hor cx (fin with gas_obs := []) res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))))
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  `w2n a + 32 <= u.vs_alloca_next` by decide_tac >>
  drule_all subscript_captured_dynamic_execution_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qabbrev_tac `child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))` >>
  `!gs. select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id path))
         (ValueSubscript (IntV i)) (fin with gas_obs := gs) =
       (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs)) then
          INL child else INR (Error (RuntimeError "evaluate_subscripts array_index")),
        fin with gas_obs := gs)` by
    (gen_tac >>
     `lookup_scopes id (fin with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule_all_then assume_tac (Q.INST [`ty` |-> `ArrayT et (Dynamic cap)`,
                                       `sb` |-> `ValueSubscript (IntV i)`] select_memory_result) >>
     Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))` >>
     gvs[Abbr `child`, bind_def, return_def, lift_sum_def, raise_def]) >>
  qexistsl [`if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))
     then INL child else INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
    `if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))
     then OK q else Abort Revert_abort q`,`q`,`H`,`tm`] >>
  simp[] >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))`)
  >- gvs[fragExecTheory.exit_result_def, expr_exit_def, halt_exit_def] >>
  fs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `array_length_frame _ u _ _ q _ _`
       (strip_assume_tac o SRULE [] o
        Q.AP_TERM `\st. (st.vs_allocas,st.vs_initial_fmp,st.vs_fmp)` o
        cj 1 o REWRITE_RULE[array_length_frame_def]) >>
     strip_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` drule >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  rename1 `lookup_var row_var u = SOME (row_word:256 word)` >>
  `q.vs_alloca_next = u.vs_alloca_next /\ q.vs_memory = u.vs_memory /\ tm.t_mem = tn.t_mem` by
    (fs[array_length_frame_def] >>
     qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `LENGTH vs <= cap` by gs[vyperTypingTheory.value_has_type_def] >>
  `SUC (Num i) * type_memory_size tv <= cap * type_memory_size tv` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `w2n a + 32 + Num i * type_memory_size tv + type_memory_size tv <= u.vs_alloca_next` by
    (qpat_assum `SUC (Num i) * _ <= _` mp_tac >>
     rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  qabbrev_tac `w = a + 32w + iw * n2w (type_memory_size tv)` >>
  `b <= w2n w /\ w2n w + type_memory_size tv <= b + sz /\
   w2n w + type_memory_size tv <= q.vs_alloca_next` by (rpt conj_tac >> decide_tac) >>
  `!m. mem_agree_outside tm.t_mem q.vs_memory m ==> val_in_memory tv v (w2n w) m` by
    (qpat_assum `q.vs_memory = _` SUBST1_TAC >>
     qpat_assum `tm.t_mem = _` SUBST1_TAC >>
     qpat_assum `w2n w = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all_then (qspecl_then [`obj`,`idx`] strip_assume_tac) dynamic_selected_memory_fields >>
  `lookup_var row_var q = SOME row_word` by
    (`not_fresh_at sn row_var` by metis_tac[environment_var_not_fresh, local_ptrs_reserved_next_var] >>
     fs[array_length_frame_def]) >>
  `w2n w = w2n row_word + k` by decide_tac >>
  `vv_at ce cx et sa sb fin child (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (`val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
     drule_then assume_tac val_footprint_le >>
     simp[vv_at_def, mk_ptr_def] >>
     disj2_tac >> disj1_tac >> qexistsl [`id`,`w2n row_word`,`ssz`] >>
     simp[Abbr `child`, local_region_def, local_val_at_def, local_place_at_def,
          local_path_at_def] >>
     rpt conj_tac >> metis_tac[]) >>
  `w = row_word + n2w k` by
    (qpat_assum `w2n w = w2n row_word + k` (mp_tac o Q.AP_TERM `n2w : num -> 256 word`) >>
     rewrite_tac[GSYM word_add_n2w, n2w_w2n]) >>
  `vv_place_ptr ce cx fin q child (LocatedValue et (mk_ptr dst LocMemory))` by
    (simp[Abbr `child`, vv_place_ptr_def, mk_ptr_def] >> metis_tac[]) >>
  simp[subscript_dynamic_select_post_def, Abbr `child`, fragExecTheory.exit_result_def,
       lowered_value_type_def, expr_type_def, vv_location_def, mk_ptr_def] >>
  qx_gen_tac `hor` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `hor` (strip_assume_tac o UNDISCH)) >>
  drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) [] dynamic_select_frame) >>
  conj_tac
  >- (irule vv_post_frame_intro >> gvs[expr_type_def, mk_ptr_def]) >>
  gvs[lowered_value_type_def, expr_type_def, mk_ptr_def]
QED

(* Forget the itinerary for clients of the ordinary full simulation. *)
Theorem subscript_dynamic_value_select_full:
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv)
    (is_signed_type (expr_type idx)) (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (b,sz) /\ op_prov G iop = NONE /\ b <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= b + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + (32 + cap * type_memory_size tv) <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size tv /\
  vv_own ce cx (ArrayT et (Dynamic cap)) sa sm fin
    (Value (ArrayV (DynArrayV vs))) (LocatedValue bt (mk_ptr bop LocMemory)) u /\
  sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  wb_frame ce es fin sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d ce cx fin G tn u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et (Dynamic cap)) (Value (ArrayV (DynArrayV vs)))
      (ValueSubscript (IntV i))) (fin,u,G,tn)
    (\H res ee Gz tnz z. ?r. res = INL r /\
       vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       vv_store_bound cx (post_value_type ce (Subscript et obj idx))
         (lowered_value_type ce (Subscript et obj idx)) ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type ce (Subscript et obj idx))
         r (LocatedValue et (mk_ptr dst LocMemory)) ee Gz tnz z /\
       (!v. r = Value v /\ ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) ==>
          vv_own ce cx (post_value_type ce (Subscript et obj idx)) sa sb ee
            r (LocatedValue et (mk_ptr dst LocMemory)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocCode ==>
        ?v. read_result cx r ee = (INL v,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocMemory))) z = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocMemory) = StackValue t' op /\
          ~is_word_type (post_value_type ce (Subscript et obj idx)) ==>
          ptr_buf_ok ce (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok ce (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gz tnz)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  assume_tac captured_dynamic_scalar_rule_trivial >>
  drule_all subscript_dynamic_value_select_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `r = if _ then _ else _` kall_tac >>
  irule gas_outcome_full_intro >>
  qexistsl [`H`,`fin`,`[]`,`r`,`res`,`tm`] >>
  simp[gasSummaryTheory.gas_explicit_def] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!hor. valid_horizon _ _ hor _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    drule >> simp[subscript_dynamic_select_post_def]
QED

Theorem subscript_dynamic_memory_select_full:
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv)
    (is_signed_type (expr_type idx)) (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  lookup_scopes id fin.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (b,sz) /\ op_prov G iop = NONE /\ b <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= b + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + (32 + cap * type_memory_size tv) <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size tv /\
  (0 <= i /\ Num i < LENGTH vs ==>
    ?v root ssz base rt k.
      read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
        (INL v,fin) /\ value_has_type tv v /\
      (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n a + 32 + Num i * type_memory_size tv) m) /\
      FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
      lookup_var root u = SOME base /\
      ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
      mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,tv) /\
      w2n a + 32 + Num i * type_memory_size tv = w2n base + k /\
      k + type_memory_size tv <= ssz) /\
  sa.cs_next_var <= sn.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  wb_frame ce es fin sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d ce cx fin G tn u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i))) (fin,u,G,tn)
    (\H res ee Gz tnz z. ?r. res = INL r /\
       vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       vv_store_bound cx (post_value_type ce (Subscript et obj idx))
         (lowered_value_type ce (Subscript et obj idx)) ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type ce (Subscript et obj idx))
         r (LocatedValue et (mk_ptr dst LocMemory)) ee Gz tnz z /\
       (!v. r = Value v /\ ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) ==>
          vv_own ce cx (post_value_type ce (Subscript et obj idx)) sa sb ee
            r (LocatedValue et (mk_ptr dst LocMemory)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocCode ==>
        ?v. read_result cx r ee = (INL v,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocMemory))) z = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocMemory) = StackValue t' op /\
          ~is_word_type (post_value_type ce (Subscript et obj idx)) ==>
          ptr_buf_ok ce (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok ce (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gz tnz)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  assume_tac captured_dynamic_scalar_rule_trivial >>
  drule_all subscript_dynamic_memory_select_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `r = if _ then _ else _` kall_tac >>
  irule gas_outcome_full_intro >>
  qexistsl [`H`,`fin`,`[]`,`r`,`res`,`tm`] >>
  simp[gasSummaryTheory.gas_explicit_def] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!hor. valid_horizon _ _ hor _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    drule >> simp[subscript_dynamic_select_post_def]
QED
