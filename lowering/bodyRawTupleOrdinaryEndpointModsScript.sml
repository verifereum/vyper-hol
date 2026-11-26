(* Ordinary result of the positive, non-reverting raw-call suffix. *)
Theory bodyRawTupleOrdinaryEndpointMods
Ancestors
  exprSimRawCall exprSimRawCallCalldata exprSimHash exprSimMemDefs
  exprSimProps valueEncoding valueTypingMemoryProps loweringPosts
  stateRelProj context vyperState venomMemDefs vfmConstants
  exprLowering exprLoweringProps fragExec fragExecMem instIdxIndep
  words list emitHelper venomInst
Libs
  monadsyntax

Theorem raw_tuple_ordinary_live_row[local]:
  storage_well_formed_on cx es (FST H) /\ expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
  eval_operand result t = SOME w /\
  FLOOKUP t.vs_allocas ti = SOME (w2n w,64 + ((n+31) DIV 32)*32) /\
  sf.cs_next_id <= ti /\ ti < sb.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
    w2n w + (64 + ((n+31) DIV 32)*32) <= lb \/ lb + lsz <= w2n w) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n bytes)]) /\
  val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    v (w2n w) t.vs_memory /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    es (Value v) vv t /\
  vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv t
Proof
  strip_tac >>
  `type_memory_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) =
     64 + ((n+31) DIV 32)*32` by
    (simp[type_memory_size_def, word_size_def] >> decide_tac) >>
  `w2n w + (64 + ((n+31) DIV 32)*32) <= t.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >>
     simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  conj_asm1_tac
  >- (simp[] >> metis_tac[raw_call_tuple_post]) >>
  conj_tac
  >- (qpat_assum `vv = _` SUBST1_TAC >>
      qpat_assum `post_value_type cenv e = _` SUBST1_TAC >>
      qpat_assum `lowered_value_type cenv e = _` SUBST1_TAC >>
      irule vv_store_bound_capacity >> simp[mk_ptr_def] >>
      qexistsl_tac [`H`,`cenv`,`ctx`,`es0`,`func`,`s0`,`sf`,`sb`] >> gvs[mk_ptr_def]) >>
  `val_wf (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) v` by
    (simp[valueEncodingDefsTheory.val_wf_def, type_memory_size_def, listTheory.LENGTH_TAKE_EQ] >>
     qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def] >> decide_tac) >>
  drule val_footprint_le >> strip_tac >>
  gvs[vv_own_def, mk_ptr_def, read_result_def, return_def] >>
  disj1_tac >> qexistsl_tac [`ti`,`w2n w`,`64 + ((n+31) DIV 32)*32`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* Select the physical endpoint before quantifying over horizons. *)
Theorem raw_tuple_ordinary_endpoint:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel H0 ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      !H. stmt_state_rel H ctx func cenv cx es s /\
          storage_well_formed_on cx es (FST H) ==>
          let u = t with vs_inst_idx := LENGTH sb.cs_current_insts in
            vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv u /\
            vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
              es (Value v) vv u /\
            vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv u
Proof
  strip_tac >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_nonrevert_positive_run) >>
  disch_then drule_all >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms, Excl "vv_post_inst_idx"] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_nonrevert_positive_run) >>
  disch_then drule_all >> strip_tac >>
  rename1 `stmt_state_rel H ctx func cenv cx es t'` >>
  `t' = t` by
    (qpat_x_assum `run_inst_seq _ s = OK t'` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u` by
    simp[Abbr `u`, stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx] >>
  `!name lb lsz. local_region cenv es.scopes u name lb lsz <=>
                 local_region cenv es.scopes t name lb lsz` by
    simp[Abbr `u`, loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def] >>
  irule raw_tuple_ordinary_live_row >> simp[] >>
  qexistsl_tac [`s.vs_returndata`,`result`,`ti`,`tw`] >>
  gvs[Abbr `u`, hash_eval_operand_inst_idx] >> first_assum ACCEPT_TAC
QED
