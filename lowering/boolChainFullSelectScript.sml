(* Joint forced-read composition across a single selected Boolean edge. *)
Theory boolChainFullSelect
Ancestors
  boolChainSource boolChainFullControl gasOutcomeFullCompose gasOutcomeFullGuarded
  gasOutcomeFull exprSimDefs loweringPosts bodyPtrDefs vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState

(* P is the head post supplied by the caller, including any retained frames.
   Only its control-relevant fields are needed to run the emitted JNZ. *)
Theorem bool_word_forced_select_full:
  expr_body_pre cenv cx env (IfExp (BaseT BoolT) c a f) es /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx c) (read_result cx)) (es,s,G,tn) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!H res mid G1 tn1 u. P H res mid G1 tn1 u ==> ?b.
     res = INL (BoolV b) /\
     expr_post H ctx func cenv cx c es sa sc s mid (BoolV b) op u /\
     eval_operand op u = SOME (if b then 1w else 0w) /\ op_taint tn1 op = {} /\
     u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
     ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u) /\
  emit_inst JNZ [op; Label lt; Label lf] [] sc = ((),sn) /\ fn_has_code sc sn func /\
  (!b. (entry b).cs_current_bb = (if b then lt else lf) /\
       (entry b).cs_current_insts = [] /\ sa.cs_next_var <= (entry b).cs_next_var) /\
  return_buf_frame d cenv sa s /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!marks b mid G1 tn1 u z.
     bind (eval_expr cx c) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV b),mid) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> P H (INL (BoolV b)) mid G1 tn1 u) /\
     z = jump_to (if b then lt else lf) u /\
     return_buf_frame d cenv (entry b) z /\ alloca_history func z /\
     s.vs_alloca_next <= z.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
     (!fn inst w. frag_reachable ctx func z fn inst w ==> dalloca_fmp_headroom inst w) /\
     ~z.vs_halted /\ z.vs_current_bb = (entry b).cs_current_bb /\
     z.vs_inst_idx = LENGTH (entry b).cs_current_insts /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid z /\ storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 z) ==>
     gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
       (bind (eval_expr cx (if b then a else f)) (read_result cx)) (mid,z,G1,tn1) Q
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !w. r = Halt w ==> allocas_below_fmp w))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx (IfExp (BaseT BoolT) c a f)) (read_result cx)) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> irule gas_outcome_full_source_cong >>
  drule bool_chain_forced_select >> strip_tac >> goal_assum (drule_at Any) >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >- (gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >>
      simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_raise]) >>
  qexists_tac `\H res mid G1 tn1 u. P H res mid G1 tn1 u /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`u`] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `h = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 h mid.storage_trace` by fs[Abbr `h`, storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> P H res mid G1 tn1 u /\ _` (qspec_then `h` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H res mid G1 tn1 u. P H res mid G1 tn1 u ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV b),mid)` by
    (`mid with gas_obs := [] = mid` by
       (Cases_on `mid` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >>
     pop_assum (fn upd =>
       qpat_assum `!tail. _ (es with gas_obs := _ ++ tail) = (_,mid with gas_obs := tail)`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,upd])))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK u,G1,tn1) /\
     expr_post H ctx func cenv cx c es sa sc s mid (BoolV b) op u /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> P H _ mid G1 tn1 u` (drule_then assume_tac) >>
     qpat_assum `!H res mid G1 tn1 u. P H res mid G1 tn1 u ==> _`
       (drule_then strip_assume_tac) >> fs[]) >>
  qpat_assum `!b. (entry b).cs_current_bb = _ /\ _` (qspec_then `b` strip_assume_tac) >>
  drule_all bool_word_selected_entry_full >> strip_tac >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
     (bind (eval_expr cx (if b then a else f)) (read_result cx)) (mid,u,G1,tn1) Q
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !w. r = Halt w ==> allocas_below_fmp w))` by
    (irule gas_outcome_full_zero_prefix_guarded >>
     simp[storage_trace_frame_bind, evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
     qexistsl_tac [`G1`,`z`,`tn1`] >> conj_tac
     >- (gen_tac >> strip_tac >>
         qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,G1,tn1) [] _ /\ _`
           (drule_then strip_assume_tac) >> simp[]) >>
     qpat_x_assum `z = jump_to _ _` SUBST_ALL_TAC >>
     qpat_assum `!marks b mid G1 tn1 u. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
     simp[] >> rpt conj_tac
     >- (first_assum ACCEPT_TAC)
     >~ [`?marks'. _ (es with gas_obs := gas_explicit marks' _) = _`]
     >- (qexists_tac `marks` >> simp[]) >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,G1,tn1) [] _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  Cases_on `b` >> fs[]
QED
