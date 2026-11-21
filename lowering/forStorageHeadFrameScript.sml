Theory forStorageHeadFrame
Ancestors
  bodyFullGhostFrame bodyPtrSignedConvertSourceFrame exprSimPtrLiteralBuffer
  assignTuplePtrCopyLen bodyMemoryDefs bodyPtrDefs stmtSimProps stmtSimDefs
  exprLoweringProps allocaHistory ptrDiscipline loweringPosts
  compileEnv emitHelper venomState venomExecSemantics venomInst vyperAST
  words finite_map list pred_set

(* The scalar prefix can give its element address provenance; only registers
   outside the prefix's outputs participate in the preserved frame. *)
Theorem for_storage_array_head_prefix_transport_outside:
  !H D lo d ctx func cx c0 e0 sa0 s0 G0 tn0 ei s G tn u Gu tnu bd dv ov tot ep
      slot k n sa bod bb idx p dst nb lvo len.
    let Fr = (\c ee s G tn.
      alloca_history func s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      s0.vs_alloca_next <= s.vs_alloca_next /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
             lookup_var x s = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c0 e0 sa0 s0 c ee s /\
      !aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) in
    let dyn = (case bd of Fixed _ => F | Dynamic _ => T) in
    let outs = if dyn then [dv;ov;tot;ep] else [dv;ov;ep] in
    let addr = (if dyn then slot + 1w else slot) + n2w (k*n) in
    u = (update_var ep addr
           (if dyn then update_var tot (1w + n2w (k*n))
              (update_var ov (n2w (k*n)) (jump_to bod (update_var dv 0w s)))
            else update_var ov (n2w (k*n)) (jump_to bod (update_var dv 0w s))))
           with vs_inst_idx := LENGTH sa.cs_current_insts /\
    (!x. ~MEM x outs ==> FLOOKUP Gu x = FLOOKUP G x) /\
    tnu = (tn with t_var := FOLDL (\m x. fmupdate x {} m) tn.t_var outs) /\
    lookup_block bod func.fn_blocks = SOME bb /\
    (!j. j < LENGTH sa.cs_current_insts ==>
         ?inst. get_instruction bb j = SOME inst /\ inst.inst_opcode <> ALLOCA) /\
    ALL_DISTINCT outs /\
    (!x. MEM x outs ==> ~not_fresh_at sa0 x) /\
    ~MEM idx outs /\ ~MEM p outs /\
    (!x. lvo = Var x ==> ~MEM x outs) /\
    sa.cs_current_bb = bod /\ ~s.vs_halted /\
    local_ptrs_reserved c0 sa0 /\
    (!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    stmt_state_rel H ctx func c0 cx ei s /\
    storage_well_formed_on cx ei (FST H) /\
    ghost_inv_at D lo d c0 cx ei G tn s /\
    Fr c0 ei s G tn /\ return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
    lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
    op_taint tn (Var idx) = {} /\ lookup_var p s = SOME dst /\
    ptr_covers G tn p s nb /\ eval_operand lvo s = SOME (n2w len) /\
    op_prov G lvo = NONE /\ op_taint tn lvo = {} ==>
    stmt_state_rel H ctx func c0 cx ei u /\
    storage_well_formed_on cx ei (FST H) /\
    ghost_inv_at D lo d c0 cx ei Gu tnu u /\
    Fr c0 ei u Gu tnu /\ return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u /\
    u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    lookup_var idx u = SOME (n2w k) /\ FLOOKUP Gu idx = NONE /\
    op_taint tnu (Var idx) = {} /\ eval_operand lvo u = SOME (n2w len) /\
    op_prov Gu lvo = NONE /\ op_taint tnu lvo = {} /\
    lookup_var p u = SOME dst /\ ptr_covers Gu tnu p u nb /\
    eval_operand (Var ep) u = SOME addr /\ op_taint tnu (Var ep) = {} /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_immutables = s.vs_immutables /\
    tnu.t_mem = tn.t_mem /\
    (!name b sz. local_region c0 ei.scopes u name b sz <=>
                 local_region c0 ei.scopes s name b sz) /\
    !x. ~MEM x outs ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
        op_taint tnu (Var x) = op_taint tn (Var x)
Proof
  rpt gen_tac >>
  SIMP_TAC pureSimps.pure_ss
    [combinTheory.LET_FORALL_ELIM, combinTheory.S_ABS_R,
     combinTheory.o_ABS_R, combinTheory.o_THM, combinTheory.C_THM] >>
  ntac 4 (gen_tac >> disch_tac) >> strip_tac >>
  `u.vs_current_bb = sa.cs_current_bb /\
   u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_memory = s.vs_memory /\ u.vs_immutables = s.vs_immutables /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp /\
   tnu.t_mem = tn.t_mem /\ tnu.t_stor = tn.t_stor /\
   tnu.t_trans = tn.t_trans /\ tnu.t_imm = tn.t_imm /\
   u = jump_to bod s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
   eval_operand (Var ep) u = SOME addr /\ op_taint tnu (Var ep) = {} /\
   (!x. ~MEM x outs ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
     op_taint tnu (Var x) = op_taint tn (Var x))` by suspend "endpoint" >>
  qpat_x_assum `u = (update_var _ _ _) with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `tnu = tn with t_var := _` kall_tac >>
  `!x. not_fresh_at sa0 x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
     op_taint tnu (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >> `~MEM x outs` by metis_tac[] >> simp[]) >>
  `!name b sz. local_region c0 ei.scopes u name b sz <=>
                local_region c0 ei.scopes s name b sz` by
    (irule literal_ptr_local_region_frame >> qexists_tac `sa0` >> simp[]) >>
  `stmt_state_rel H ctx func c0 cx ei u` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl [`jump_to bod s`,`sa0`] >> simp[stmt_state_rel_jump_to] >>
     simp[jump_to_def, lookup_var_def, GSYM lookup_var_def]) >>
  `ghost_inv_at D lo d c0 cx ei Gu tnu u` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl [`G`,`ei`,`s`,`sa0`,`tn`] >> simp[]) >>
  `Fr c0 ei u Gu tnu` by suspend "frame" >>
  suspend "post"
QED

Resume for_storage_array_head_prefix_transport_outside[endpoint]:
  fs[Abbr `outs`] >> Cases_on `dyn` >>
  gvs[update_var_def, jump_to_def, eval_operand_def, lookup_var_def,
      op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume for_storage_array_head_prefix_transport_outside[frame]:
  qpat_x_assum `Fr c0 ei s G tn` mp_tac >> simp[Abbr `Fr`] >> strip_tac >>
  `alloca_history func u` by
    (qpat_x_assum `alloca_history func s` mp_tac >>
     simp[alloca_history_def] >> disch_tac >>
     qx_gen_tac `j` >> qx_gen_tac `inst` >> strip_tac >>
     qpat_assum `!i. i < LENGTH sa.cs_current_insts ==>
         ?a. get_instruction bb i = SOME a /\ a.inst_opcode <> ALLOCA`
       (qspec_then `j` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (qx_choose_then `other` strip_assume_tac) >>
     `other = inst` by
       (qpat_x_assum `get_instruction bb j = SOME other` mp_tac >> simp[]) >>
     gvs[]) >>
  `alloca_frame c0 e0 sa0 s0 c0 ei u` by
    (qpat_x_assum `alloca_frame c0 e0 sa0 s0 c0 ei s` mp_tac >>
     simp[alloca_frame_def]) >>
  simp[allocas_below_fmp_def] >> metis_tac[allocas_below_fmp_def]
QED

Resume for_storage_array_head_prefix_transport_outside[post]:
  `return_buf_frame d c0 sa0 u` by
    (irule return_buf_frame_frame >> qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
  `ret_pc_ok c0 sa0 u` by
    (irule ret_pc_ok_frame >> qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
  `ptr_covers Gu tnu p u nb` by
    (irule ptr_covers_lookup_frame >> qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  `allocas_from lo u` by
    (qpat_x_assum `ghost_inv_at D lo d c0 cx ei Gu tnu u` mp_tac >> simp[ghost_inv_at_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >> simp[Abbr `Fr`]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `u = jump_to bod s with <|vs_vars := _; vs_inst_idx := _|>`
       SUBST1_TAC >> simp[jump_to_def]) >>
  simp[] >> Cases_on `lvo` >> gvs[eval_operand_def, op_prov_def, op_taint_def]
QED

Finalise for_storage_array_head_prefix_transport_outside
