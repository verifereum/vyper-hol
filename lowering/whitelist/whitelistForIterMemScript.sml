(*
 * Whitelist removal: for loops over a memory-valued array iterable other
 * than a local name (form 2 of whitelistForIter's survey).
 *
 * compile_stmt's For Array case compiles the iterable with compile_expr
 * and then runs the fixed or dynamic memory loop over the pointer it
 * returns: a temporary buffer (a list literal, an extcall result, an IfExp
 * copy) or a place inside a local (a struct member or a subscript).  The
 * source iterates the snapshot it read at loop entry, so the compiled loop
 * agrees only while the body leaves the iterable's bytes alone.
 *
 * Neither S1 interface says that yet:
 *   - for a temporary, stmt_post keeps no memory outside the locals, so a
 *     body's stmt_frag doesn't keep the buffer;
 *   - for a place, vv_post doesn't tie the pointer to the source place
 *     (only to some offset of a local of the same type), so
 *     "the body doesn't write the place" (iterator_unmodified) doesn't
 *     reach the bytes the loop reads.
 * So the loop is proved against a hook, and each kind of iterable reduces
 * the hook to the interface clause it lacks today, taken as an explicit
 * hypothesis:
 *
 *   stmt_frag_keep Q    - a statement fragment that also keeps the state
 *                         predicate Q from start to end
 *   expr_vv_sim_with Qe - expr_vv_sim with an extra postcondition Qe
 *   keep_stable Q sb b z - Q survives code that keeps the variables handed
 *                         out before sb and the bytes [b, b+z)
 *
 * TOP-LEVEL:
 *   compile_for_mem_frag      - the For case over a memory iterable, given
 *                               the hook (a pointer inside an allocation
 *                               made before the loop, and a body that keeps
 *                               the elements there)
 *   typed_stmts_place_frame   - source side: a body that writes nothing
 *                               containing the iterable's place keeps every
 *                               read below its attribute path
 *   for_keep_temp             - hook for a temporary: from a body that keeps
 *                               the bytes of the buffer's allocation
 *   for_keep_place            - hook for a place: from the pointer being the
 *                               place's (local pointer + mem_path_offset)
 *                               and the source frame
 *)
Theory whitelistForIterMem
Ancestors
  whitelistForIterDynFrag stmtSimForArrayFrame exprSimSubscriptMap exprSimDefs loweringPosts
  stmtSimDefs gasOutcome gasSummary supportedStmts vyperTypeSystem vyperState
  vyperInterpreter valueEncoding valueEncodingProps valueEncodingProofs
  stmtLowering exprLowering venomState exprSimPopImmutableTarget
  compileEnv exprLoweringProps list finite_map arithmetic words

(* A statement fragment as stmt_frag says, that also keeps Q: started in a
   state where Q holds, it ends where Q holds.  stmt_frag_keep (K T) is
   stmt_frag. *)
Definition stmt_frag_keep_def:
  stmt_frag_keep Q ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      stmt_state_rel ctx func cenv cx es s0 /\ Q s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) source (es, s0)
        (\res ee t. stmt_post ctx func cx lctx cenv cenv' sa sb s0 res ee t /\
                    Q t)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

(* expr_vv_sim, whose post also has Qe of the compile states, the start
   state, and the source and Venom results.  expr_vv_sim_with (K ...) T is
   expr_vv_sim. *)
Definition expr_vv_sim_with_def:
  expr_vv_sim_with Qe ctx func cenv cx ty e es <=>
    !sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) (eval_expr cx e) (es, s0)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          Qe sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)
End

(* Q survives any code that keeps the variables handed out before sb and
   the bytes [b, b + z): the loop's own index, element copy and branches
   write only fresh variables and the loop variable's allocation. *)
Definition keep_stable_def:
  keep_stable Q (sb : compile_state) b z <=>
    !s s'. Q s /\
      (!x. not_fresh_at sb x ==> lookup_var x s' = lookup_var x s) /\
      mem_bytes_at b z s'.vs_memory = mem_bytes_at b z s.vs_memory ==>
      Q s'
End

(* Control changes and fresh register writes do not disturb the snapshot. *)
Theorem for_keep_jump[local]:
  keep_stable Q caller b z /\ Q s ==> Q (jump_to lbl s)
Proof
  simp[keep_stable_def] >> strip_tac >> first_x_assum irule >>
  qexists_tac `s` >> simp[jump_to_def, lookup_var_def]
QED

Theorem for_keep_update[local]:
  keep_stable Q caller b z /\ Q s /\ ~not_fresh_at caller x ==>
  Q (update_var x w s)
Proof
  simp[keep_stable_def] >> strip_tac >> first_x_assum irule >>
  qexists_tac `s` >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem for_keep_alloca[local]:
  inst.inst_outputs = [out] /\ exec_alloca inst s amount = OK t /\
  keep_stable Q caller b z /\ Q s /\ ~not_fresh_at caller out /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z)
Proof
  strip_tac >>
  gvs[venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs()] >>
  `inst.inst_id <> aid \/ FLOOKUP s.vs_allocas inst.inst_id <> NONE` by
    (Cases_on `inst.inst_id = aid` >> gvs[]) >>
  simp[update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `keep_stable _ _ _ _` mp_tac >>
  simp[keep_stable_def] >> strip_tac >> first_x_assum irule >>
  qexists_tac `s` >> simp[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Both layouts use the same EQ/JNZ condition; only rhs differs. *)
Theorem for_condition_keep[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j1 EQ [lhs; rhs] [dv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst j2 JNZ [Var dv; Label yes; Label no] []) /\
  ~s.vs_halted /\ eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME d /\
  keep_stable Q caller b z /\ Q s /\ ~not_fresh_at caller dv /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\
    FLOOKUP t.vs_allocas aid = SOME (b,z) /\
    t = jump_to (if a = d then yes else no)
          (update_var dv (bool_to_word (a = d)) s)
Proof
  strip_tac >> drule_all stmtSimForArrayLoopTheory.eq_branch_zero_path >> strip_tac >>
  qexists_tac `jump_to (if a = d then yes else no)
                 (update_var dv (bool_to_word (a = d)) s)` >>
  `Q (update_var dv (bool_to_word (a = d)) s)` by
    (drule_all for_keep_update >> simp[]) >>
  `Q (jump_to (if a = d then yes else no)
        (update_var dv (bool_to_word (a = d)) s))` by
    (drule_all for_keep_jump >> simp[]) >>
  simp[jump_to_def, update_var_def]
QED

Theorem for_increment_keep[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
     mk_inst i2 ASSIGN [Var nv] [idx]; mk_inst i3 JMP [Label cond] []] /\
  ~s.vs_halted /\ lookup_var idx s = SOME w /\
  keep_stable Q caller b z /\ Q s /\
  ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\
    FLOOKUP t.vs_allocas aid = SOME (b,z) /\
    t = jump_to cond (update_var idx (w + 1w) (update_var nv (w + 1w) s))
Proof
  strip_tac >>
  `run_inst_seq [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
                mk_inst i2 ASSIGN [Var nv] [idx]] s =
    OK (update_var idx (w + 1w) (update_var nv (w + 1w) s))` by
    simp[run_inst_seq_def,
         venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomExecSemanticsTheory.exec_pure2_def,
         venomInstTheory.mk_inst_def,
         eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  `Q (update_var nv (w + 1w) s)` by (drule_all for_keep_update >> simp[]) >>
  `Q (update_var idx (w + 1w) (update_var nv (w + 1w) s))` by
    (metis_tac[for_keep_update]) >>
  `Q (jump_to cond (update_var idx (w + 1w) (update_var nv (w + 1w) s)))` by
    (drule_all for_keep_jump >> simp[]) >>
  qexists_tac `jump_to cond (update_var idx (w + 1w) (update_var nv (w + 1w) s))` >>
  conj_tac
  >- (irule stmtSimForArrayLoopTheory.inst_seq_jump_zero_path >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`bb`, `[mk_inst i1 ADD [Var idx; Lit 1w] [nv];
                       mk_inst i2 ASSIGN [Var nv] [idx]]`, `i3`] >>
      simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  simp[jump_to_def, update_var_def]
QED

(* This is the framing part of the element copy interface.  It uses the
   allocation witness, not a claim that all source locals are disjoint. *)
Theorem for_keep_copy_frame[local]:
  keep_stable Q caller b z /\ Q s /\
  alloca_inv s /\ aid <> dstid /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\
  FLOOKUP s.vs_allocas dstid = SOME (dst,sz) /\ bytes <= sz /\
  (!x. not_fresh_at caller x ==> lookup_var x t = lookup_var x s) /\
  (!a len. a + len <= dst \/ dst + bytes <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  Q t
Proof
  strip_tac >>
  `b + z <= dst \/ dst + sz <= b` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.allocas_non_overlapping_def] >>
  `mem_bytes_at b z t.vs_memory = mem_bytes_at b z s.vs_memory` by
    (first_x_assum irule >> decide_tac) >>
  gvs[keep_stable_def] >> first_x_assum irule >>
  qexists_tac `s` >> simp[]
QED

Theorem for_iter_copy_keep[local]:
  compile_iter_elem_copy cenv src dst tybytes LocMemory F ty ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  type_memory_size tv + 64 < dimword (:256) /\
  keep_stable Q caller b z /\ Q s /\ alloca_inv s /\ aid <> dstid /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\
  FLOOKUP s.vs_allocas dstid = SOME (w2n dw,sz) /\ type_memory_size tv <= sz /\
  (!x. not_fresh_at caller x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\ Q t /\
      t.vs_allocas = s.vs_allocas /\
      (!x. not_fresh_at caller x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all stmtSimForArrayTheory.array_iter_copy_run >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `!x. not_fresh_at caller x ==> lookup_var x t = lookup_var x s` by metis_tac[] >>
  `Q t` by
    (drule_all for_keep_copy_frame >> simp[]) >>
  simp[] >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
  simp[venom_state_component_equality]
QED

(* The address prefix is register-only, so the copy boundary can retain the
   snapshot without opening the copy's implementation in round proofs. *)
Theorem dynarray_address_copy_keep[local]:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\
  not_fresh_at sa ep /\ not_fresh_at sa p /\
  keep_stable Q caller b z /\ Q s /\ alloca_inv s /\ aid <> dstid /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\
  FLOOKUP s.vs_allocas dstid = SOME (w2n dst,sz) /\ stride <= sz /\
  ~not_fresh_at caller ov /\ ~not_fresh_at caller tot /\ ~not_fresh_at caller ep /\
  (!x. not_fresh_at caller x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [Lit 32w; Var ov] [tot];
      mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z) /\
    (!x. not_fresh_at caller x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var ep (n2w (w2n arr_base + 32 + k * stride))
    (update_var tot (n2w (32 + k * stride))
      (update_var ov (n2w (k * stride)) s))` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] s = OK s1` by
    (qunabbrev_tac `s1` >> irule whitelistForIterDynLoopTheory.dynarray_address_prefix_run >> simp[]) >>
  `Q s1` by
    (qunabbrev_tac `s1` >> metis_tac[for_keep_update]) >>
  `!x. not_fresh_at caller x ==> lookup_var x s1 = lookup_var x s` by
    (simp[Abbr `s1`, emitHelperPropsTheory.lookup_var_update_var] >> metis_tac[]) >>
  `alloca_inv s1 /\ FLOOKUP s1.vs_allocas aid = SOME (b,z) /\
   FLOOKUP s1.vs_allocas dstid = SOME (w2n dst,sz)` by
    (conj_tac
     >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
         simp[Abbr `s1`, update_var_def]) >>
     simp[Abbr `s1`, update_var_def]) >>
  `eval_operand (Var ep) s1 = SOME (n2w (w2n arr_base + 32 + k * stride)) /\
   eval_operand (Var p) s1 = SOME dst` by
    simp[Abbr `s1`, eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  `val_in_memory tv v (w2n (n2w (w2n arr_base + 32 + k * stride) : bytes32))
     s1.vs_memory` by gvs[Abbr `s1`, update_var_def, w2n_n2w] >>
  `!x. Var ep = Var x \/ Var p = Var x ==> not_fresh_at sa x` by
    (simp[] >> metis_tac[]) >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_size tv + 64 < dimword (:256) /\ type_memory_size tv <= sz` by
    metis_tac[] >>
  drule_all for_iter_copy_keep >> strip_tac >>
  qexists_tac `t` >>
  `run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [Lit 32w; Var ov] [tot];
      mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0) s = OK t` by
    (qpat_x_assum `run_inst_seq [_;_;_] s = OK s1`
       (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append) >>
     simp[]) >>
  simp[]
QED

Theorem array_address_copy_keep[local]:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\
  not_fresh_at sa ep /\ not_fresh_at sa p /\
  keep_stable Q caller b z /\ Q s /\ alloca_inv s /\ aid <> dstid /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\
  FLOOKUP s.vs_allocas dstid = SOME (w2n dst,sz) /\ stride <= sz /\
  ~not_fresh_at caller ov /\ ~not_fresh_at caller ep /\
  (!x. not_fresh_at caller x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z) /\
    (!x. not_fresh_at caller x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var ep (n2w (w2n arr_base + k * stride))
      (update_var ov (n2w (k * stride)) s)` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] s = OK s1` by
    (qunabbrev_tac `s1` >> irule stmtSimForArrayLoopTheory.array_address_prefix_run >> simp[] >> metis_tac[]) >>
  `Q s1` by (qunabbrev_tac `s1` >> metis_tac[for_keep_update]) >>
  `!x. not_fresh_at caller x ==> lookup_var x s1 = lookup_var x s` by
    (simp[Abbr `s1`, emitHelperPropsTheory.lookup_var_update_var] >> metis_tac[]) >>
  `alloca_inv s1 /\ FLOOKUP s1.vs_allocas aid = SOME (b,z) /\
   FLOOKUP s1.vs_allocas dstid = SOME (w2n dst,sz)` by
    (conj_tac
     >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
         simp[Abbr `s1`, update_var_def]) >> simp[Abbr `s1`, update_var_def]) >>
  `eval_operand (Var ep) s1 = SOME (n2w (w2n arr_base + k * stride)) /\
   eval_operand (Var p) s1 = SOME dst` by
    simp[Abbr `s1`, eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  `val_in_memory tv v (w2n (n2w (w2n arr_base + k * stride) : bytes32)) s1.vs_memory` by
    gvs[Abbr `s1`, update_var_def, w2n_n2w] >>
  `!x. Var ep = Var x \/ Var p = Var x ==> not_fresh_at sa x` by (simp[] >> metis_tac[]) >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_size tv + 64 < dimword (:256) /\ type_memory_size tv <= sz` by metis_tac[] >>
  drule_all for_iter_copy_keep >> strip_tac >> qexists_tac `t` >>
  `run_inst_seq ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0) s = OK t` by
    (qpat_x_assum `run_inst_seq [_;_] s = OK s1`
       (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append) >> simp[]) >>
  simp[]
QED

Theorem dynarray_for_body_entry_keep[local]:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  keep_stable Q caller b z /\ Q s /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\ aid <> ainst.inst_id /\
  ~not_fresh_at caller ov /\ ~not_fresh_at caller tot /\ ~not_fresh_at caller ep /\
  (!x. not_fresh_at caller x ==> not_fresh_at sa x) ==>
  ?s2. whitelistForIterDynLoop$dynarray_entry_ready ctx func bc cx es id tv v
         sb0 sa ov tot ep st s s2 /\ Q s2 /\
       FLOOKUP s2.vs_allocas aid = SOME (b,z)
Proof
  strip_tac >>
  drule_all whitelistForIterDynLoopTheory.dynarray_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`, `j5`] strip_assume_tac) >>
  `not_fresh_at sa p` by
    metis_tac[stmtSimForArrayLoopTheory.array_copy_live_ptrs_reserved] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  drule_all dynarray_address_copy_keep >>
  disch_then (qspecl_then [`j5`, `j4`, `j3`] strip_assume_tac) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by metis_tac[] >>
  `t' = t` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t' = t` SUBST_ALL_TAC >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule stmtSimForArrayLoopTheory.iter_memory_copy_no_gas >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    simp[venomInstTheory.mk_inst_def] >>
  `sb0.cs_current_insts = sb0.cs_current_insts` by simp[] >>
  drule_all stmtSimForArrayLoopTheory.array_body_prefix_continuation >> strip_tac >>
  `!x. lookup_var x s2 = lookup_var x t` by simp[lookup_var_def] >>
  `Q s2` by
    (qpat_x_assum `keep_stable _ _ _ _` mp_tac >>
     simp[keep_stable_def] >> strip_tac >> first_x_assum irule >>
     qexists_tac `t` >> simp[]) >>
  qexists_tac `s2` >> simp[whitelistForIterDynLoopTheory.dynarray_entry_ready_def] >>
  fs[ret_pc_ok_def] >> metis_tac[]
QED

Theorem array_for_body_entry_keep[local]:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  keep_stable Q caller b z /\ Q s /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\ aid <> ainst.inst_id /\
  ~not_fresh_at caller ov /\ ~not_fresh_at caller ep /\
  (!x. not_fresh_at caller x ==> not_fresh_at sa x) ==>
  ?s2. stmtSimForArrayLoop$array_entry_ready ctx func bc cx es id tv v
         sb0 sa ov ep st s s2 /\ Q s2 /\
       FLOOKUP s2.vs_allocas aid = SOME (b,z)
Proof
  strip_tac >>
  drule_all stmtSimForArrayLoopTheory.array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  `not_fresh_at sa p` by
    metis_tac[stmtSimForArrayLoopTheory.array_copy_live_ptrs_reserved] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  drule_all array_address_copy_keep >>
  disch_then (qspecl_then [`j4`, `j3`] strip_assume_tac) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by metis_tac[] >>
  `t' = t` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t' = t` SUBST_ALL_TAC >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule stmtSimForArrayLoopTheory.iter_memory_copy_no_gas >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    simp[venomInstTheory.mk_inst_def] >>
  `sb0.cs_current_insts = sb0.cs_current_insts` by simp[] >>
  drule_all stmtSimForArrayLoopTheory.array_body_prefix_continuation >> strip_tac >>
  `!x. lookup_var x s2 = lookup_var x t` by simp[lookup_var_def] >>
  `Q s2` by
    (qpat_x_assum `keep_stable _ _ _ _` mp_tac >>
     simp[keep_stable_def] >> strip_tac >> first_x_assum irule >>
     qexists_tac `t` >> simp[]) >>
  qexists_tac `s2` >> simp[stmtSimForArrayLoopTheory.array_entry_ready_def] >>
  fs[ret_pc_ok_def] >> metis_tac[]
QED

(* The body boundary is shared by both layouts. It uses only the
   control, source relation and path projections of their ready relations. *)
Theorem mem_round_body_prepare_keep[local]:
  s2.vs_current_bb = sb0.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
  stmt_state_rel ctx func bc cx
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes) s2 /\
  ret_pc_ok bc sb0 s2 /\ gas_marked_path F ctx func s 0 (OK s2) /\ Q s2 /\
  gas_marked_path F ctx func cc 0 (OK s) /\
  ei = es with <|scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes; gas_obs := []|> /\
  stmt_frag_keep Q ctx func cx lctx RetQ bc m source ei /\
  m sb0 = (bc',sb1) /\ fn_has_code sb0 sb1 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ~block_is_terminated sb0 /\ gas_admissible source (stmt_res_ok lctx) ei ==>
  gas_marked_exec F (ctx,func) (push_scope_with_var id tv v) (es,cc) []
    (INL ())
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes) (OK s2) /\
  gas_outcome F (cx_tops cx) (ctx,func) source (ei,s2)
    (\res ee t. stmt_post ctx func cx lctx bc bc' sb0 sb1 s2 res ee t /\ Q t)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `gas_marked_path F ctx func cc 0 (OK s2)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  (conj_tac >- (irule stmtSimForArrayLoopTheory.push_scope_with_var_zero_exec >> simp[])) >>
  qpat_x_assum `stmt_frag_keep _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_keep_def] >>
  disch_then irule >> simp[] >>
  `!E. stmt_state_rel ctx func bc cx E s2 ==>
       stmt_state_rel ctx func bc cx (E with gas_obs := []) s2` by
    (rpt strip_tac >>
     `s2 = s2 with <|vs_gas_readings := s2.vs_gas_readings;
                     vs_inst_idx := s2.vs_inst_idx|>` by
       simp[venomStateTheory.venom_state_component_equality] >>
     pop_assum SUBST1_TAC >> irule msg_gas_state_frame >> simp[]) >>
  first_x_assum (qspec_then `es with scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes` mp_tac) >>
  impl_tac >- fs[] >>
  match_mp_tac EQ_IMPLIES >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem mem_condition_boundary_keep[local]:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lenop] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst cond_lbl st k es cc /\
  eval_operand lenop cc = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  keep_stable Q caller b z /\ Q cc /\ ~not_fresh_at caller dv /\
  FLOOKUP cc.vs_allocas aid = SOME (b,z) ==>
  ?s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst (if k = LENGTH vs then exit_lbl else stmts_lbl) st k es s /\
    Q s /\ FLOOKUP s.vs_allocas aid = SOME (b,z) /\
    (!x. x <> dv ==> lookup_var x s = lookup_var x cc) /\
    s.vs_allocas = cc.vs_allocas /\ gas_marked_path F ctx func cc 0 (OK s)
Proof
  strip_tac >>
  `k <= LENGTH vs` by fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
  `(n2w k : bytes32) = n2w (LENGTH vs) <=> k = LENGTH vs` by
    (`k < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  `?s. gas_marked_path F ctx func cc 0 (OK s) /\ Q s /\
    FLOOKUP s.vs_allocas aid = SOME (b,z) /\
    s = jump_to (if k = LENGTH vs then exit_lbl else stmts_lbl)
      (update_var dv (bool_to_word (k = LENGTH vs)) cc)` by
    (`?s. gas_marked_path F ctx func cc 0 (OK s) /\ Q s /\
       FLOOKUP s.vs_allocas aid = SOME (b,z) /\
       s = jump_to (if (n2w k : bytes32) = n2w (LENGTH vs) then exit_lbl else stmts_lbl)
         (update_var dv (bool_to_word ((n2w k : bytes32) = n2w (LENGTH vs))) cc)`
       suffices_by simp[] >>
     irule for_condition_keep >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
     reverse conj_tac >- (qexists_tac `caller` >> simp[]) >>
     qexistsl_tac [`j1`, `j2`, `Var idx`, `lenop`] >>
     simp[venomInstTheory.get_instruction_def, venomInstTheory.mk_inst_def, eval_operand_def]) >>
  qexists_tac `s` >> simp[] >> gvs[] >>
  reverse conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[stmtSimForArrayLoopTheory.array_loop_inv_def, lookup_var_def] >>
  `stmt_state_rel ctx func cenv cx es
      (update_var dv (bool_to_word (k = LENGTH vs)) cc)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  fs[stmt_state_rel_jump_to, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (Cases_on `saved_base` >>
      gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  fs[ret_pc_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `x = dv` >> gvs[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem dynarray_round_prepare_keep[local]:
  whitelistForIterDynLoop$dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + 32 + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s /\ Q s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  keep_stable Q caller b z /\ Q cc /\
  FLOOKUP cc.vs_allocas aid = SOME (b,z) /\ aid <> ainst.inst_id /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag_keep Q ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry ==>
  ?s2 bc'.
    stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
    eval_operand saved_base s2 = SOME arr_base /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    Q s2 /\ FLOOKUP s2.vs_allocas aid = SOME (b,z) /\
    stmtSimForArrayLoop$array_caller_frame caller cc s2 /\
    gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
      (es,cc) [] (INL ())
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
      (\res ee t. stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
        res ee t /\ Q t)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  drule whitelistForIterDynLoopTheory.dynarray_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv es.scopes dv /\ ~not_fresh_at caller dv` by metis_tac[] >>
  `eval_operand (Var lv) cc = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  drule_all mem_condition_boundary_keep >> strip_tac >>
  `k <> LENGTH vs` by decide_tac >> gvs[] >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule whitelistForIterDynLoopTheory.dynarray_for_code_scope_frame >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule whitelistForIterDynLoopTheory.dynarray_for_code_iteration_static >> strip_tac >>
  drule whitelistForIterDynLoopTheory.dynarray_for_code_entry_inputs >> strip_tac >>
  `~not_fresh_at caller ov /\ ~not_fresh_at caller tot /\ ~not_fresh_at caller ep` by
    metis_tac[] >>
  `?s2. whitelistForIterDynLoop$dynarray_entry_ready ctx func bc cx es id tv (EL k vs)
    sb0 sa ov tot ep sb0 s s2 /\ Q s2 /\ FLOOKUP s2.vs_allocas aid = SOME (b,z)` by
    (irule dynarray_for_body_entry_keep >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
     conj_tac >- (qexists_tac `caller` >> simp[] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (w2n dst,sz)`)) >>
     simp[] >> metis_tac[]) >>
  `?bc'. stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1)` by
    (irule stmtSimForArrayLoopTheory.array_body_compiler_env >> simp[]) >>
  qmatch_asmsub_abbrev_tac `stmt_frag_keep _ _ _ _ _ _ _ _ _ entry` >>
  `gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
      (es,cc) [] (INL ())
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
      (\res ee t. stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
        res ee t /\ Q t)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (irule mem_round_body_prepare_keep >>
     fs[whitelistForIterDynLoopTheory.dynarray_entry_ready_def, Abbr `entry`] >>
     rpt conj_tac >> metis_tac[]) >>
  drule_all whitelistForIterDynLoopTheory.dynarray_entry_ready_runtime >> strip_tac >>
  qexistsl_tac [`s2`, `bc'`] >> simp[] >>
  qhdtm_x_assum `whitelistForIterDynLoop$dynarray_entry_ready` mp_tac >>
  qpat_x_assum `!x. not_fresh_at caller x ==> _` mp_tac >>
  qpat_x_assum `!x. x <> dv ==> _` mp_tac >>
  qpat_x_assum `s.vs_allocas = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[whitelistForIterDynLoopTheory.dynarray_entry_ready_def,
    stmtSimForArrayLoopTheory.array_caller_frame_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem array_for_code_entry_inputs_keep[local]:
  stmtSimForArrayLoop$array_for_code func cenv bc ty stmts id et tv c stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  stride + 64 < dimword (:256) /\ local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!scs. not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep) /\
  p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\ stride <= sz /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  sb0.cs_current_bb = stmts_lbl /\
  compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func)
Proof
  simp[stmtSimForArrayLoopTheory.array_for_code_def, ALL_DISTINCT] >>
  rpt strip_tac >> gvs[]
QED

Theorem array_round_prepare_keep[local]:
  stmtSimForArrayLoop$array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s /\ Q s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  keep_stable Q caller b z /\ Q cc /\
  FLOOKUP cc.vs_allocas aid = SOME (b,z) /\ aid <> ainst.inst_id /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag_keep Q ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry ==>
  ?s2 bc'.
    stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
    eval_operand saved_base s2 = SOME arr_base /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    Q s2 /\ FLOOKUP s2.vs_allocas aid = SOME (b,z) /\
    stmtSimForArrayLoop$array_caller_frame caller cc s2 /\
    gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
      (es,cc) [] (INL ())
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
      (\res ee t. stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
        res ee t /\ Q t)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  drule stmtSimForArrayLoopTheory.array_for_code_entry_static >> strip_tac >>
  drule stmtSimForArrayLoopTheory.array_for_code_condition >> strip_tac >>
  `not_local_ptr cenv es.scopes dv /\ ~not_fresh_at caller dv` by metis_tac[] >>
  `eval_operand (Lit (n2w (LENGTH vs))) cc = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  drule_all mem_condition_boundary_keep >> strip_tac >>
  `k <> LENGTH vs` by decide_tac >> gvs[] >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule stmtSimForArrayLoopTheory.array_for_code_scope_frame >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule stmtSimForArrayLoopTheory.array_for_code_iteration_static >> strip_tac >>
  drule array_for_code_entry_inputs_keep >> strip_tac >>
  `~not_fresh_at caller ov /\ ~not_fresh_at caller ep` by metis_tac[] >>
  `?s2. stmtSimForArrayLoop$array_entry_ready ctx func bc cx es id tv (EL k vs)
    sb0 sa ov ep sb0 s s2 /\ Q s2 /\ FLOOKUP s2.vs_allocas aid = SOME (b,z)` by
    (irule array_for_body_entry_keep >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
     conj_tac >- (qexists_tac `caller` >> simp[] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (w2n dst,sz)`)) >>
     simp[] >> metis_tac[]) >>
  `?bc'. stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1)` by
    (irule stmtSimForArrayLoopTheory.array_body_compiler_env >> simp[]) >>
  qmatch_asmsub_abbrev_tac `stmt_frag_keep _ _ _ _ _ _ _ _ _ entry` >>
  `gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
      (es,cc) [] (INL ())
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
      (\res ee t. stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
        res ee t /\ Q t)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (irule mem_round_body_prepare_keep >>
     fs[stmtSimForArrayLoopTheory.array_entry_ready_def, Abbr `entry`] >>
     rpt conj_tac >> metis_tac[]) >>
  drule_all stmtSimForArrayLoopTheory.array_entry_ready_runtime >> strip_tac >>
  qexistsl_tac [`s2`, `bc'`] >> simp[] >>
  qhdtm_x_assum `stmtSimForArrayLoop$array_entry_ready` mp_tac >>
  qpat_x_assum `!x. not_fresh_at caller x ==> _` mp_tac >>
  qpat_x_assum `!x. x <> dv ==> _` mp_tac >>
  qpat_x_assum `s.vs_allocas = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[stmtSimForArrayLoopTheory.array_entry_ready_def,
    stmtSimForArrayLoopTheory.array_caller_frame_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* Both layouts route ordinary and continue results to the increment
   block without touching any snapshot data. Use the explicit endpoint. *)
Theorem mem_body_to_increment_keep[local]:
  stmt_lands (InLoop exit_lbl incr_lbl) sb res t /\
  (res = INL () \/ res = INR ContinueException) /\ ~t.vs_halted /\
  (res = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  keep_stable Q caller b z /\ Q t ==>
  gas_marked_path F ctx func t 0 (OK (if res = INL () then jump_to incr_lbl t else t)) /\
  Q (if res = INL () then jump_to incr_lbl t else t)
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `res = INL ()` >> gvs[]
  >- (reverse conj_tac >- (drule_all for_keep_jump >> simp[]) >>
      `t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by fs[stmt_lands_def] >>
      simp[fragGasModeTheory.gas_marked_path_def] >>
      irule stmtSimPropsTheory.emit_jump_zero_path >>
      fs[] >> goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >> simp[]) >>
  simp[fragGasModeTheory.gas_marked_path_def, fragGasPathTheory.gas_path_rules]
QED

Theorem mem_increment_loop_keep[local]:
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst incr_lbl st k es s /\ k < LENGTH vs /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\ (!l. saved_base <> Label l) /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  keep_stable Q caller b z /\ Q s /\
  ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  ?next. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst cond_lbl st (SUC k) es next /\
    Q next /\ FLOOKUP next.vs_allocas aid = SOME (b,z) /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x s) /\
    next.vs_allocas = s.vs_allocas /\ gas_marked_path F ctx func s 0 (OK next)
Proof
  strip_tac >>
  `?next. gas_marked_path F ctx func s 0 (OK next) /\ Q next /\
    FLOOKUP next.vs_allocas aid = SOME (b,z) /\
    next = jump_to cond_lbl
      (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) s))` by
    (irule for_increment_keep >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
     conj_tac >- (qexistsl_tac [`i1`, `i2`, `i3`] >> simp[]) >>
     qexists_tac `caller` >> simp[]) >>
  qexists_tac `next` >> simp[] >> gvs[] >>
  reverse conj_tac
  >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
  `stmt_state_rel ctx func cenv cx es
    (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) s))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  simp[stmt_state_rel_jump_to, jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, GSYM word_add_n2w, arithmeticTheory.ADD1] >>
  conj_tac >- (Cases_on `saved_base` >>
    gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def]) >>
  fs[lookup_var_def, ret_pc_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `x = idx` >> Cases_on `x = nv` >> gvs[FLOOKUP_UPDATE]
QED

Theorem mem_body_continue_iteration_keep[local]:
  stmt_lands (InLoop exit_lbl incr_lbl) sb res s /\
  (res = INL () \/ res = INR ContinueException) /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst s.vs_current_bb st k es (s with vs_inst_idx := 0) /\
  k < LENGTH vs /\ (!l. saved_base <> Label l) /\
  (res = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx]; mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  keep_stable Q caller b z /\ Q s /\
  ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  ?next. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst cond_lbl st (SUC k) es next /\
    Q next /\ FLOOKUP next.vs_allocas aid = SOME (b,z) /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x s) /\
    next.vs_allocas = s.vs_allocas /\ gas_marked_path F ctx func s 0 (OK next)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~s.vs_halted` by fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
  drule_all mem_body_to_increment_keep >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Q dd` >>
  qpat_x_assum `!ctx. gas_marked_path _ _ _ _ _ _ /\ _`
    (qspec_then `ctx` strip_assume_tac) >>
  `stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst incr_lbl st k es dd` by
    (Cases_on `res = INL ()` >>
     gvs[Abbr `dd`, stmtSimForArrayLoopTheory.array_loop_inv_def,
       stmt_lands_def, stmt_state_rel_jump_to, stmt_state_rel_inst_idx,
       lookup_var_def, ret_pc_ok_def] >>
     simp[jump_to_def, lookup_var_def] >>
     Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  `FLOOKUP dd.vs_allocas aid = SOME (b,z)` by
    (simp[Abbr `dd`] >> Cases_on `res = INL ()` >> simp[jump_to_def]) >>
  drule_all mem_increment_loop_keep >> strip_tac >>
  qexists_tac `next` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[Abbr `dd`] >>
      Cases_on `res = INL ()` >> simp[jump_to_def, lookup_var_def]) >>
  conj_tac
  >- (simp[Abbr `dd`] >> Cases_on `res = INL ()` >> simp[jump_to_def]) >>
  drule_all fragGasModeTheory.gas_marked_path_then >> simp[]
QED

(* The finish boundary uses only the common increment and body-jump
   projections, so Fixed and Dynamic layouts share scope/control handling. *)
Theorem mem_body_finish_counted_keep[local]:
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx]; mk_inst i3 JMP [Label cond_lbl] []]|> /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv) /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func) /\
  k < LENGTH vs /\
  gas_marked_exec F (ctx,func) (eval_stmts cx stmts) (entry,s2) marks res ee (OK t) /\
  stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
    res (ee with gas_obs := []) t /\ Q t /\
  cenv_top_ext cenv bc entry.scopes /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
  eval_operand saved_base s2 = SOME arr_base /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  stmtSimForArrayLoop$array_caller_frame caller cc s2 /\
  keep_stable Q caller b z /\ FLOOKUP s2.vs_allocas aid = SOME (b,z) /\
  ~not_fresh_at caller idx /\ ~not_fresh_at caller nv ==>
  ?rest u. ee.scopes <> [] /\ rest = TL ee.scopes /\
    gas_marked_path F ctx func t 0 (OK u) /\
    stmtSimForArrayLoop$array_caller_frame caller cc u /\
    Q u /\ FLOOKUP u.vs_allocas aid = SOME (b,z) /\
    ((res = INR BreakException /\ u.vs_current_bb = exit_lbl /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      stmt_state_rel ctx func cenv cx
        (ee with <|scopes := rest; gas_obs := []|>) u) \/
     ((res = INL () \/ res = INR ContinueException) /\
      stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
        ainst cond_lbl st (SUC k) (ee with <|scopes := rest; gas_obs := []|>) u))
Proof
  strip_tac >> drule_all stmtSimForArrayLoopTheory.array_body_counted_post >> strip_tac >>
  `stmtSimForArrayLoop$array_caller_frame caller cc t` by
    (fs[stmtSimForArrayLoopTheory.array_caller_frame_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (b,z)` by metis_tac[] >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`rest`, `t`] >>
      fs[stmt_lands_def, fragGasModeTheory.gas_marked_path_def,
         fragGasPathTheory.gas_path_rules]) >>
  `res = INL () \/ res = INR ContinueException` by fs[stmt_lands_def] >>
  drule_all stmtSimForArrayLoopTheory.array_body_runtime_frame >> strip_tac >>
  `stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst t.vs_current_bb st k (ee with <|scopes := rest; gas_obs := []|>)
    (t with vs_inst_idx := 0)` by
      (fs[stmtSimForArrayLoopTheory.array_loop_inv_def, stmt_state_rel_inst_idx,
          lookup_var_def, ret_pc_ok_def] >>
       Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  `?next. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (SUC k) (ee with <|scopes := rest; gas_obs := []|>) next /\
     Q next /\ FLOOKUP next.vs_allocas aid = SOME (b,z) /\
     (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x t) /\
     next.vs_allocas = t.vs_allocas /\ gas_marked_path F ctx func t 0 (OK next)` by
    (irule mem_body_continue_iteration_keep >> simp[] >>
     conj_tac >- (qexists_tac `caller` >> simp[]) >>
     goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
     goal_assum (drule_at (Pat `stmt_lands _ _ _ _`)) >>
     qexists_tac `sj` >> simp[]) >>
  qexistsl_tac [`rest`, `next`] >> simp[] >>
  fs[stmtSimForArrayLoopTheory.array_caller_frame_def] >> metis_tac[]
QED

Theorem dynarray_for_round_counted_keep[local]:
  whitelistForIterDynLoop$dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + 32 + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s /\ Q s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  keep_stable Q caller b z /\ Q cc /\ FLOOKUP cc.vs_allocas aid = SOME (b,z) /\
  aid <> ainst.inst_id /\ ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag_keep Q ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (es,cc)
    (\res ee t. ?broke. res = INL broke /\
      stmtSimForArrayLoop$array_caller_frame caller cc t /\
      Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z) /\
      (broke ==> t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        stmt_state_rel ctx func cenv cx ee t) /\
      (~broke ==> stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base
        p dst sz ainst cond_lbl st (SUC k) ee t))
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  `gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry` by
    (qpat_x_assum `!gs r es2. _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gasContextTheory.gas_admissible_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) round (es,cc) Post R` >>
  drule_all dynarray_round_prepare_keep >> strip_tac >>
  qhdtm_x_assum `stmt_frag_keep` kall_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >> rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "ordinary"
  >> suspend "exempt"
QED

Resume dynarray_for_round_counted_keep[exempt]:
  `?sc rest. ee.scopes = sc :: rest` by
    (drule gasExemptCertTheory.gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  gvs[] >>
  drule_all stmtSimForArrayLoopTheory.loop_round_exempt_cert >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  simp[Abbr `round`] >> goal_assum (drule_at Any)
QED

Resume dynarray_for_round_counted_keep[ordinary]:
  qhdtm_x_assum `gas_summary_at` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  `?sc rest. ee.scopes = sc :: rest` by
    (qhdtm_assum `gas_marked_exec` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  drule_all stmtSimForArrayLoopTheory.loop_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec F (ctx,func) cleanup _ _ wrapped fin r` >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin r` by
    (simp[Abbr `round`, ignore_bind_def] >>
     irule (SRULE [] (Q.INST [`left` |-> `[]`] gasSummaryComposeTheory.gas_marked_exec_bind_normal)) >>
     goal_assum (drule_at Any) >> gvs[]) >>
  strip_tac >- suspend "normal_finish" >> suspend "exit_finish"
QED

Resume dynarray_for_round_counted_keep[exit_finish]:
  fs[] >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
     metis_tac[stmt_exit_loop_ctl]) >>
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `r`] >> simp[] >> disj2_tac >>
  gvs[Abbr `R`, Abbr `fin`, Abbr `wrapped`, stmt_exit_def]
QED

Resume dynarray_for_round_counted_keep[normal_finish]:
  fs[] >>
  `cenv_top_ext cenv bc entry.scopes` by
    (drule whitelistForIterDynLoopTheory.dynarray_for_code_scope_frame >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def, cenv_top_ext_def] >> metis_tac[]) >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule whitelistForIterDynLoopTheory.dynarray_for_code_iteration_static >> strip_tac >>
  drule whitelistForIterDynLoopTheory.dynarray_for_code_entry_inputs >> strip_tac >>
  drule_all mem_body_finish_counted_keep >> strip_tac >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin (OK u)` by
    (qhdtm_x_assum `gas_marked_path` mp_tac >>
     qpat_x_assum `gas_marked_exec _ _ round _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     rpt strip_tac >> simp[] >>
     qpat_x_assum `gas_marked_path _ _ _ cc _ _` mp_tac >>
     disch_then (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `OK u`] >> simp[] >> disj1_tac >>
  simp[Abbr `Post`, Abbr `fin`, Abbr `wrapped`] >> gvs[]
QED
Finalise dynarray_for_round_counted_keep

Theorem array_for_round_counted_keep[local]:
  stmtSimForArrayLoop$array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s /\ Q s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  keep_stable Q caller b z /\ Q cc /\ FLOOKUP cc.vs_allocas aid = SOME (b,z) /\
  aid <> ainst.inst_id /\ ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag_keep Q ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (es,cc)
    (\res ee t. ?broke. res = INL broke /\
      stmtSimForArrayLoop$array_caller_frame caller cc t /\
      Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z) /\
      (broke ==> t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        stmt_state_rel ctx func cenv cx ee t) /\
      (~broke ==> stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base
        p dst sz ainst cond_lbl st (SUC k) ee t))
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  `gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry` by
    (qpat_x_assum `!gs r es2. _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gasContextTheory.gas_admissible_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) round (es,cc) Post R` >>
  drule_all array_round_prepare_keep >> strip_tac >>
  qhdtm_x_assum `stmt_frag_keep` kall_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >> rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "ordinary"
  >> suspend "exempt"
QED

Resume array_for_round_counted_keep[exempt]:
  `?sc rest. ee.scopes = sc :: rest` by
    (drule gasExemptCertTheory.gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  gvs[] >>
  drule_all stmtSimForArrayLoopTheory.loop_round_exempt_cert >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  simp[Abbr `round`] >> goal_assum (drule_at Any)
QED

Resume array_for_round_counted_keep[ordinary]:
  qhdtm_x_assum `gas_summary_at` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  `?sc rest. ee.scopes = sc :: rest` by
    (qhdtm_assum `gas_marked_exec` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  drule_all stmtSimForArrayLoopTheory.loop_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec F (ctx,func) cleanup _ _ wrapped fin r` >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin r` by
    (simp[Abbr `round`, ignore_bind_def] >>
     irule (SRULE [] (Q.INST [`left` |-> `[]`] gasSummaryComposeTheory.gas_marked_exec_bind_normal)) >>
     goal_assum (drule_at Any) >> gvs[]) >>
  strip_tac >- suspend "normal_finish" >> suspend "exit_finish"
QED

Resume array_for_round_counted_keep[exit_finish]:
  fs[] >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
     metis_tac[stmt_exit_loop_ctl]) >>
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `r`] >> simp[] >> disj2_tac >>
  gvs[Abbr `R`, Abbr `fin`, Abbr `wrapped`, stmt_exit_def]
QED

Resume array_for_round_counted_keep[normal_finish]:
  fs[] >>
  `cenv_top_ext cenv bc entry.scopes` by
    (drule stmtSimForArrayLoopTheory.array_for_code_scope_frame >>
     fs[stmtSimForArrayLoopTheory.array_loop_inv_def, cenv_top_ext_def] >> metis_tac[]) >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule stmtSimForArrayLoopTheory.array_for_code_iteration_static >> strip_tac >>
  drule array_for_code_entry_inputs_keep >> strip_tac >>
  drule_all mem_body_finish_counted_keep >> strip_tac >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin (OK u)` by
    (qhdtm_x_assum `gas_marked_path` mp_tac >>
     qpat_x_assum `gas_marked_exec _ _ round _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     rpt strip_tac >> simp[] >>
     qpat_x_assum `gas_marked_path _ _ _ cc _ _` mp_tac >>
     disch_then (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `OK u`] >> simp[] >> disj1_tac >>
  simp[Abbr `Post`, Abbr `fin`, Abbr `wrapped`] >> gvs[]
QED
Finalise array_for_round_counted_keep

Theorem mem_loop_last_counted_keep[local]:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lenop] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base
    arr_base p dst sz ainst cond_lbl st (LENGTH vs) es s /\
  eval_operand lenop s = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  keep_stable Q caller b z /\ Q s /\ ~not_fresh_at caller dv /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\
  stmtSimForArrayLoop$array_caller_frame caller old s ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx (es with gas_obs := []) t /\
    stmtSimForArrayLoop$array_caller_frame caller old t /\
    Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z)
Proof
  strip_tac >> drule_all mem_condition_boundary_keep >> simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK next)` >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) next` by
    (fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >> drule msg_gas_state_frame >>
     disch_then (qspecl_then [`next.vs_gas_readings`, `next.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  qexists_tac `next` >> fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
  fs[stmtSimForArrayLoopTheory.array_caller_frame_def] >> metis_tac[]
QED

Theorem dynarray_for_loop_counted_keep[local]:
  whitelistForIterDynLoop$dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\ evaluate_type tenv et = SOME tv /\
  (!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)) /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!j ei s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st j ei s /\ Q s /\ j < LENGTH vs ==>
     val_in_memory tv (EL j vs) (w2n arr_base + 32 + j * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at caller lv /\ lookup_var lv old = SOME (n2w (LENGTH vs)) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  keep_stable Q caller b z /\ aid <> ainst.inst_id /\
  ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  (!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    w2n arr_base + 32 + j * stride < dimword (:256) /\
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
    stmt_frag_keep Q ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))) /\
  k <= LENGTH vs /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ stmtSimForArrayLoop$array_caller_frame caller old cc /\
  Q cc /\ FLOOKUP cc.vs_allocas aid = SOME (b,z) /\
  gas_admissible (eval_for cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts (DROP k vs)) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      stmtSimForArrayLoop$array_caller_frame caller old t /\
      Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z))
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  qabbrev_tac `Inv = \j ei s.
    stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst cond_lbl st j ei s /\ stmtSimForArrayLoop$array_caller_frame caller old s /\
    Q s /\ FLOOKUP s.vs_allocas aid = SOME (b,z)` >>
  qabbrev_tac `Done = \ei s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ei s /\
    stmtSimForArrayLoop$array_caller_frame caller old s /\ Q s /\
    FLOOKUP s.vs_allocas aid = SOME (b,z)` >>
  qabbrev_tac `R = \ex ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r` >>
  `(!j ei s. j < LENGTH vs /\ Inv j ei s /\
      gas_admissible (eval_for cx tv id stmts (DROP j vs)) (stmt_res_ok lctx) ei ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (do push_scope_with_var id tv (EL j vs);
            finally (try (do eval_stmts cx stmts; return F od)
              handle_loop_exception) pop_scope od) (ei,s)
        (\res ee t. ?broke. res = INL broke /\
          (broke ==> Done ee t) /\ (~broke ==> Inv (SUC j) ee t))
        (\res ee r. ?ex. res = INR ex /\ R ex ee r)) /\
    (!ei s. Inv (LENGTH vs) ei s ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\ Done (ei with gas_obs := []) t)` by
    (conj_tac >- suspend "round" >> suspend "last") >>
  drule stmtSimForRoundsTheory.eval_for_rounds >>
  disch_then (qspecl_then [`k`, `es`, `cc`] mp_tac) >>
  simp[Abbr `Inv`, Abbr `Done`, Abbr `R`]
QED

Resume dynarray_for_loop_counted_keep[last]:
  rpt gen_tac >> simp[Abbr `Inv`, Abbr `Done`] >> strip_tac >>
  drule whitelistForIterDynLoopTheory.dynarray_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv ei.scopes dv /\ ~not_fresh_at caller dv` by metis_tac[] >>
  `eval_operand (Var lv) s = SOME (n2w (LENGTH vs))` by
    fs[stmtSimForArrayLoopTheory.array_caller_frame_def, eval_operand_def] >>
  drule_all mem_loop_last_counted_keep >> simp[]
QED

Resume dynarray_for_loop_counted_keep[round]:
  rpt gen_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `P ei /\ lookup_scopes id ei.scopes = NONE` by fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
  `lookup_var lv s = SOME (n2w (LENGTH vs))` by
    fs[stmtSimForArrayLoopTheory.array_caller_frame_def] >>
  qpat_assum `!ei j. _` drule_all >> strip_tac >>
  `value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)` by metis_tac[] >>
  qabbrev_tac `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> simp[Abbr `entry`]) >>
  `!t. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst stmts_lbl st j ei t /\ Q t ==>
    val_in_memory tv (EL j vs) (w2n arr_base + 32 + j * stride) t.vs_memory /\
    ret_pc_ok bc sb0 t` by metis_tac[] >>
  `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` by simp[Abbr `entry`] >>
  drule_all dynarray_for_round_counted_keep >> strip_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >>
  qpat_x_assum `stmtSimForArrayLoop$array_caller_frame caller old s` mp_tac >>
  simp[Abbr `Done`, Abbr `R`, NoAsms] >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qhdtm_x_assum `gas_summary_at` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >> suspend "round_post") >>
  qexists_tac `marks` >> disj2_tac >> goal_assum (drule_at Any)
QED
Resume dynarray_for_loop_counted_keep[round_post]:
  markerLib.RESUME_TAC >> gvs[] >>
  `stmtSimForArrayLoop$array_caller_frame caller old t` by
    (irule stmtSimForArrayLoopTheory.array_caller_frame_trans >> goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED
Finalise dynarray_for_loop_counted_keep

Theorem array_for_loop_counted_keep[local]:
  stmtSimForArrayLoop$array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\ evaluate_type tenv et = SOME tv /\
  (!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)) /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!j ei s. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st j ei s /\ Q s /\ j < LENGTH vs ==>
     val_in_memory tv (EL j vs) (w2n arr_base + j * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  keep_stable Q caller b z /\ aid <> ainst.inst_id /\
  ~not_fresh_at caller idx /\ ~not_fresh_at caller nv /\
  (!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    w2n arr_base + j * stride < dimword (:256) /\
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
    stmt_frag_keep Q ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))) /\
  k <= LENGTH vs /\
  stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ stmtSimForArrayLoop$array_caller_frame caller old cc /\
  Q cc /\ FLOOKUP cc.vs_allocas aid = SOME (b,z) /\
  gas_admissible (eval_for cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts (DROP k vs)) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      stmtSimForArrayLoop$array_caller_frame caller old t /\
      Q t /\ FLOOKUP t.vs_allocas aid = SOME (b,z))
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  qabbrev_tac `Inv = \j ei s.
    stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst cond_lbl st j ei s /\ stmtSimForArrayLoop$array_caller_frame caller old s /\
    Q s /\ FLOOKUP s.vs_allocas aid = SOME (b,z)` >>
  qabbrev_tac `Done = \ei s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ei s /\
    stmtSimForArrayLoop$array_caller_frame caller old s /\ Q s /\
    FLOOKUP s.vs_allocas aid = SOME (b,z)` >>
  qabbrev_tac `R = \ex ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r` >>
  `(!j ei s. j < LENGTH vs /\ Inv j ei s /\
      gas_admissible (eval_for cx tv id stmts (DROP j vs)) (stmt_res_ok lctx) ei ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (do push_scope_with_var id tv (EL j vs);
            finally (try (do eval_stmts cx stmts; return F od)
              handle_loop_exception) pop_scope od) (ei,s)
        (\res ee t. ?broke. res = INL broke /\
          (broke ==> Done ee t) /\ (~broke ==> Inv (SUC j) ee t))
        (\res ee r. ?ex. res = INR ex /\ R ex ee r)) /\
    (!ei s. Inv (LENGTH vs) ei s ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\ Done (ei with gas_obs := []) t)` by
    (conj_tac >- suspend "round" >> suspend "last") >>
  drule stmtSimForRoundsTheory.eval_for_rounds >>
  disch_then (qspecl_then [`k`, `es`, `cc`] mp_tac) >>
  simp[Abbr `Inv`, Abbr `Done`, Abbr `R`]
QED

Resume array_for_loop_counted_keep[last]:
  rpt gen_tac >> simp[Abbr `Inv`, Abbr `Done`] >> strip_tac >>
  drule stmtSimForArrayLoopTheory.array_for_code_entry_static >> strip_tac >>
  drule stmtSimForArrayLoopTheory.array_for_code_condition >> strip_tac >>
  `not_local_ptr cenv ei.scopes dv /\ ~not_fresh_at caller dv` by metis_tac[] >>
  `eval_operand (Lit (n2w (LENGTH vs))) s = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  drule_all mem_loop_last_counted_keep >> simp[]
QED

Resume array_for_loop_counted_keep[round]:
  rpt gen_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `P ei /\ lookup_scopes id ei.scopes = NONE` by fs[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
  qpat_assum `!ei j. _` drule_all >> strip_tac >>
  `value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)` by metis_tac[] >>
  qabbrev_tac `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> simp[Abbr `entry`]) >>
  `!t. stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst stmts_lbl st j ei t /\ Q t ==>
    val_in_memory tv (EL j vs) (w2n arr_base + j * stride) t.vs_memory /\
    ret_pc_ok bc sb0 t` by metis_tac[] >>
  `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` by simp[Abbr `entry`] >>
  drule_all array_for_round_counted_keep >> strip_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >>
  qpat_x_assum `stmtSimForArrayLoop$array_caller_frame caller old s` mp_tac >>
  simp[Abbr `Done`, Abbr `R`, NoAsms] >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qhdtm_x_assum `gas_summary_at` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >> suspend "round_post") >>
  qexists_tac `marks` >> disj2_tac >> goal_assum (drule_at Any)
QED
Resume array_for_loop_counted_keep[round_post]:
  markerLib.RESUME_TAC >> gvs[] >>
  `stmtSimForArrayLoop$array_caller_frame caller old t` by
    (irule stmtSimForArrayLoopTheory.array_caller_frame_trans >> goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED
Finalise array_for_loop_counted_keep

Theorem compile_for_mem_dynamic_stages[local]:
  expr_type arr_e = ArrayT et (Dynamic c) /\
  compile_expr cenv (ArrayT et (Dynamic c)) arr_e se = (vv,st) /\
  vv_location vv = SOME LocMemory /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),st') ==>
  ?lvo st1 bc entry cond bod incr exit idx offo toto epo sa sb0 sb1 sj.
    emit_op MLOAD [vv_operand vv] st = (lvo,st1) /\
    (do bc <- declare_local cenv id et;
        emit_local_alloca bc id;
        entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        (do invalid <- emit_op GT [lvo; Lit (n2w c)];
            valid <- emit_op ISZERO [invalid];
            emit_void ASSERT [valid] od);
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; lvo];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        off <- emit_op MUL [Var idx;
                   Lit (n2w (elem_size_in_location cenv LocMemory et))];
        tot <- emit_op ADD [Lit 32w; off];
        ep <- emit_op ADD [vv_operand vv; tot];
        return (bc,entry,cond,bod,incr,exit,idx,off,tot,ep)
     od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) => compile_iter_elem_copy cenv epo (Lit (n2w dst))
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
     | SOME (PtrVar ptr_op _) => compile_iter_elem_copy cenv epo ptr_op
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
     | _ => emit_void INVALID []) sa = ((),sb0) /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    (do new_block incr;
        next <- emit_op ADD [Var idx; Lit 1w];
        emit_inst ASSIGN [next] [idx]; emit_inst JMP [Label cond] [];
        new_block exit; return () od) sj = ((),st')
Proof
  strip_tac >> qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, LET_THM, is_slot_addressed_def,
       contextTheory.compile_ptr_load_def, word_scale_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]
QED

Theorem compile_for_mem_dynamic_parts[local]:
  expr_type arr_e = ArrayT et (Dynamic c) /\
  compile_expr cenv (ArrayT et (Dynamic c)) arr_e se = (vv,st) /\
  vv_location vv = SOME LocMemory /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),st') /\
  cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) ==>
  ?st1 bc lv p idx g vld dv ov tot ep nv entry cond bod incr exit sa sb0 sb1 sj.
    lv = STRING #"%" (toString st.cs_next_var) /\
    p = STRING #"%" (toString (st.cs_next_var + 1)) /\
    idx = STRING #"%" (toString (st.cs_next_var + 2)) /\
    g = STRING #"%" (toString (st.cs_next_var + 3)) /\
    vld = STRING #"%" (toString (st.cs_next_var + 4)) /\
    dv = STRING #"%" (toString (st.cs_next_var + 5)) /\
    ov = STRING #"%" (toString (st.cs_next_var + 6)) /\
    tot = STRING #"%" (toString (st.cs_next_var + 7)) /\
    ep = STRING #"%" (toString (st.cs_next_var + 8)) /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    st1.cs_next_var = st.cs_next_var + 1 /\
    declare_local cenv id et st1 = (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst (st.cs_next_id + 10) MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocMemory et))] [ov];
       mk_inst (st.cs_next_id + 11) ADD [Lit 32w; Var ov] [tot];
       mk_inst (st.cs_next_id + 12) ADD [vv_operand vv; Var tot] [ep]] /\
    sa.cs_next_var = st.cs_next_var + 9 /\
    compile_iter_elem_copy cenv (Var ep) (Var p)
      (elem_size_in_location cenv LocMemory et) LocMemory F et et sa = ((),sb0) /\
    sb0.cs_current_bb = bod /\ same_blocks sa sb0 /\
    sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
    ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    sj.cs_next_var = sb1.cs_next_var /\
    (~block_is_terminated sb1 ==>
      sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
      sj.cs_current_insts = sb1.cs_current_insts ++
        [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
    cs_extends st sa /\ cs_extends sa sb0 /\ cs_extends sb0 sb1 /\
    cs_extends sb1 sj /\ cs_extends sj st' /\
    fn_has_code st sa func /\ fn_has_code sa sb0 func /\
    fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\ fn_has_code sj st' func /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
        [mk_inst st.cs_next_id MLOAD [vv_operand vv] [lv];
         mk_inst (st.cs_next_id + 1) ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p];
         mk_inst (st.cs_next_id + 2) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 4) GT [Var lv; Lit (n2w c)] [g];
         mk_inst (st.cs_next_id + 5) ISZERO [Var g] [vld];
         mk_inst (st.cs_next_id + 6) ASSERT [Var vld] [];
         mk_inst (st.cs_next_id + 7) JMP [Label cond] []]|> /\
    lookup_block cond func.fn_blocks =
      SOME <|bb_label := cond; bb_instructions :=
        [mk_inst (st.cs_next_id + 8) EQ [Var idx; Var lv] [dv];
         mk_inst (st.cs_next_id + 9) JNZ [Var dv; Label exit; Label bod] []]|> /\
    lookup_block incr func.fn_blocks =
      SOME <|bb_label := incr; bb_instructions :=
        [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
         mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
         mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = []
Proof
  strip_tac >> drule_all compile_for_mem_dynamic_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  drule_all compile_for_dynarray_prefix >> strip_tac >>
  dxrule stmtSimForArrayPartsTheory.compile_for_array_suffix >> strip_tac >>
  `cs_extends st sa` by
    (irule stmtSimForArrayPartsTheory.array_prefix_extends >> simp[] >> metis_tac[]) >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def, venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
  drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
  drule stmtSimForArrayPartsTheory.array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  drule_all stmtSimForArrayPartsTheory.array_stages_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sa.cs_blocks = preblocks ++ st.cs_blocks` >>
  qmatch_asmsub_abbrev_tac `st'.cs_blocks = postblocks ++ sj.cs_blocks` >>
  qexistsl_tac [`st1`, `bc`, `entry`, `cond`, `incr`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[] >> rpt conj_tac
  >- fs[same_blocks_def]
  >- (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
      (conj_tac >- simp[]) >> qexistsl_tac [`preblocks`, `st`, `sa`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [Abbr `preblocks`, MEM] >>
      disj2_tac >> disj2_tac >> disj1_tac >> simp[])
  >- (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
      (conj_tac >- simp[]) >> qexistsl_tac [`preblocks`, `st`, `sa`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [Abbr `preblocks`, MEM] >>
      disj2_tac >> disj1_tac >> simp[])
  >- (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
      (conj_tac >- simp[]) >> qexistsl_tac [`preblocks`, `st`, `sa`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [Abbr `preblocks`, MEM] >> disj1_tac >> simp[])
  >> irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
  (conj_tac >- simp[]) >> qexistsl_tac [`postblocks`, `sj`, `st'`] >>
  (conj_tac >- simp[]) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  simp_tac pure_ss [Abbr `postblocks`, MEM] >> disj1_tac >> simp[]
QED

Theorem mem_dynamic_register_frame[local]:
  local_ptrs_reserved cenv st /\
  (!x. arr_op = Var x ==> not_fresh_at st x) /\
  st.cs_next_var + 9 <= sj.cs_next_var /\
  lv = STRING #"%" (toString st.cs_next_var) /\
  p = STRING #"%" (toString (st.cs_next_var + 1)) /\
  idx = STRING #"%" (toString (st.cs_next_var + 2)) /\
  g = STRING #"%" (toString (st.cs_next_var + 3)) /\
  vld = STRING #"%" (toString (st.cs_next_var + 4)) /\
  dv = STRING #"%" (toString (st.cs_next_var + 5)) /\
  ov = STRING #"%" (toString (st.cs_next_var + 6)) /\
  tot = STRING #"%" (toString (st.cs_next_var + 7)) /\
  ep = STRING #"%" (toString (st.cs_next_var + 8)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  ALL_DISTINCT [idx; dv; ov; tot; ep; nv; p; lv; g; vld] /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
         not_local_ptr cenv scs ep /\ not_local_ptr cenv scs nv /\
         not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
         not_local_ptr cenv scs vld) /\
  (!x. not_fresh_at st x ==> ~MEM x [idx; dv; ov; tot; ep; nv; p; lv; g; vld])
Proof
  strip_tac >>
  `!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
         not_local_ptr cenv scs ep /\ not_local_ptr cenv scs nv /\
         not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
         not_local_ptr cenv scs vld` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  simp[] >> simp[not_fresh_at_def] >> rpt strip_tac >> gvs[]
QED

Theorem compile_for_mem_dynamic_code_ready[local]:
  expr_type arr_e = ArrayT et (Dynamic c) /\
  compile_expr cenv (ArrayT et (Dynamic c)) arr_e se = (vv,st) /\
  vv_location vv = SOME LocMemory /\
  (!x. vv_operand vv = Var x ==> not_fresh_at st x) /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),st') /\
  cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) ==>
  ?st1 bc lv p idx g vld dv ov tot ep nv entry cond bod incr exit sa sb0 sb1 sj ainst.
    whitelistForIterDynLoop$dynarray_for_code func cenv bc ty stmts id et tv
      (type_memory_bytes cenv et) (vv_operand vv) p (type_memory_bytes cenv et)
      ainst idx dv ov tot ep nv lv cond exit bod incr
      (st.cs_next_id + 8) (st.cs_next_id + 9) (st.cs_next_id + 10)
      (st.cs_next_id + 11) (st.cs_next_id + 12)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    ainst = mk_inst (st.cs_next_id + 1) ALLOCA
      [Lit (n2w (type_memory_bytes cenv et))] [p] /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
        [mk_inst st.cs_next_id MLOAD [vv_operand vv] [lv]; ainst;
         mk_inst (st.cs_next_id + 2) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 4) GT [Var lv; Lit (n2w c)] [g];
         mk_inst (st.cs_next_id + 5) ISZERO [Var g] [vld];
         mk_inst (st.cs_next_id + 6) ASSERT [Var vld] [];
         mk_inst (st.cs_next_id + 7) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    (?sd. declare_local cenv id et st1 = (bc,sd)) /\
    ALL_DISTINCT [lv; p; idx; g; vld] /\
    (!scs. not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
           not_local_ptr cenv scs vld /\ not_local_ptr cenv scs idx) /\
    (!x. vv_operand vv = Var x ==> ~MEM x [lv; p; idx; g; vld]) /\
    (!x. not_fresh_at st x ==> ~MEM x [lv; p; idx; g; vld]) /\
    (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
    (!x. not_fresh_at st1 x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
    (!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at st1 lv /\ not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sb0 x)
Proof
  strip_tac >>
  `!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb`
    by metis_tac[] >>
  drule_all compile_for_mem_dynamic_parts >> strip_tac >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  `st.cs_next_var + 9 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc sa sb. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all mem_dynamic_register_frame >> strip_tac >>
  `local_ptrs_reserved cenv st1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `st1.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all stmtSimForArrayFragTheory.array_declared_reserved >> strip_tac >>
  `MEM (mk_inst (st.cs_next_id + 1) ALLOCA
          [Lit (n2w (type_memory_bytes cenv et))] [p]) (fn_insts func)` by
    (irule fragExecTheory.lookup_block_fn_insts >>
     qpat_assum `lookup_block st.cs_current_bb _ = _` (irule_at (Pos hd)) >> simp[]) >>
  qexistsl_tac [`st1`, `bc`, `lv`, `p`, `idx`, `g`, `vld`, `dv`, `ov`, `tot`,
    `ep`, `nv`, `entry`, `cond`, `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`] >>
  simp[] >> rpt conj_tac
  >- (`elem_size_in_location cenv LocMemory et = type_memory_size tv` by
        simp[compileEnvTheory.elem_size_in_location_def, is_slot_addressed_def] >>
      simp[whitelistForIterDynLoopTheory.dynarray_for_code_def, venomInstTheory.mk_inst_def] >>
      gvs[ALL_DISTINCT] >>
      qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      qpat_x_assum `MEM _ (fn_insts func)` mp_tac >>
      simp[venomInstTheory.mk_inst_def] >> rpt strip_tac >> simp[not_fresh_at_def] >>
      rpt strip_tac >> rename1 `x = STRING #"%" (toString m)` >>
      qpat_x_assum `!x. vv_operand vv = Var x ==> _` drule >>
      rewrite_tac[not_fresh_at_def] >> disch_then (qspec_then `m` mp_tac) >> simp[])
  >- gvs[ALL_DISTINCT]
  >- (rpt strip_tac >> gvs[] >> fs[not_fresh_at_def])
  >- (rpt strip_tac >> qpat_x_assum `not_fresh_at st _` mp_tac >> simp[not_fresh_at_def])
  >- simp[not_fresh_at_def]
  >- (simp[not_fresh_at_def] >> rpt strip_tac >> gvs[])
  >- (simp[not_fresh_at_def] >> rpt strip_tac >> gvs[])
  >- simp[not_fresh_at_def]
  >- simp[not_fresh_at_def]
  >> rpt strip_tac >>
  qpat_x_assum `!x. vv_operand vv = Var x ==> not_fresh_at st x` drule >>
  rewrite_tac[not_fresh_at_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem compile_for_mem_fixed_stages[local]:
  expr_type arr_e = ArrayT et (Fixed c) /\
  compile_expr cenv (ArrayT et (Fixed c)) arr_e se = (vv,st) /\
  vv_location vv = SOME LocMemory /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),st') ==>
  ?bc entry cond bod incr exit idx off ep sa sb0 sb1 sj.
    (do bc <- declare_local cenv id et;
        emit_local_alloca bc id;
        entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; Lit (n2w c)];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        off <- emit_op MUL [Var idx;
                   Lit (n2w (elem_size_in_location cenv LocMemory et))];
        ep <- emit_op ADD [vv_operand vv; off];
        return (bc,entry,cond,bod,incr,exit,idx,off,ep)
     od) st = ((bc,entry,cond,bod,incr,exit,idx,off,ep),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) => compile_iter_elem_copy cenv ep (Lit (n2w dst))
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
     | SOME (PtrVar ptr_op _) => compile_iter_elem_copy cenv ep ptr_op
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
     | _ => emit_void INVALID []) sa = ((),sb0) /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    (do new_block incr;
        next <- emit_op ADD [Var idx; Lit 1w];
        emit_inst ASSIGN [next] [idx]; emit_inst JMP [Label cond] [];
        new_block exit; return () od) sj = ((),st')
Proof
  strip_tac >> qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, LET_THM, is_slot_addressed_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]
QED

Theorem compile_for_mem_fixed_parts[local]:
  expr_type arr_e = ArrayT et (Fixed c) /\
  compile_expr cenv (ArrayT et (Fixed c)) arr_e se = (vv,st) /\
  vv_location vv = SOME LocMemory /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),st') /\
  cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) ==>
  ?bc p idx dv ov ep nv entry cond bod incr exit sa sb0 sb1 sj.
    p = STRING #"%" (toString st.cs_next_var) /\
    idx = STRING #"%" (toString (st.cs_next_var + 1)) /\
    dv = STRING #"%" (toString (st.cs_next_var + 2)) /\
    ov = STRING #"%" (toString (st.cs_next_var + 3)) /\
    ep = STRING #"%" (toString (st.cs_next_var + 4)) /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    declare_local cenv id et st = (bc, st with cs_next_var := st.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst (st.cs_next_id + 6) MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocMemory et))] [ov];
       mk_inst (st.cs_next_id + 7) ADD [vv_operand vv; Var ov] [ep]] /\
    sa.cs_next_var = st.cs_next_var + 5 /\
    compile_iter_elem_copy cenv (Var ep) (Var p)
      (elem_size_in_location cenv LocMemory et) LocMemory F et et sa = ((),sb0) /\
    sb0.cs_current_bb = bod /\ same_blocks sa sb0 /\
    sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
    ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    sj.cs_next_var = sb1.cs_next_var /\
    (~block_is_terminated sb1 ==>
      sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
      sj.cs_current_insts = sb1.cs_current_insts ++
        [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
    cs_extends st sa /\ cs_extends sa sb0 /\ cs_extends sb0 sb1 /\
    cs_extends sb1 sj /\ cs_extends sj st' /\
    fn_has_code st sa func /\ fn_has_code sa sb0 func /\
    fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\ fn_has_code sj st' func /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
        [mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p];
         mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|> /\
    lookup_block cond func.fn_blocks =
      SOME <|bb_label := cond; bb_instructions :=
        [mk_inst (st.cs_next_id + 4) EQ [Var idx; Lit (n2w c)] [dv];
         mk_inst (st.cs_next_id + 5) JNZ [Var dv; Label exit; Label bod] []]|> /\
    lookup_block incr func.fn_blocks =
      SOME <|bb_label := incr; bb_instructions :=
        [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
         mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
         mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = []
Proof
  strip_tac >> drule_all compile_for_mem_fixed_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  drule_all stmtSimForArrayPartsTheory.compile_for_array_prefix >> strip_tac >>
  dxrule stmtSimForArrayPartsTheory.compile_for_array_suffix >> strip_tac >>
  `cs_extends st sa` by
    (irule stmtSimForArrayPartsTheory.array_prefix_extends >> simp[] >> metis_tac[]) >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def, venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
  drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
  drule stmtSimForArrayPartsTheory.array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  drule_all stmtSimForArrayPartsTheory.array_stages_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sa.cs_blocks = preblocks ++ st.cs_blocks` >>
  qmatch_asmsub_abbrev_tac `st'.cs_blocks = postblocks ++ sj.cs_blocks` >>
  qexistsl_tac [`entry`, `cond`, `incr`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[] >> rpt conj_tac
  >- fs[same_blocks_def]
  >- (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
      (conj_tac >- simp[]) >> qexistsl_tac [`preblocks`, `st`, `sa`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [Abbr `preblocks`, MEM] >>
      disj2_tac >> disj2_tac >> disj1_tac >> simp[])
  >- (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
      (conj_tac >- simp[]) >> qexistsl_tac [`preblocks`, `st`, `sa`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [Abbr `preblocks`, MEM] >> disj2_tac >> disj1_tac >> simp[])
  >- (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
      (conj_tac >- simp[]) >> qexistsl_tac [`preblocks`, `st`, `sa`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [Abbr `preblocks`, MEM] >> disj1_tac >> simp[])
  >> irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
  (conj_tac >- simp[]) >> qexistsl_tac [`postblocks`, `sj`, `st'`] >>
  (conj_tac >- simp[]) >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  simp_tac pure_ss [Abbr `postblocks`, MEM] >> disj1_tac >> simp[]
QED

Theorem mem_fixed_register_frame[local]:
  local_ptrs_reserved cenv st /\
  (!x. arr_op = Var x ==> not_fresh_at st x) /\
  sa.cs_next_var = st.cs_next_var + 5 /\ st.cs_next_var + 5 <= sj.cs_next_var /\
  p = STRING #"%" (toString st.cs_next_var) /\
  idx = STRING #"%" (toString (st.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st.cs_next_var + 2)) /\
  ov = STRING #"%" (toString (st.cs_next_var + 3)) /\
  ep = STRING #"%" (toString (st.cs_next_var + 4)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  ALL_DISTINCT [idx;dv;ov;ep;nv;p] /\
  not_fresh_at sa p /\ not_fresh_at sa idx /\ not_fresh_at sa ep /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv) /\
  (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  (!x. arr_op = Var x ==> ~MEM x [idx;dv;ov;ep;nv])
Proof
  strip_tac >>
  `!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  simp[] >> simp[not_fresh_at_def] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_for_mem_fixed_code_ready[local]:
  expr_type arr_e = ArrayT et (Fixed c) /\
  compile_expr cenv (ArrayT et (Fixed c)) arr_e se = (vv,st) /\
  vv_location vv = SOME LocMemory /\
  (!x. vv_operand vv = Var x ==> not_fresh_at st x) /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),st') /\
  cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) ==>
  ?bc p idx dv ov ep nv entry cond bod incr exit sa sb0 sb1 sj ainst.
    stmtSimForArrayLoop$array_for_code func cenv bc ty stmts id et tv c
      (type_memory_bytes cenv et) (vv_operand vv) p (type_memory_bytes cenv et)
      ainst idx dv ov ep nv cond exit bod incr
      (st.cs_next_id + 4) (st.cs_next_id + 5) (st.cs_next_id + 6) (st.cs_next_id + 7)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    ainst = mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p] /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
        [ainst; mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    declare_local cenv id et st = (bc, st with cs_next_var := st.cs_next_var + 1) /\
    cs_extends st sa /\
    (!scs. not_local_ptr cenv scs idx) /\ p <> idx /\
    (!x. vv_operand vv = Var x ==> x <> p /\ x <> idx) /\
    (!x. not_fresh_at st x ==> x <> p /\ x <> idx)
Proof
  strip_tac >>
  `!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb`
    by metis_tac[] >>
  drule_all compile_for_mem_fixed_parts >> strip_tac >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  `st.cs_next_var + 5 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc sa sb. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all mem_fixed_register_frame >> strip_tac >>
  `st.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all stmtSimForArrayFragTheory.array_declared_reserved >> strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA
          [Lit (n2w (type_memory_bytes cenv et))] [p]) (fn_insts func)` by
    (irule fragExecTheory.lookup_block_fn_insts >>
     qpat_assum `lookup_block st.cs_current_bb _ = _` (irule_at (Pos hd)) >> simp[]) >>
  qexistsl_tac [`bc`, `p`, `idx`, `dv`, `ov`, `ep`, `nv`, `entry`, `cond`, `bod`,
    `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`] >> simp[] >> rpt conj_tac
  >- (`elem_size_in_location cenv LocMemory et = type_memory_size tv` by
        simp[elem_size_in_location_def, is_slot_addressed_def] >>
      simp[stmtSimForArrayLoopTheory.array_for_code_def, venomInstTheory.mk_inst_def] >>
      gvs[ALL_DISTINCT] >>
      qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      qpat_x_assum `MEM _ (fn_insts func)` mp_tac >>
      simp[venomInstTheory.mk_inst_def])
  >> rpt strip_tac >> gvs[] >> fs[not_fresh_at_def]
QED

Theorem dynarray_loop_initialize_keep[local]:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\
  ret_pc_ok cenv st s0 /\
  ALL_DISTINCT [lv; p; idx; g; vld] /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv; p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv; p; idx; g; vld]) /\
  keep_stable Q caller b z /\ Q s0 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,z) /\
  (!x. MEM x [lv; p; idx; g; vld] ==> ~not_fresh_at caller x) ==>
  ?dst cc.
    stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    stmtSimForArrayLoop$array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    Q cc /\ FLOOKUP cc.vs_allocas aid = SOME (b,z)
Proof
  strip_tac >>
  drule_all whitelistForIterDynFragTheory.dynarray_loop_initialize_explicit >> strip_tac >>
  `Q (update_var lv (n2w (LENGTH vs)) s0)` by
    (irule for_keep_update >> metis_tac[MEM]) >>
  `FLOOKUP (update_var lv (n2w (LENGTH vs)) s0).vs_allocas aid = SOME (b,z)` by
    simp[update_var_def] >>
  `~not_fresh_at caller p` by metis_tac[MEM] >>
  drule_all for_keep_alloca >> strip_tac >>
  `Q cc` by
    (simp[] >> metis_tac[for_keep_jump, for_keep_update, MEM]) >>
  qexistsl_tac [`dst`, `cc`] >>
  simp[jump_to_def, update_var_def]
QED

Theorem array_loop_initialize_keep[local]:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\ ret_pc_ok cenv st s0 /\
  p <> idx /\ not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  (!x. saved_base = Var x ==> x <> p /\ x <> idx) /\
  (!x. not_fresh_at st x ==> x <> p /\ x <> idx) /\
  keep_stable Q caller b z /\ Q s0 /\ FLOOKUP s0.vs_allocas aid = SOME (b,z) /\
  ~not_fresh_at caller p /\ ~not_fresh_at caller idx ==>
  ?dst cc s1.
    stmtSimForArrayLoop$array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    stmtSimForArrayLoop$array_caller_frame caller s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    Q cc /\ FLOOKUP cc.vs_allocas aid = SOME (b,z) /\
    exec_alloca ainst s0 (n2w sz : bytes32) = OK s1 /\
    cc = jump_to cond (update_var idx 0w (jump_to entry s1))
Proof
  strip_tac >>
  `!x. saved_base = Var x ==> x <> p` by metis_tac[] >>
  drule_all stmtSimForArrayFragTheory.array_allocate_ready >> strip_tac >>
  drule_all stmtSimForArrayFragTheory.array_alloca_frame >> strip_tac >>
  drule_all for_keep_alloca >> strip_tac >>
  `step_inst_base ainst s0 = OK s1` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, eval_operand_def] >>
  `gas_marked_path F ctx func s0 0 (OK (jump_to entry s1))` by
    (irule stmtSimForArrayLoopTheory.inst_seq_jump_zero_path >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`<|bb_label := lbl; bb_instructions :=
       pre ++ [ainst; mk_inst j JMP [Label entry] []]|>`, `[ainst]`, `j`] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def, venomInstTheory.is_terminator_def]) >>
  qabbrev_tac `e0 = jump_to entry s1` >>
  `e0.vs_current_bb = entry /\ e0.vs_inst_idx = 0 /\ ~e0.vs_halted` by
    simp[Abbr `e0`, jump_to_def] >>
  `gas_marked_path F ctx func e0 0 (OK (jump_to cond (update_var idx 0w e0)))` by
    (irule stmtSimForArrayLoopTheory.inst_seq_jump_zero_path >>
     conj_tac >- simp[] >>
     qexistsl_tac [`<|bb_label := entry; bb_instructions :=
       [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|>`,
       `[mk_inst ei ASSIGN [Lit 0w] [idx]]`, `ej`] >>
     simp[run_inst_seq_def, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs, eval_operand_def]) >>
  qabbrev_tac `cc = jump_to cond (update_var idx 0w e0)` >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[Abbr `e0`, stmt_state_rel_jump_to]) >>
  `eval_operand saved_base cc = SOME array_base` by
    (Cases_on `saved_base` >>
     gvs[Abbr `cc`, Abbr `e0`, jump_to_def, eval_operand_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `Q cc` by
    (simp[Abbr `cc`, Abbr `e0`] >> metis_tac[for_keep_jump, for_keep_update]) >>
  `ret_pc_ok cenv st cc` by
    simp[Abbr `cc`, Abbr `e0`, stmtSimPropsTheory.ret_pc_ok_jump_to,
         stmtSimForArrayLoopTheory.array_ret_pc_update] >>
  qexistsl_tac [`dst`, `cc`, `s1`] >>
  conj_tac
  >- (simp[stmtSimForArrayLoopTheory.array_loop_inv_def] >>
      fs[Abbr `cc`, Abbr `e0`, jump_to_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (simp[stmtSimForArrayLoopTheory.array_caller_frame_def] >>
      conj_tac
      >- (rpt strip_tac >>
          `x <> p /\ x <> idx` by metis_tac[] >>
          `lookup_var x s1 = lookup_var x s0` by metis_tac[] >>
          fs[Abbr `cc`, Abbr `e0`, jump_to_def, update_var_def,
             lookup_var_def, FLOOKUP_UPDATE]) >>
      rpt strip_tac >> simp[Abbr `cc`, Abbr `e0`, jump_to_def, update_var_def] >>
      first_x_assum irule >> goal_assum (drule_at Any)) >>
  conj_tac >- (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  simp[Abbr `cc`, Abbr `e0`, jump_to_def, update_var_def]
QED

(* Ownership of the expression and loop intervals is separated before
   applying expression simulation; this boundary needs no runtime hook. *)
Theorem compile_for_mem_suffix_extends[local]:
  expr_type arr_e = ArrayT et bd /\ (bd = Fixed c \/ bd = Dynamic c) /\
  compile_expr cenv (ArrayT et bd) arr_e se = (vv,sm) /\
  vv_location vv = SOME LocMemory /\ cenv.ce_alloca_locals /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),sf) /\
  (!bc lc sa sb. compile_stmts bc lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb) ==> cs_extends sm sf
Proof
  strip_tac >> gvs[]
  >- (drule_all compile_for_mem_fixed_stages >> strip_tac >>
      qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
      drule_all stmtSimForArrayPartsTheory.compile_for_array_prefix >> strip_tac >>
      dxrule stmtSimForArrayPartsTheory.compile_for_array_suffix >> strip_tac >>
      `cs_extends sm sa` by
        (irule stmtSimForArrayPartsTheory.array_prefix_extends >> simp[] >> metis_tac[]) >>
      `~block_is_terminated sa` by
        simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
             venomInstTheory.is_terminator_def] >>
      qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
      drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
      drule stmtSimForArrayPartsTheory.array_body_backedge >> strip_tac >>
      `cs_extends sb0 sb1` by metis_tac[] >>
      metis_tac[compileEnvTheory.cs_extends_trans]) >>
  drule_all compile_for_mem_dynamic_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  drule_all compile_for_dynarray_prefix >> strip_tac >>
  dxrule stmtSimForArrayPartsTheory.compile_for_array_suffix >> strip_tac >>
  `cs_extends sm sa` by
    (irule stmtSimForArrayPartsTheory.array_prefix_extends >> simp[] >> metis_tac[]) >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def] >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
  drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
  drule stmtSimForArrayPartsTheory.array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  metis_tac[compileEnvTheory.cs_extends_trans]
QED

Theorem compile_for_mem_code_intervals[local]:
  expr_type arr_e = ArrayT et bd /\ (bd = Fixed c \/ bd = Dynamic c) /\
  compile_expr cenv (ArrayT et bd) arr_e se = (vv,sm) /\
  vv_location vv = SOME LocMemory /\ cenv.ce_alloca_locals /\
  compile_stmt cenv lctx ty (For id et (Array arr_e) n stmts) se = ((),sf) /\
  (!bc lc sa sb. compile_stmts bc lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb) /\ fn_has_code se sf func ==>
  fn_has_code se sm func /\ fn_has_code sm sf func
Proof
  strip_tac >>
  `cs_extends sm sf` by
    (irule compile_for_mem_suffix_extends >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule (cj 1 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  irule fragExecTheory.fn_has_code_split >> goal_assum (drule_at Any) >> simp[]
QED

(* The snapshot is well formed only in the successful array-type branch. *)
Theorem mem_iter_snapshot_wf[local]:
  expr_type e = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  vv_post ctx func cenv cx e es sa sb s0 es1 rv vv s1 /\
  vv_location vv = SOME LocMemory /\
  read_result cx rv es1 = (INL v, es1) ==>
  val_wf (ArrayTV tv bd) v
Proof
  Cases_on `vv` >> simp[contextTheory.vv_location_def] >> strip_tac >>
  gvs[vv_post_def, vv_at_def] >> metis_tac[]
QED

Theorem mem_iter_array_type_value[local]:
  evaluate_type tenv et = SOME tv /\
  evaluate_type tenv (ArrayT et bd) = SOME atv ==>
  atv = ArrayTV tv bd
Proof
  simp[vyperValueTheory.evaluate_type_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem mem_iter_snapshot_shape[local]:
  val_wf (ArrayTV tv bd) v /\
  extract_elements (ArrayTV tv bd) v = SOME vs ==>
  (!c. bd = Fixed c ==> ?kvs. v = ArrayV (SArrayV kvs)) /\
  (!c. bd = Dynamic c ==> ?vs. v = ArrayV (DynArrayV vs))
Proof
  Cases_on `v` >>
  simp[vyperValueOperationTheory.extract_elements_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  Cases_on `bd` >> simp[val_wf_def]
QED

Theorem mem_iter_snapshot_length[local]:
  val_wf (ArrayTV tv bd) v /\
  extract_elements (ArrayTV tv bd) v = SOME vs ==>
  (!c. bd = Fixed c ==> LENGTH vs = c) /\
  (!c. bd = Dynamic c ==> LENGTH vs <= c)
Proof
  Cases_on `v` >>
  simp[vyperValueOperationTheory.extract_elements_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  simp[val_wf_def, vyperValueOperationTheory.array_elements_def] >>
  Cases_on `bd` >> simp[] >> rpt strip_tac >> gvs[]
QED

(* Normalize only the source prefix, retaining expression effects. *)
Theorem mem_for_source_bind[local]:
  evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_stmt cx (For id et (Array e) n stmts) =
  bind (eval_expr cx e) (\rv. do
    v <- read_result cx rv;
    at <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e)) "For array type";
    vs <- lift_option_type (extract_elements at v) "For not ArrayV";
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
    eval_for cx tv id stmts vs od)
Proof
  strip_tac >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def, bind_return] >>
  simp[Once evaluate_def, bind_assoc, bind_return,
       lift_option_type_def, lift_option_def]
QED

Theorem mem_for_expr_admissible[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\
  gas_admissible (eval_stmt cx (For id et (Array e) n stmts))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >>
  drule mem_for_source_bind >> disch_then (fn th => fs[th]) >>
  simp[gasContextTheory.gas_admissible_def] >>
  map_every qx_gen_tac [`gs`, `res`, `ee`] >> strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `res`
  >- (rename1 `eval_expr cx e _ = (INL rv,ee)` >>
      Cases_on `rv` >> simp[expr_vv_res_ok_def] >>
      simp[bind_def, read_result_def, raise_def, stmt_res_ok_def]) >>
  simp[bind_def] >> strip_tac >>
  fs[stmt_res_ok_def, expr_vv_res_ok_def] >>
  drule (cj 1 vyperExprNoControlTheory.eval_expr_no_control) >>
  simp[vyperExprNoControlTheory.no_control_exc_def] >> gvs[]
QED

Theorem mem_for_continuation_admissible[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\
  gas_admissible (eval_stmt cx (For id et (Array e) n stmts)) ok es /\
  (!tail. eval_expr cx e (es with gas_obs := xs ++ tail) =
     (INL rv, mid with gas_obs := tail)) ==>
  gas_admissible
    (do v <- read_result cx rv;
        at <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e)) "For array type";
        vs <- lift_option_type (extract_elements at v) "For not ArrayV";
        check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
        eval_for cx tv id stmts vs od) ok (mid with gas_obs := [])
Proof
  strip_tac >>
  drule mem_for_source_bind >> disch_then (fn th => fs[th]) >>
  drule stmtSimForRoundsTheory.gas_admissible_bind_tail >>
  disch_then drule >> simp[]
QED

Theorem mem_for_continuation_outcome[local]:
  read_result cx rv es = (INL v,es) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME at /\
  extract_elements at v = SOME vs /\ LENGTH vs <= n /\ ~s.vs_halted /\
  gas_outcome F tops (ctx,func) (eval_for cx tv id stmts vs)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome F tops (ctx,func)
    (do xs <- (do v <- read_result cx rv;
                  at <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                          "For array type";
                  vs <- lift_option_type (extract_elements at v) "For not ArrayV";
                  return vs od);
        check (compatible_bound (Dynamic n) (LENGTH xs)) "For too long";
        eval_for cx tv id stmts xs od) (es,s) Q R
Proof
  strip_tac >>
  `!msg. assert T msg = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  irule stmtSimForArrayFragTheory.array_values_prefix_outcome >>
  drule exprSimMemorySourceTheory.read_result_gas_obs >> strip_tac >>
  simp[bind_def, lift_option_type_def, lift_option_def, return_def,
       vyperValueTheory.compatible_bound_def, check_def, vyperStateTheory.assert_def] >>
  simp[ignore_bind_def, bind_return]
QED

(* A successful iterable read cannot reach the array type error in an
   admissible source For execution. *)
Theorem mem_iter_array_type_success[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\
  gas_admissible (eval_stmt cx (For id et (Array e) n stmts))
    (stmt_res_ok lctx) es /\
  eval_expr cx e (es with gas_obs := gs) = (INL rv, es1) /\
  read_result cx rv es1 = (INL v, es1) ==>
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e))
Proof
  strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)` >> simp[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >>
  qexists_tac `gs` >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def,
       bind_def, return_def, raise_def, stmt_res_ok_def] >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def,
       bind_def, return_def, raise_def]
QED

(* The For case over a memory-valued iterable, fixed or dynamic.  The hook
   (the last premise) is asked of every end of the iterable's fragment: the
   pointer w lies inside an allocation (aid, b, z) made before the loop,
   the elements vs of the value v the source read sit at w, and the body,
   at every element, keeps a predicate Q that puts them there and that
   survives the loop's own code (keep_stable).  P is the source-side loop
   invariant, as in compile_for_dynarray_frag. *)
Theorem compile_for_mem_frag:
  !ctx func cx cenv lctx RetQ ty id et bd c n arr_e stmts tv es Qe.
  expr_type arr_e = ArrayT et bd /\ (bd = Fixed c \/ bd = Dynamic c) /\
  c <= n /\ c < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  (!st. vv_location (FST (compile_expr cenv (ArrayT et bd) arr_e st)) =
          SOME LocMemory) /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  expr_vv_sim_with Qe ctx func cenv cx (ArrayT et bd) arr_e es /\
  (!sa sb s0 es1 rv vv s1.
     compile_expr cenv (ArrayT et bd) arr_e sa = (vv, sb) /\
     vv_post ctx func cenv cx arr_e es sa sb s0 es1 rv vv s1 /\
     Qe sa sb s0 es1 rv vv s1 ==>
     ?v vs w aid b z Q P.
       read_result cx rv es1 = (INL v, es1) /\
       extract_elements (ArrayTV tv bd) v = SOME vs /\
       eval_operand (vv_operand vv) s1 = SOME w /\
       FLOOKUP s1.vs_allocas aid = SOME (b, z) /\ aid < sb.cs_next_id /\
       b <= w2n w /\ w2n w + type_memory_size (ArrayTV tv bd) <= b + z /\
       b + z < dimword (:256) /\
       Q s1 /\ keep_stable Q sb b z /\
       (!s. Q s ==> val_in_memory (ArrayTV tv bd) v (w2n w) s.vs_memory) /\
       P es1 /\ lookup_scopes id es1.scopes = NONE /\
       (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
       (!st0 bc sd ex inc ei k.
          declare_local cenv id et st0 = (bc,sd) /\
          P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
          stmt_frag_keep Q ctx func cx (InLoop ex inc) RetQ bc
            (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
            (ei with scopes :=
              (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                                popped := []|>)) :: ei.scopes)) /\
       (!ei k gs r es2.
          P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
          eval_stmts cx stmts (ei with <| scopes :=
            (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                              popped := []|>)) :: ei.scopes; gas_obs := gs |>) =
            (r,es2) ==>
          (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
          ?sc rest. es2.scopes = sc :: rest /\
            (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
            ((r = INL () \/ r = INR ContinueException) ==>
              P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (For id et (Array arr_e) n stmts))
    (eval_stmt cx (For id et (Array arr_e) n stmts)) es
Proof
  cheat
QED

(* Source side for a place iterable: a body that writes nothing containing
   the place p (iterator_unmodified) keeps, at every scope, the root
   local's type and its sub-value at p's attribute path (the path up to
   p's first subscript, place_access).  The iterable is an array, so a
   well-typed target can't extend that path by another attribute before a
   subscript, which place_contains wouldn't see.
   typed_stmts_projection_frame is the case of an empty attribute path,
   where the whole root is kept. *)
Theorem typed_stmts_place_frame:
  supported_stmts tops bindings stmts /\
  type_stmts env ret_ty stmts = SOME env' /\
  well_typed_expr env arr_e /\ expr_type arr_e = ArrayT et bd /\
  expr_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
  root IN FDOM env.var_types /\
  stmts_writes_ok (\w. ~place_contains w p) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
  LENGTH es'.scopes = LENGTH es.scopes /\
  MAP (\sc. OPTION_MAP
          (\e. (e.type, evaluate_subscripts e.type e.value
                           (MAP AttrSubscript attrs)))
          (FLOOKUP sc root)) es'.scopes =
  MAP (\sc. OPTION_MAP
          (\e. (e.type, evaluate_subscripts e.type e.value
                           (MAP AttrSubscript attrs)))
          (FLOOKUP sc root)) es.scopes
Proof
  cheat
QED

(* Hook for a temporary buffer: a body that keeps the bytes of the
   buffer's allocation keeps the iterable's value in it.  The hypothesis
   is what stmt_post's frame on the memory of allocations made before the
   fragment and holding no local (the S1 interface piece on stmt_post)
   gives every body. *)
Theorem for_keep_temp:
  !ctx func cx lctx RetQ cenv m source es atv v w b z cs.
    (!bs. stmt_frag_keep (\s. mem_bytes_at b z s.vs_memory = bs)
            ctx func cx lctx RetQ cenv m source es) /\
    val_wf atv v /\ b <= w /\ w + type_memory_size atv <= b + z ==>
    stmt_frag_keep (\s. val_in_memory atv v w s.vs_memory)
      ctx func cx lctx RetQ cenv m source es /\
    keep_stable (\s. val_in_memory atv v w s.vs_memory) cs b z
Proof
  rpt gen_tac >> strip_tac >>
  `!m1 m2. mem_bytes_at b z m2 = mem_bytes_at b z m1 /\
           val_in_memory atv v w m1 ==> val_in_memory atv v w m2` by
    (rpt strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
     qexistsl_tac [`type_memory_size atv`, `m1`] >> simp[] >>
     drule (cj 1 mem_bytes_at_agree_window) >> disch_then irule >> simp[]) >>
  conj_tac >~ [`keep_stable`] >- (simp[keep_stable_def] >> metis_tac[]) >>
  simp[stmt_frag_keep_def] >>
  map_every qx_gen_tac [`sa`, `sb`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `!bs. stmt_frag_keep _ _ _ _ _ _ _ _ _ _`
    (qspec_then `mem_bytes_at b z s0.vs_memory` mp_tac) >>
  simp[stmt_frag_keep_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >> simp[] >>
  strip_tac >> irule gas_outcome_conseq >> first_assum (irule_at Any) >>
  simp[] >> metis_tac[]
QED

(* A projection of one name's entries that two scope lists agree on
   gives the same projection of its lookup. *)
Theorem scope_projection_lookup_map[local]:
  !a b n f.
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) a =
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) b ==>
    OPTION_MAP f (lookup_scopes n a) = OPTION_MAP f (lookup_scopes n b)
Proof
  Induct >- (Cases >> simp[lookup_scopes_def]) >>
  rpt gen_tac >> Cases_on `b` >> simp[lookup_scopes_def] >> strip_tac >>
  Cases_on `FLOOKUP h n` >> Cases_on `FLOOKUP h' n` >> gvs[]
QED

(* The same, for a name bound below the top scope. *)
Theorem scope_projection_lookup_below[local]:
  !a sc0 rest0 n f e.
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) a =
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) (sc0 :: rest0) /\
    n NOTIN FDOM sc0 /\ lookup_scopes n rest0 = SOME e ==>
    ?sc rest e'. a = sc :: rest /\ lookup_scopes n rest = SOME e' /\
      lookup_scopes n a = SOME e' /\ f e' = f e
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >> gvs[] >>
  `FLOOKUP sc0 n = NONE` by gvs[flookup_thm] >>
  `FLOOKUP h n = NONE` by gvs[] >>
  drule scope_projection_lookup_map >> simp[] >>
  Cases_on `lookup_scopes n t` >> simp[lookup_scopes_def]
QED

(* A path read that succeeds reads its prefix. *)
Theorem evaluate_subscripts_append_prefix[local]:
  !p tv a sfx r.
    evaluate_subscripts tv a (p ++ sfx) = INL r ==>
    ?x. evaluate_subscripts tv a p = INL x
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >>
      metis_tac[]) >>
  Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >> metis_tac[]
QED

(* Two values with the same sub-value at a path read the same below it:
   the types a read passes through depend on the path alone. *)
Theorem sum_case_id[local]:
  !X. (case X of INL vj => INL vj | INR err => INR err) = X
Proof
  Cases >> simp[]
QED

Theorem evaluate_subscripts_prefix_agree[local]:
  !p tv a b sfx x.
    evaluate_subscripts tv a p = INL x /\
    evaluate_subscripts tv b p = INL x ==>
    evaluate_subscripts tv a (p ++ sfx) = evaluate_subscripts tv b (p ++ sfx)
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def] >>
      Cases_on `b` >> simp[evaluate_subscripts_def, sum_case_id] >>
      rpt strip_tac >>
      Cases_on `array_index tv a i` >> Cases_on `array_index tv a' i` >>
      gvs[] >> metis_tac[]) >>
  Cases_on `a` >> simp[evaluate_subscripts_def] >>
  Cases_on `b` >> simp[evaluate_subscripts_def, sum_case_id] >>
  rpt strip_tac >> BasicProvers.EVERY_CASE_TAC >> gvs[] >> metis_tac[]
QED

(* Hook for a place inside a local: the iterable's pointer is the place's,
   the root local's pointer bw (in its variable q) plus the byte offset k
   of the place's path in the root's type tv0 (the vv_place_ptr clause of
   the S1 interface piece on vv_post), and the body writes nothing
   containing the place.  Then the body keeps q and the value v the place
   held at entry.

   The root is bound below the body's top scope (the loop variable's), and
   its value is well typed after every run of the body (the caller's
   state_well_typed).

   v is read from the root's value (evaluate_subscripts), not through
   read_memory_path's fallback to popped history: memory keeps only a
   local's value (local_ptrs_rel), so a body's stmt_frag says nothing of
   a popped element's bytes.  The checker gives the premise: it rejects a
   pop at any depth of a For iterable (expr_writes_ok (\_. F) in
   well_typed_iterator, the checker piece), and with no pop the place
   reads the value. *)
Theorem for_keep_place:
  !ctx func cx ex inc RetQ bc ty stmts ei tops bindings env ret_ty env' arr_e
   et bd p root attrs rest sc0 rest0 entry v q z bw tv0 k atv.
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts) ei /\
    supported_stmts tops bindings stmts /\
    type_stmts env ret_ty stmts = SOME env' /\
    well_typed_expr env arr_e /\ expr_type arr_e = ArrayT et bd /\
    expr_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
    root IN FDOM env.var_types /\
    stmts_writes_ok (\w. ~place_contains w p) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    ei.scopes = sc0 :: rest0 /\ root NOTIN FDOM sc0 /\
    lookup_scopes root rest0 = SOME entry /\ entry.type = tv0 /\
    well_formed_type_value tv0 /\
    evaluate_subscripts tv0 entry.value (MAP AttrSubscript attrs ++ rest) =
      INL v /\
    FLOOKUP bc.ce_vars root = SOME (PtrVar (Var q) z) /\
    mem_path_offset tv0 (MAP AttrSubscript attrs ++ rest) = SOME (k, atv) /\
    (!gs res ee e.
       eval_stmts cx stmts (ei with gas_obs := gs) = (res, ee) /\
       lookup_scopes root ee.scopes = SOME e ==>
       value_has_type e.type e.value) ==>
    stmt_frag_keep
      (\s. lookup_var q s = SOME bw /\
           val_in_memory atv v (w2n bw + k) s.vs_memory)
      ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts) ei
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_keep_def] >>
  map_every qx_gen_tac [`sa`, `sb`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def, gas_marked_exec_def] >>
  strip_tac >> qexists_tac `marks`
  >| [
      disj1_tac >> qexistsl_tac [`res`, `es_end`, `r`] >> gvs[] >>
      qabbrev_tac `gs = gas_explicit marks s0.vs_gas_readings` >>
      qabbrev_tac `ee = es_end with gas_obs := []` >>
      `eval_stmts cx stmts (ei with gas_obs := gs) = (res,ee)` by
        (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
         simp[Abbr `ee`]) >>
      qpat_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE std_ss [stmt_post_def]) >>
      `not_fresh_at sa q` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var q t = SOME bw` by metis_tac[] >>
      simp[] >>
      mp_tac (Q.INST [`es` |-> `ei with gas_obs := gs`, `es'` |-> `ee`]
      typed_stmts_place_frame) >>
      impl_tac >- simp[] >> strip_tac >>
      qmatch_asmsub_abbrev_tac `MAP (\sc. OPTION_MAP f (FLOOKUP sc root))` >>
      `?sc rest' e'. ee.scopes = sc :: rest' /\ lookup_scopes root rest' = SOME e' /\
      lookup_scopes root ee.scopes = SOME e' /\ f e' = f entry` by
      (irule scope_projection_lookup_below >> gvs[] >> metis_tac[]) >>
      fs[Abbr `f`] >>
      `FLOOKUP cenv''.ce_vars root = SOME (PtrVar (Var q) z)` by
      (qpat_x_assum `cenv_top_ext _ _ _` mp_tac >>
      simp[cenv_top_ext_def] >> strip_tac >>
      first_x_assum (qspec_then `root` mp_tac) >> CCONTR_TAC >> gvs[]) >>
      `local_ptrs_rel func cenv'' ee.scopes t` by
      gvs[stmt_state_rel_def, state_rel_def] >>
      pop_assum mp_tac >> simp[local_ptrs_rel_def] >>
      disch_then (qspecl_then [`root`, `e'`, `q`, `z`] mp_tac o CONJUNCT1) >>
      simp[] >> strip_tac >> gvs[] >>
      `value_has_type entry.type e'.value` by metis_tac[] >>
      drule evaluate_subscripts_append_prefix >> strip_tac >>
      `evaluate_subscripts entry.type e'.value (MAP AttrSubscript attrs ++ rest) =
        INL v` by
      metis_tac[evaluate_subscripts_prefix_agree] >>
      disj1_tac >> once_rewrite_tac[ADD_COMM] >>
      irule imm_typed_path_memory >> metis_tac[],
      disj1_tac >> qexistsl_tac [`res`, `es_end`, `r`] >> simp[],
      disj2_tac >> metis_tac[]]
QED
