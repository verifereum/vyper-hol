Theory bodyFullExtCallDelayedSlot
Ancestors
  bodyFullAttributeAdd bodyPtrMakeArrayEmission assignBasePtrOffset
  exprLoweringProps bodyPtrDefs loweringStateRelDefs
  fragExec allocaHistory venomState ptrDiscipline words finite_map
  venomInst venomExecSemantics emitHelper compileEnv
  bodyFullExtCallSlotCopyReplay bodyFullExtCallRuntimeCopyReplay
  bodyFullExtCallCtorCopyReplay fragGasOriginPtrDead
  loweringPosts exprSimMemDefs vyperValue vyperStorageFootprint
  exprLowering exprSimWordArgs fragGasOriginPtr vyperState
  stateRelProj exprSimVVFrame bodyFullExtCallSavedOperand
Libs pureFrameLib

(* The slot address is computed before the saved argument is unwrapped. *)
Theorem extcall_slot_address[local]:
  emit_op ADD [Var root; Lit (n2w off)] sa = (dst,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  not_fresh_at sa root /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s capacity /\ off + n <= capacity /\
  w2n bw + off < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p t G' tn'.
    dst = Var p /\ p = STRING #"%" (toString sa.cs_next_var) /\
    t = (update_var p (bw + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    not_fresh_at sb p /\ ptr_covers G' tn' p t n /\
    lookup_var p t = SOME (n2w (w2n bw + off)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!x. x <> p ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (alloca_history fn s /\ venomMemDefs$alloca_inv s ==> alloca_history fn t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME bw` by simp[eval_operand_def] >>
  `op_taint tn (Var root) = {} /\ ?b cap. FLOOKUP G root = SOME (b,cap)` by
    fs[ptr_covers_def] >>
  drule_all emit_op_fetch_boundary >>
  disch_then (qx_choose_then `p` (qx_choose_then `bb` strip_assume_tac)) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [p]` >>
  qabbrev_tac `u = update_var p (bw + n2w off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  `(!D lo explicit. allocas_from lo s ==>
       gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
   FLOOKUP G' p = FLOOKUP G root /\ op_taint tn' (Var p) = {} /\
   tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!x. x <> p ==> FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x))` by
    (rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all attribute_add_full_frame >> simp[op_prov_def]) >>
  `lookup_var p t = SOME (bw + n2w off)` by
    simp[Abbr `t`, Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers G' tn' p t n` by
    (irule assign_base_ptr_covers_offset_address >> metis_tac[]) >>
  `alloca_history fn s /\ venomMemDefs$alloca_inv s ==> alloca_history fn t` by
    (strip_tac >>
     `step_inst_base i s = OK u` by
       simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
            exec_pure2_def, eval_operand_def] >>
     `get_instruction bb s.vs_inst_idx = SOME i` by fs[Abbr `i`] >>
     drule_all alloca_history_base_step >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, Abbr `t`]) >>
  qexistsl [`p`,`t`,`G'`,`tn'`] >>
  simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       GSYM word_add_n2w] >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
  strip_tac >> gvs[]
QED

(* The delayed read is code-free for a saved word or memory aggregate. *)
Theorem extcall_slot_identity_unwrap[local]:
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\
        p.ptr_location = LocMemory)) /\
  unwrap_value ce saved sa = (src,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx ty raw saved ee s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_store_bound cx ty ty ee raw saved s /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ val_wf rt v ==>
  src = vv_operand saved /\ sb = sa /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s /\
  (~is_word_type ty ==>
   !w. eval_operand src s = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next)
Proof
  strip_tac >>
  `val_store_size rt v <= type_memory_size rt` by simp[exprSimPropsTheory.val_store_size_le] >>
  gvs[vv_holds_def, unwrap_value_def, comp_return_def, contextTheory.vv_operand_def,
      expr_val_rel_def, ptr_vv_ok_def, ptr_val_ok_def,
      vv_store_bound_def, expr_store_bound_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_assum (qspec_then `w` mp_tac) >> simp[]) >> decide_tac
QED

(* A retained nonmemory VV still reads the saved value.  Rebase its VV
   post at the current endpoint, without re-evaluating the expression. *)
Theorem extcall_slot_nonmemory_rebase[local]:
  p.ptr_location <> LocMemory /\
  post_value_type ce e = expr_type e /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee t /\
  vv_storage_live H cx (LocatedValue (expr_type e) p) ee t /\
  stmt_state_rel H ctx fn ce cx ee t /\
  storage_well_formed_on cx ee (FST H) ==>
  vv_post H ctx fn ce cx e ee si sm t ee (Value v)
    (LocatedValue (expr_type e) p) t
Proof
  strip_tac >> simp[vv_post_def, vv_at_def] >>
  Cases_on `p.ptr_location` >>
  gvs[vv_holds_def, storage_holds_def, immutable_holds_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

(* A supplier has the existing physical-copy contract and adds P at that
   very same normal endpoint.  Form the signatures from the pure replay
   contracts so the frame and horizon clauses are kept single-sourced. *)
local
  fun with_side th =
    let
      val (pre, post) = boolSyntax.dest_imp (concl (SPEC_ALL th))
      val (ws, body) = boolSyntax.strip_exists post
      fun arg name = List.find (fn v => #1 (dest_var v) = name) (free_vars pre)
      val pred = ``P:compile_state -> compile_state -> venom_state -> venom_state -> bool``
      val side = list_mk_comb (pred, List.map (valOf o arg) ["su", "sb", "t"] @ [hd ws])
      val result = boolSyntax.mk_imp (pre,
        boolSyntax.list_mk_exists (ws, boolSyntax.mk_conj (side, body)))
      val fixed = pred :: List.map (valOf o arg) ["ctx", "fn", "su", "sb"] @
        List.filter (fn v => #1 (dest_var v) = "explicit") (free_vars result)
    in boolSyntax.list_mk_forall
         (List.filter (fn v => not (List.exists (aconv v) fixed)) (free_vars result), result)
    end
in
  val slot_copy_side = with_side extcall_saved_slot_copy_replay_pure
  val runtime_copy_side = with_side extcall_saved_runtime_copy_replay_pure
  val ctor_copy_side = with_side extcall_saved_ctor_copy_replay_pure
end

Definition saved_restore_copy_laws_def:
  saved_restore_copy_laws ctx fn explicit su sb P <=> ^slot_copy_side /\ ^runtime_copy_side /\ ^ctor_copy_side
End

Theorem saved_restore_copy_laws_true:
  saved_restore_copy_laws ctx fn explicit su sb (\a b u z. T)
Proof
  simp_tac bool_ss [saved_restore_copy_laws_def] >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC extcall_saved_slot_copy_replay_pure) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC extcall_saved_runtime_copy_replay_pure) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC extcall_saved_ctor_copy_replay_pure
QED

Theorem extcall_slot_nonmemory_unwrap_from_side[local]:
  saved_restore_copy_laws ctx fn explicit su sb P /\
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ p.ptr_location <> LocMemory /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee t /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx (LocatedValue (expr_type e) p) ee t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (ce.ce_is_ctor /\ p.ptr_location = LocCode ==>
    !w. eval_operand p.ptr_operand t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    P su sb t z /\
    pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx (expr_type e) v src z /\ ptr_val_ok cx (expr_type e) v src G' tn' z /\
    expr_store_bound cx (expr_type e) v src z /\ ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    expr_val_at ce cx (expr_type e) su sb ee v src z
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t` by
    gvs[ptr_vv_ok_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx fn ce cx e ee si sm t ee (Value v) (LocatedValue (expr_type e) p) t /\
     ghost_inv_at (DF H) lo d ce cx ee G tn t` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
     TRY (first_assum ACCEPT_TAC) >>
     irule extcall_slot_nonmemory_rebase >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
      impl_tac >- fs[storage_trace_domain_def] >>
      simp[exprSimUnwrapTheory.vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `ce.ce_is_ctor`
      >- (qpat_x_assum `saved_restore_copy_laws ctx fn explicit su sb P`
            (irule o cj 3 o REWRITE_RULE [saved_restore_copy_laws_def]) >>
          simp[] >> qexistsl [`p`,`si`,`sm`] >> fs[]) >>
      qpat_x_assum `saved_restore_copy_laws ctx fn explicit su sb P`
        (irule o cj 2 o REWRITE_RULE [saved_restore_copy_laws_def]) >>
      simp[] >> qexistsl [`p`,`si`,`sm`] >> simp[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  qpat_x_assum `saved_restore_copy_laws ctx fn explicit su sb P`
    (irule o cj 1 o REWRITE_RULE [saved_restore_copy_laws_def]) >>
  simp[] >> qexistsl [`p`,`si`,`sm`] >> simp[]
QED

(* At the ADD cut, only the fresh output variable and instruction index
   change. Keep the exact equality private to this cut. *)
Theorem extcall_slot_add_transport[local]:
  t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s with
         vs_inst_idx := k) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. x <> STRING #"%" (toString sa.cs_next_var) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm ==>
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s /\ op_prov G1 op = op_prov G op /\
    op_taint tn1 op = op_taint tn op) /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\
  (!H. stmt_state_rel H ctx fn ce cx ee s ==> stmt_state_rel H ctx fn ce cx ee t) /\
  (!D. ghost_inv_at D lo d ce cx ee G tn s ==> ghost_inv_at D lo d ce cx ee G1 tn1 t) /\
  wb_frame ce ee ee sa s t /\ ghost_kept_at lo ce ee sa G tn s G1 tn1
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> fs[not_fresh_at_def]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s /\ op_prov G1 op = op_prov G op /\
    op_taint tn1 op = op_taint tn op` by
    (Cases >> simp[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s /\
   t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_transient = s.vs_transient` by
    simp[update_var_def, contract_storage_def, contract_transient_def] >>
  simp[] >> conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> rpt strip_tac >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      irule (cj 1 attribute_fresh_full_ghost_update) >>
      conj_tac >- (qexists_tac `sa` >> simp[]) >>
      qexistsl [`G`,`tn`] >> simp[] >> metis_tac[]) >>
  gvs[wb_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, ghost_kept_at_def] >>
  irule exprSimPropsTheory.locals_kept_regions >> simp[]
QED

(* A saved operand's read and pointer facts depend on its own operand,
   not on the fresh destination computed by the ADD. *)
Theorem extcall_slot_vv_transport[local]:
  vv_holds ce cx ty raw saved ee s /\ ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_store_bound cx et ty ee raw saved s /\
  eval_operand (vv_operand saved) t = eval_operand (vv_operand saved) s /\
  op_taint tn1 (vv_operand saved) = op_taint tn (vv_operand saved) /\
  op_prov G1 (vv_operand saved) = op_prov G (vv_operand saved) /\
  (!x. vv_operand saved = Var x ==> FLOOKUP G1 x = FLOOKUP G x) /\
  t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
  contract_storage t = contract_storage s /\ contract_transient t = contract_transient s /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\ tn1.t_mem = tn.t_mem /\
  tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans ==>
  vv_holds ce cx ty raw saved ee t /\ ptr_vv_ok cx ty raw saved ee G1 tn1 t /\
  vv_store_bound cx et ty ee raw saved t /\
  (!H. vv_storage_live H cx saved ee s ==> vv_storage_live H cx saved ee t)
Proof
  strip_tac >> conj_tac
  >- metis_tac[vv_holds_vars_frame] >>
  reverse conj_tac
  >- (conj_tac >- (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >> simp[]) >>
      Cases_on `saved` >> gvs[contextTheory.vv_operand_def]) >>
  Cases_on `saved` >>
  gvs[contextTheory.vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def] >>
  metis_tac[]
QED

(* The unwrap returns a store input at a single physical endpoint.  The
   retained interval [si,sm) is used only for a non-memory saved value. *)
Theorem extcall_slot_unwrap_from_side:
  saved_restore_copy_laws ctx fn explicit su sb P /\
  (!a u. ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==> P a a u u) /\
  ty = lowered_value_type ce e /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ compile_expr ce (expr_type e) e si = (saved,sm) /\
        (!x. p.ptr_operand = Var x ==> not_fresh_at sm x))) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  unwrap_value ce saved su = (src,sb) /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\ vv_holds ce cx ty raw saved ee t /\
  ptr_vv_ok cx ty raw saved ee G tn t /\
  vv_store_bound cx ty ty ee raw saved t /\
  ((case saved of
     StackValue tag op0 => ~is_word_type ty
   | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G t) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee t /\ ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?z G' tn'.
    P su sb t z /\
    pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G' tn' z /\
    expr_store_bound cx ty v src z /\ (~is_word_type ty ==> ptr_buf_ok ce e src G' z) /\
    (~is_word_type ty ==> !w. eval_operand src z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    (!p. saved = LocatedValue ty p /\ p.ptr_location <> LocMemory ==>
      expr_val_at ce cx ty su sb ee v src z) /\
    ((?tag op0. saved = StackValue tag op0) \/
     (?p. saved = LocatedValue ty p /\ p.ptr_location = LocMemory) ==>
      z = t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `val_wf rt v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  Cases_on `(?tag op0. saved = StackValue tag op0) \/
    (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)`
  >- (drule_all extcall_slot_identity_unwrap >> strip_tac >>
      qexistsl [`t`,`G`,`tn`] >>
      gvs[wb_frame_refl, ghost_kept_at_def, cj 1 gas_origin_ptr_path_rules]) >>
  `?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
       ty = expr_type e /\ compile_expr ce (expr_type e) e si = (saved,sm) /\
       (!x. p.ptr_operand = Var x ==> not_fresh_at sm x)` by metis_tac[] >>
  `ty = expr_type e` by metis_tac[] >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
   local_ptrs_reserved ce sm` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends, local_ptrs_reserved_next_var] >>
  qpat_x_assum `saved = LocatedValue ty p` SUBST_ALL_TAC >>
  qpat_x_assum `ty = expr_type e` SUBST_ALL_TAC >>
  qpat_x_assum `expr_type e = lowered_value_type ce e` (assume_tac o SYM) >>
  simp[] >>
  irule (SIMP_RULE (boss_ss()) [] extcall_slot_nonmemory_unwrap_from_side) >>
  `type_memory_size rt < 18446744073709551616` by fs[] >>
  simp[] >> qexistsl [`p`,`raw`,`si`,`sm`] >>
  fs[contextTheory.vv_operand_def, contextTheory.vv_location_def]
QED

local
  val unobserved = PURE_REWRITE_RULE
    [saved_restore_copy_laws_true, boolTheory.AND_CLAUSES,
     boolTheory.IMP_CLAUSES, boolTheory.FORALL_SIMP]
    (BETA_RULE (Q.INST [`P` |-> `\a b u z. T`] extcall_slot_unwrap_from_side))
in
Theorem extcall_slot_unwrap_pure:
  ^(concl unobserved)
Proof
  ACCEPT_TAC unobserved
QED
end

Theorem extcall_slot_unwrap =
  pureFrameLib.drop_frame extcall_slot_unwrap_pure

(* Use the actual saved snapshot to protect the read operand from the ADD.
   The two physical endpoints do not depend on the storage horizon. *)
Theorem extcall_slot_horizon_transport[local]:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!(H : (bool # 256 word # type_value) list # num list).
    stmt_state_rel H ctx fn ce cx ee s ==> stmt_state_rel H ctx fn ce cx ee t) /\
  (!(H : (bool # 256 word # type_value) list # num list).
    vv_storage_live H cx saved ee s ==> vv_storage_live H cx saved ee t) /\
  (!D. ghost_inv_at D lo d ce cx ee G tn s ==> ghost_inv_at D lo d ce cx ee G1 tn1 t) ==>
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee t /\ ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t
Proof
  metis_tac[]
QED

(* Both the horizon post and the unrestricted path use the same exit. *)
Theorem extcall_saved_slot_prepare_all_dead:
  emit_op ADD [Var root; Lit (n2w off)] sa = (dst,su) /\
  unwrap_value ce saved su = (src,sb) /\
  fn_has_code sa su fn /\ fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  not_fresh_at sa root /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s capacity /\ off + n <= capacity /\
  w2n bw + off < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  sm.cs_next_var <= sa.cs_next_var /\ sm.cs_next_id <= sa.cs_next_id /\
  ss.cs_next_var <= sa.cs_next_var /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\ vv_holds ce cx ty raw saved ee s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of
     StackValue tag op0 => ~is_word_type ty
   | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) ==>
  ?p z G2 tn2.
    dst = Var p /\ not_fresh_at sb p /\
    lookup_var p z = SOME (n2w (w2n bw + off)) /\ ptr_covers G2 tn2 p z n /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,G2,tn2) /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G2 tn2 z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G2 tn2 z /\
    expr_store_bound cx ty v src z /\ (~is_word_type ty ==> ptr_buf_ok ce e src G2 z) /\
    (~is_word_type ty ==> !w. eval_operand src z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==>
       lookup_var x z = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee sa s z /\ ghost_kept_at lo ce ee sa G tn s G2 tn2 /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,G2,tn2))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `si.cs_next_var <= sm.cs_next_var` by
    (drule exprSimUnwrapTheory.compile_expr_extends >> simp[]) >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `su.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`ce`,`saved`,`su`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `si.cs_next_var <= sa.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce sa` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. vv_operand saved = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `ss` >> simp[] >>
     irule extcall_saved_operand_not_fresh >>
     qexistsl [`ce`,`copy`,`e`,`expr_type e`,`saved`,`si`,`sm`,`ty`,`vv`] >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx fn ce cx ee s` by
    (first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `venomMemDefs$alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  drule_all extcall_slot_address >>
  disch_then (qspec_then `PG` (qx_choose_then `p` (qx_choose_then `t`
    (qx_choose_then `G1` (qx_choose_then `tn1`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `t = (update_var (STRING #"%" (toString sa.cs_next_var)) (bw + n2w off) s with
         vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  `!x. x <> STRING #"%" (toString sa.cs_next_var) ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  drule_all (Q.INST_TYPE [`:'a` |-> `:256`] extcall_slot_add_transport) >>
  disch_then (qspecl_then [`lo`,`fn`,`ee`,`d`,`cx`,`ctx`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `eval_operand (vv_operand saved) t = eval_operand (vv_operand saved) s /\
   op_prov G1 (vv_operand saved) = op_prov G (vv_operand saved) /\
   op_taint tn1 (vv_operand saved) = op_taint tn (vv_operand saved)` by metis_tac[] >>
  `!x. vv_operand saved = Var x ==> FLOOKUP G1 x = FLOOKUP G x` by metis_tac[] >>
  drule_all (Q.INST_TYPE [`:'a` |-> `:256`] extcall_slot_vv_transport) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  suspend "unwrap"
QED

Resume extcall_saved_slot_prepare_all_dead[unwrap]:
  qpat_x_assum `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    kall_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee t /\ ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t` by
    (MATCH_MP_TAC extcall_slot_horizon_transport >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `(?tag op0. saved = StackValue tag op0) \/
     (?q. saved = LocatedValue ty q /\ ~is_word_type ty /\ q.ptr_location = LocMemory) \/
     (?q. saved = LocatedValue ty q /\ ~is_word_type ty /\ q.ptr_location <> LocMemory /\
          ty = expr_type e /\ compile_expr ce (expr_type e) e si = (saved,sm) /\
          (!x. q.ptr_operand = Var x ==> not_fresh_at sm x))`
   >-
    (qpat_assum `(?tag op0. saved = StackValue tag op0) \/ _`
       (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 assume_tac
          (qx_choose_then `q` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))
     >- simp[]
     >- simp[] >>
     disj2_tac >> disj2_tac >> qexists_tac `q` >>
     qpat_assum `saved = LocatedValue ty q` (SUBST1_TAC) >>
     qpat_assum `!x. vv_operand vv = Var x ==> _` mp_tac >>
     simp[contextTheory.vv_operand_def] >>
     metis_tac[contextTheory.vv_operand_def])) >>
  `sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id` by decide_tac >>
  `alloca_history fn t` by simp[] >>
  `((case saved of StackValue tag op0 => ~is_word_type ty
     | LocatedValue tag q => q.ptr_location = LocMemory) ==>
     ptr_buf_ok ce e (vv_operand saved) G1 t)` by
    (disch_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
     qexistsl [`G`,`s`] >> simp[]) >>
  `(ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
      !w. eval_operand (vv_operand saved) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem))` by
    (simp[] >> metis_tac[]) >>
  drule_all extcall_slot_unwrap >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `z`
    (qx_choose_then `G2` (qx_choose_then `tn2`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x z = _ /\ _`
    (qspec_then `p` (drule_then strip_assume_tac)) >>
  `ptr_covers G2 tn2 p z n` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl [`G1`,`t`,`tn1`] >> simp[]) >>
  `wb_frame ce ee ee sa s z` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx fn ce cx ee s`
       (mp_then Any irule wb_frame_trans) >>
     qpat_assum `wb_frame ce ee ee su t z` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee sa G tn s G2 tn2` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx fn ce cx ee s`
       (mp_then Any irule wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo ce ee su G1 tn1 t G2 tn2` (irule_at Any) >>
     qexists_tac `ee` >> simp[]) >>
  `not_fresh_at sb p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `s.vs_alloca_next <= z.vs_alloca_next` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,G2,tn2)` by
    (qx_gen_tac `D` >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G1,tn1)` by
       (qpat_assum `!D l ex. allocas_from l s ==>
           gas_origin_ptr_path (D,l,ex,ctx,fn,PG) _ _ (OK t,G1,tn1)` irule >> simp[]) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,G1,tn1)`
       (mp_then Any (irule o SRULE []) gas_origin_ptr_path_append) >>
     irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  qexistsl [`p`,`z`,`G2`,`tn2`] >> simp[] >>
  qx_gen_tac `x` >> disch_tac >>
  `not_fresh_at su x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[]
QED

Finalise extcall_saved_slot_prepare_all_dead

Theorem extcall_saved_slot_prepare:
  emit_op ADD [Var root; Lit (n2w off)] sa = (dst,su) /\
  unwrap_value ce saved su = (src,sb) /\
  fn_has_code sa su fn /\ fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  not_fresh_at sa root /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s capacity /\ off + n <= capacity /\
  w2n bw + off < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  sm.cs_next_var <= sa.cs_next_var /\ sm.cs_next_id <= sa.cs_next_id /\
  ss.cs_next_var <= sa.cs_next_var /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\ vv_holds ce cx ty raw saved ee s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of
     StackValue tag op0 => ~is_word_type ty
   | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) ==>
  ?p z G2 tn2.
    dst = Var p /\ not_fresh_at sb p /\
    lookup_var p z = SOME (n2w (w2n bw + off)) /\ ptr_covers G2 tn2 p z n /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,G2,tn2) /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G2 tn2 z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G2 tn2 z /\
    expr_store_bound cx ty v src z /\ (~is_word_type ty ==> ptr_buf_ok ce e src G2 z) /\
    (~is_word_type ty ==> !w. eval_operand src z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==>
       lookup_var x z = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee sa s z /\ ghost_kept_at lo ce ee sa G tn s G2 tn2
Proof
  disch_then (mp_tac o MATCH_MP extcall_saved_slot_prepare_all_dead) >>
  disch_then (qx_choose_then `p` (qx_choose_then `z` (qx_choose_then `G2`
    (qx_choose_then `tn2` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qexistsl [`p`,`z`,`G2`,`tn2`] >> simp[]
QED
