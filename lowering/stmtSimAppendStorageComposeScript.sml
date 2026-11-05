(* Source and code partitions for primitive storage Append composition. *)
Theory stmtSimAppendStorageCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  appendStorageRel stmtSimAppendStorage stmtSimAssignStorage  fragExec
  varsExt freshWrites stateFrame venomState finite_map 
  accountsRelProps vyperStorage vyperStorageBackend vyperValue vfmState
  exprOperandVar stmtSimDecl
  vyperInterpreter vyperState vyperExprNoControl stmtLowering exprLowering
  exprLoweringProps compileEnv emitHelper emitHelperProps venomInst venomExecSemantics
Libs
  monadsyntax

Theorem eval_append_toplevel:
  eval_target_place cx (TopLevelNameTarget nid) es = (INL p,es) /\
  eval_stmt cx (Append (TopLevelNameTarget nid) e) es = (res,es') ==>
  ?r es1.
    (do result <- eval_expr cx e; read_result cx result od) es = (r,es1) /\
    (!ex. r = INR ex ==> res = INR ex /\ es' = es1 /\ no_control_exc ex) /\
    (!v. r = INL v ==> append_place cx p v es1 = (res,es'))
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1,es1)` >>
  Cases_on `r1` >> simp[]
  >- (Cases_on `read_result cx x es1` >>
      rename1 `read_result cx x es1 = (r2,es2)` >>
      Cases_on `r2` >> simp[] >> strip_tac >> gvs[] >>
      drule read_result_no_control >> simp[]) >>
  strip_tac >> gvs[] >> imp_res_tac (cj 1 eval_expr_no_control) >> simp[]
QED

Theorem append_storage_word_code_parts:
  stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e) sa = (c,sf) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 ==>
  c = cenv /\ ?sb op.
    lower_value compile_expr cenv elem e sa = (op,sb) /\
    compile_dynarray_append cenv (Lit slot) op 1 1 elem
      (lowered_value_type cenv e) cap T
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def,
       target_root_type_def, target_root_capacity_def, target_to_expr_def,
       compile_target_base_def, infer_array_location_def] >>
  Cases_on `tr` >>
  simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
       load_opc_for_def, store_opc_for_def] >>
  Cases_on `lower_value compile_expr cenv elem e sa` >>
  rename1 `lower_value _ _ _ _ _ = (op,sb)` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = (u,_)` >>
  Cases_on `u` >> simp[]
QED

Theorem append_storage_word_suffix_structure:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  same_blocks sa sf /\ inst_extends sa sf /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_ext_call_op i.inst_opcode) (emitted_insts sa sf)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC,
                   rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem append_storage_word_code_frame:
  lower_value compile_expr cenv elem e sa = (op,sb) /\
  compile_dynarray_append cenv (Lit slot) op 1 1 elem
    (lowered_value_type cenv e) cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sa sf func ==>
  cs_extends sa sb /\ cs_extends sb sf /\
  fn_has_code sa sb func /\ fn_has_code sb sf func
Proof
  strip_tac >>
  `cs_extends sa sb` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  `cs_extends sb sf` by
    (simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, inst_extends_def]) >>
  metis_tac[fn_has_code_split]
QED

Theorem append_storage_word_run_frag:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop sbase = SOME slot /\ eval_operand vop sbase = SOME w /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot sbase else sload slot sbase) /\ len < cap /\
  ~sbase.vs_call_ctx.cc_static ==>
  frag_exec ctx sa sf (\s. s = sbase)
    (\s. ?u. s = u with vs_inst_idx := LENGTH sf.cs_current_insts /\
      state_frame u = state_frame
       (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w sbase)
        else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w sbase))
       /\ 
      (!x a. not_fresh_at sa x /\ lookup_var x sbase = SOME a ==>
             lookup_var x u = SOME a)) R
Proof
  strip_tac >> drule append_storage_word_suffix_structure >> strip_tac >>
  irule frag_exec_run_inst_seq_drop_fresh >>
  simp_tac bool_ss [] >> reverse conj_tac
  >- fs[same_blocks_def, inst_extends_def] >>
  disj1_tac >>
  `fresh_vars_wrt sa (drop_fresh sa sbase)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa sbase) = SOME slot /\
   eval_operand vop (drop_fresh sa sbase) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  `len = w2n (if tr then tload slot (drop_fresh sa sbase)
              else sload slot (drop_fresh sa sbase))` by
    simp[drop_fresh_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def] >>
  `~(drop_fresh sa sbase).vs_call_ctx.cc_static` by simp[drop_fresh_def] >>
  drule_all compile_dynarray_append_word_run >> strip_tac >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `u` >> strip_tac >> qexists_tac `u` >>
  simp_tac bool_ss [] >> conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      qpat_x_assum `state_frame u = _` (fn th => pure_once_rewrite_tac [th]) >>
      qpat_x_assum `state_frame t = _` (fn th => pure_once_rewrite_tac [th]) >>
      Cases_on `tr` >>
      simp[drop_fresh_def, sstore_def, tstore_def, LET_THM]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa sbase) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Theorem append_storage_word_abort_frag:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop sbase = SOME slot /\ cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot sbase else sload slot sbase) ==>
  frag_exec ctx sa sf (\s. s = sbase) Q
    (stmt_exit RetQ es' (INR (Error (RuntimeError "append full storage array"))))
Proof
  strip_tac >> drule append_storage_word_suffix_structure >> strip_tac >>
  irule frag_exec_run_inst_seq_drop_fresh >>
  simp_tac bool_ss [] >> reverse conj_tac
  >- fs[same_blocks_def, inst_extends_def] >>
  disj2_tac >>
  `fresh_vars_wrt sa (drop_fresh sa sbase)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa sbase) = SOME slot` by
    simp[eval_operand_drop_fresh] >>
  `cap <= w2n (if tr then tload slot (drop_fresh sa sbase)
               else sload slot (drop_fresh sa sbase))` by
    fs[drop_fresh_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def] >>
  drule_all compile_dynarray_append_word_abort >> strip_tac >>
  goal_assum $ drule_at Any >> simp[stmt_exit_def, expr_exit_def]
QED

Theorem stmt_state_rel_reserved_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  state_frame t = state_frame s /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >> irule stmt_state_rel_operand_frame >>
  qexists_tac `drop_fresh sa s` >> conj_tac
  >- (Cases >> simp[eval_operand_def] >> rpt strip_tac >>
      fs[lookup_var_def, drop_fresh_def, FLOOKUP_DRESTRICT, IN_DEF] >>
      metis_tac[lookup_var_def]) >>
  conj_tac >- asm_simp_tac bool_ss [drop_fresh_def, state_frame_vars] >>
  metis_tac[stmt_state_rel_drop_fresh]
QED

Theorem append_storage_word_frame_fields[local]:
  state_frame u = state_frame
    (if tr then tstore slot h (tstore addr w s)
     else sstore slot h (sstore addr w s)) ==>
  u.vs_current_bb = s.vs_current_bb /\
  u.vs_halted = s.vs_halted /\ u.vs_allocas = s.vs_allocas
Proof
  Cases_on `tr` >>
  simp[state_frame_def, sstore_def, tstore_def, LET_THM,
       venom_state_component_equality]
QED

Theorem append_storage_word_success_frag:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop sbase = SOME slot /\ eval_operand vop sbase = SOME w /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot sbase else sload slot sbase) /\ len < cap /\
  stmt_state_rel ctx func cenv cx es sbase /\ local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  sbase.vs_current_bb = sa.cs_current_bb /\ ~sbase.vs_halted ==>
  frag_exec ctx sa sf (\s. s = sbase)
    (\s. stmt_state_rel ctx func cenv cx es' s /\
      stmt_lands lctx sf (INL ()) s /\ ~s.vs_halted /\
      (!x a. not_fresh_at sa x /\ lookup_var x sbase = SOME a ==>
             lookup_var x s = SOME a) /\ s.vs_allocas = sbase.vs_allocas) R
Proof
  strip_tac >>
  `~sbase.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all append_storage_word_run_frag >>
  disch_then (qspecl_then [`ctx`, `R`] assume_tac) >>
  irule frag_exec_conseq >> goal_assum $ drule_at Any >>
  simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  rename1 `state_frame u = _` >>
  drule append_storage_word_frame_fields >> strip_tac >>
  qmatch_asmsub_abbrev_tac `state_frame u = state_frame su` >>
  `stmt_state_rel ctx func cenv cx es' su` by
    (drule_all stmt_state_rel_append_storage_word >> strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ es' _` mp_tac >>
     simp_tac bool_ss [Abbr `su`, GSYM wordsTheory.word_add_n2w,
                      wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `stmt_state_rel ctx func cenv cx es' u` by
    (irule stmt_state_rel_reserved_frame >> qexistsl_tac [`su`, `sa`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     qpat_x_assum `lookup_var _ su = SOME _` mp_tac >>
     Cases_on `tr` >>
     simp_tac (srw_ss()) [Abbr `su`, sstore_def, tstore_def, LET_THM, lookup_var_def] >>
     strip_tac >>
     qpat_x_assum `!x a. _ ==> lookup_var x u = SOME a`
       (qspec_then `x` mp_tac) >> simp[lookup_var_def]) >>
  `sf.cs_current_bb = sa.cs_current_bb` by
    (drule append_storage_word_suffix_structure >> simp[same_blocks_def]) >>
  qpat_x_assum `s = _` SUBST1_TAC >>
  simp[stmt_state_rel_inst_idx, stmt_lands_def, lookup_var_def] >>
  qpat_x_assum `!x a. _ ==> lookup_var x u = SOME a` mp_tac >>
  simp[lookup_var_def]
QED

Theorem append_storage_header_agree[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr)
Proof
  strip_tac >>
  `accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule accounts_rel_storage_transient >>
  disch_then (drule_at Any) >> strip_tac >>
  `storage_read_live cx tr (get_storage cx es tr) slot
     (ArrayTV tv (Dynamic cap))` by
    metis_tac[declared_storage_region_read_live] >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[storage_rel_def, transient_rel_def, get_storage_def, lookup_account_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by
    simp[type_slot_size_def] >>
  drule_all storage_agree_read_head >>
  Cases_on `tr` >> simp[tload_def, sload_def]
QED

Theorem append_storage_word_value_frag[local]:
  compile_dynarray_append cenv (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  s.vs_current_bb = sb.cs_current_bb /\ ~s.vs_halted ==>
  frag_exec ctx sb sf (\t. t = s)
    (\t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
      (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
             lookup_var x t = SOME a) /\ t.vs_allocas = s.vs_allocas)
    (stmt_exit RetQ es' res)
Proof
  strip_tac >> drule_all append_storage_header_agree >> strip_tac >>
  Cases_on `w2n (lookup_storage slot (get_storage cx es tr)) < cap`
  >- (`~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
      `res = INL ()` by
        metis_tac[append_storage_word_success, pairTheory.PAIR_EQ, sumTheory.INL_11] >>
      `eval_operand (Lit slot) s = SOME slot` by simp[eval_operand_def] >>
      `!x. Lit slot = Var x ==> not_fresh_at sb x` by simp[] >>
      `w2n (lookup_storage slot (get_storage cx es tr)) =
       w2n (if tr then tload slot s else sload slot s)` by simp[] >>
      `w2n (lookup_storage slot (get_storage cx es tr)) =
       w2n (lookup_storage slot (get_storage cx es tr))` by simp[] >>
      drule_all append_storage_word_success_frag >>
      disch_then (qspecl_then [`lctx`, `stmt_exit RetQ es' res`] assume_tac) >>
      irule frag_exec_conseq >> goal_assum $ drule_at Any >>
      simp_tac bool_ss [] >> metis_tac[]) >>
  `cap <= w2n (lookup_storage slot (get_storage cx es tr))` by decide_tac >>
  drule append_storage_full >> strip_tac >> gvs[] >>
  irule append_storage_word_abort_frag >>
  goal_assum $ drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`) >>
  simp[eval_operand_def]
QED

Theorem append_storage_value_run[local]:
  expr_sim ctx func cenv cx elem e es /\
  lower_value compile_expr cenv elem e sa = (op,sb) /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\ is_word_type (expr_type e) /\
  compile_dynarray_append cenv (Lit slot) op 1 1 elem vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  cap < dimword (:256) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,typed_val_to_w256 etv v)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es1 = (res,es') /\
  fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
     stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
     (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==> lookup_var x t = SOME a) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
     !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
       ?fuel'. run_from fuel' ctx func s0 = r) \/
  (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\ stmt_exit RetQ es' res r)
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by metis_tac[compile_lower_value_var] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac
  >- (rename1 `expr_post _ _ _ _ _ _ _ _ _ _ _ _ s1` >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      `eval_operand op s1 = SOME (typed_val_to_w256 etv v)` by
        (gvs[expr_val_rel_def] >> metis_tac[]) >>
      drule_all append_storage_word_value_frag >>
      disch_then (qspecl_then [`lctx`, `RetQ`] mp_tac) >>
      simp_tac bool_ss [frag_exec_def] >>
      disch_then (qspec_then `func` mp_tac) >>
      impl_tac >- simp[] >>
      simp_tac bool_ss [] >> strip_tac
      >- (disj1_tac >> qexists_tac `t'` >> asm_simp_tac bool_ss [] >>
          conj_tac >- metis_tac[not_fresh_at_mono] >>
          metis_tac[]) >>
      disj2_tac >> drule exit_result_not_error >> metis_tac[]) >>
  fs[expr_exit_def]
QED

Theorem append_storage_word_suffix_open[local]:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) ==>
  ~block_is_terminated sf
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
  Cases_on `sb.cs_current_insts` >>
  simp[block_is_terminated_def, mk_inst_def, is_terminator_def,
       listTheory.LAST_CONS_cond, rich_listTheory.LAST_APPEND_NOT_NIL]
QED

Theorem compile_append_storage_word_stmt_frag:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),es) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  type_slot_size tv = 1 /\ cap < dimword (:256) /\
  (!v es1. (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) ==>
    encode_value tv v = SOME [(0,typed_val_to_w256 etv v)]) /\
  expr_sim ctx func cenv cx elem e es ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  (* admitted at base cut: restated to the 9-arg stmt_frag; proof is the uncounted one (uses the dropped res/es' premise) *)
  cheat
QED
