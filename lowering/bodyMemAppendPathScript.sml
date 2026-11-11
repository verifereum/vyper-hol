(* Counted memory paths for the storage Append suffix. *)
Theory bodyMemAppendPath
Ancestors
  bodyMemAppendFacts bodyDeclMemoryCounted bodyDeclMemoryCore bodyUnopFragMemory
  stmtSimAppendStorageCompose stmtSimAppendStorage appendStorageRel
  varsExt freshWrites stateFrame exprOperandVar stmtSimProps stmtSimDefs exprSimDefs
  fragGasMode fragGasPathMem fragExecMem fragExec
  exprLoweringProps emitHelperProps loweringPosts compileEnv venomState venomInst venomExecSemantics
  vyperState vyperStorage list rich_list words finite_map

Theorem append_storage_word_frame_fields_mem[local]:
  state_frame u = state_frame
    (if tr then tstore slot h (tstore addr w s)
     else sstore slot h (sstore addr w s)) ==>
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  Cases_on `tr` >>
  simp[state_frame_def, sstore_def, tstore_def, LET_THM,
       venom_state_component_equality]
QED

Theorem append_storage_word_run_mem[local]:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME w /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap /\
  ~s.vs_call_ctx.cc_static ==>
  ?u. run_inst_seq (emitted_insts sa sf) s = OK u /\
    state_frame u = state_frame
      (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
       else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==>
           lookup_var x u = SOME a)
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot /\
   eval_operand vop (drop_fresh sa s) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  `len = w2n (if tr then tload slot (drop_fresh sa s)
             else sload slot (drop_fresh sa s)) /\
   ~(drop_fresh sa s).vs_call_ctx.cc_static` by
    simp[drop_fresh_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def] >>
  drule_all compile_dynarray_append_word_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sf) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sf) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     drule append_storage_word_suffix_structure >> simp[EVERY_MEM]) >>
  `?u. run_inst_seq (emitted_insts sa sf) s = OK u /\ vars_ext t u` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >>
     asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa sf) s` >>
     simp[vars_ext_result_def]) >>
  qexists_tac `u` >> asm_rewrite_tac [] >> conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      qpat_x_assum `state_frame u = _` (fn th => pure_once_rewrite_tac [th]) >>
      qpat_x_assum `state_frame t = _` (fn th => pure_once_rewrite_tac [th]) >>
      Cases_on `tr` >> simp[drop_fresh_def, sstore_def, tstore_def, LET_THM]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Theorem append_storage_word_success_post_mem[local]:
  state_frame u = state_frame
    (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
     else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
  (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x u = SOME a) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') ==>
  res = INL () /\ stmt_state_rel ctx func cenv cx es' u
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `state_frame u = state_frame su` >>
  drule_all stmt_state_rel_append_storage_word >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' su` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ es' _` mp_tac >>
     simp_tac bool_ss [Abbr `su`, GSYM wordsTheory.word_add_n2w,
                      wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  asm_rewrite_tac [] >>
  irule stmt_state_rel_reserved_frame >> qexistsl_tac [`su`, `sa`] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  qpat_x_assum `lookup_var _ su = SOME _` mp_tac >>
  Cases_on `tr` >>
  simp_tac (srw_ss()) [Abbr `su`, sstore_def, tstore_def, LET_THM, lookup_var_def] >>
  strip_tac >>
  qpat_x_assum `!x a. _ ==> lookup_var x u = SOME a` (qspec_then `x` mp_tac) >>
  simp[lookup_var_def]
QED

Theorem append_storage_word_success_path_mem:
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
  sbase.vs_current_bb = sa.cs_current_bb /\ ~sbase.vs_halted /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func sbase /\ alloca_inv sbase ==>
  res = INL () /\ ?t. gas_marked_path T ctx func sbase 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es' t /\ stmt_lands lctx sf (INL ()) t /\
    ~t.vs_halted /\
    (!x a. not_fresh_at sa x /\ lookup_var x sbase = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_allocas = sbase.vs_allocas /\ t.vs_alloca_next = sbase.vs_alloca_next /\
    alloca_history func t
Proof
  strip_tac >>
  `~sbase.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all append_storage_word_run_mem >> strip_tac >>
  drule_all append_storage_word_success_post_mem >> strip_tac >>
  drule append_storage_word_frame_fields_mem >> strip_tac >>
  drule append_storage_word_suffix_footprint_mem >> strip_tac >>
  `sf.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sf` by
    fs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sf)` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     rewrite_tac[EVERY_MEM] >> disch_tac >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sf) sbase` by
    metis_tac[append_storage_word_suffix_mem_ok] >>
  `gas_path_mem ctx func sbase 0
    (OK (u with vs_inst_idx := LENGTH sf.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sf.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`sbase`, `sa`] >> simp[] >> fs[EVERY_MEM]) >>
  asm_rewrite_tac [] >>
  qexists_tac `u with vs_inst_idx := LENGTH sf.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, stmt_lands_def,
       same_blocks_def, lookup_var_def] >>
  conj_tac >- fs[same_blocks_def] >>
  rpt strip_tac >>
  qpat_x_assum `!x a. _ ==> lookup_var x u = SOME a`
    (qspecl_then [`x`, `a`] mp_tac) >>
  simp[lookup_var_def]
QED

Theorem append_storage_word_abort_path_mem[local]:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot s else sload slot s) /\
  fn_has_code sa sf func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?a t. gas_marked_path T ctx func s 0 (Abort a t)
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot` by simp[eval_operand_drop_fresh] >>
  `cap <= w2n (if tr then tload slot (drop_fresh sa s)
               else sload slot (drop_fresh sa s))` by
    (qpat_x_assum `cap <= _` mp_tac >>
     simp[drop_fresh_def, tload_def, sload_def, contract_transient_def, contract_storage_def]) >>
  drule_all compile_dynarray_append_word_abort >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sf) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sf) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     drule append_storage_word_suffix_structure >> simp[EVERY_MEM]) >>
  `?a t. run_inst_seq (emitted_insts sa sf) s = Abort a t` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >> asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa sf) s` >> simp[vars_ext_result_def]) >>
  drule append_storage_word_suffix_footprint_mem >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sf)` by
    (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[EVERY_MEM] >>
     disch_tac >> rpt strip_tac >> first_x_assum drule >>
     simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sf) s` by
    metis_tac[append_storage_word_suffix_mem_ok] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sf ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa sf) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`] strip_assume_tac) >> metis_tac[]
QED

Theorem append_storage_word_value_path_mem:
  compile_dynarray_append cenv (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  s.vs_current_bb = sb.cs_current_bb /\ ~s.vs_halted /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func s /\ alloca_inv s ==>
  ?r. gas_marked_path T ctx func s 0 r /\
    ((?t. r = OK t /\ res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
      (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t) \/
     (exit_result r /\ stmt_exit RetQ es' res r))
Proof
  strip_tac >>
  drule_all append_storage_header_agree_mem >> strip_tac >>
  `eval_operand (Lit slot) s = SOME slot /\
   (!x. Lit slot = Var x ==> not_fresh_at sb x)` by simp[eval_operand_def] >>
  Cases_on `w2n (lookup_storage slot (get_storage cx es tr)) < cap`
  >- (`?len. len = w2n (if tr then tload slot s else sload slot s) /\
        len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap` by
        metis_tac[] >>
      drule_all append_storage_word_success_path_mem >>
      disch_then (qspec_then `lctx` strip_assume_tac) >>
      qexists_tac `OK t` >> simp[]) >>
  `cap <= w2n (lookup_storage slot (get_storage cx es tr))` by decide_tac >>
  drule append_storage_full >> strip_tac >>
  `cap <= w2n (if tr then tload slot s else sload slot s)` by metis_tac[] >>
  drule_all append_storage_word_abort_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `Abort a t` >>
  gvs[stmt_exit_def, exit_result_def, expr_exit_def]
QED
