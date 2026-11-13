(* A captured nonword cell: destination address, delayed unwrap, then store. *)
Theory extcallStoreMemory
Ancestors
  extcallMaterializeMemory extcallStoreUnwrapMemory exprSimMapKey exprSimMemDefs
  bodyFieldMemoryProps bodyMemAssignAttrStorage exprSimVVFrame
  exprSimBufferStore exprSimProps exprLoweringProps freshWrites
  exprSafeOperand exprOperandVar exprSimCopy vyperState emitHelperProps
  loweringPosts loweringStateRelDefs exprLowering compileEnv context
  fragGasPathMem fragExec allocaHistory words list venomState instIdxIndep exprBopSimProps

Theorem extcall_stored_nonword_capture_mem:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
  unwrap_value ce vv sm = (src,su) /\
  compile_store_memory ce src dst lt lt su = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm su func /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ci_mono sa sm /\ ci_mono sm su /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand buf s = SOME (n2w b) /\
  b + off + type_memory_size tv < dimword (:256) /\
  b + off + type_memory_size tv <= s.vs_alloca_next /\
  ~is_word_type lt /\ evaluate_type (get_tenv cx) lt = SOME tv /\
  type_memory_bytes ce lt = type_memory_size tv /\
  value_has_type tv v /\ val_wf tv v /\
  vv_holds ce cx lt (Value v) vv es s /\
  vv_store_bound cx lt lt es (Value v) vv s /\ vv_storage_live cx vv es s /\
  (!x. vv_operand vv = Var x \/ buf = Var x ==> not_fresh_at sa x) /\
  (!tag p. vv = LocatedValue tag p ==>
    (p.ptr_location <> LocMemory \/ is_word_type tag ==> tag = lt) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sa x))) /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a + n <= b + off \/ b + off + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (b+off) z.vs_memory /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid a n x k. FLOOKUP s.vs_allocas aid = SOME (a,n) /\
      aid < sa.cs_next_id /\ a <= x /\ x+k <= a+n /\
      (x+k <= b+off \/ b+off+type_memory_size tv <= x) ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name a n x k. local_region ce es.scopes s name a n /\
      a <= x /\ x+k <= a+n ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name io itv iv x k. ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) /\
      io <= x /\ x+k <= io+type_memory_size itv ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x /\ not_fresh_at su x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all emit_ADD_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all attr_add_history >> strip_tac >>
  drule_all attr_add_gas_path >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `gas_path_mem ctx func s 0 (OK u)` by metis_tac[] >>
  `b+off < dimword (:256) /\ type_memory_size tv < dimword (:256)` by decide_tac >>
  suspend "address"
QED

Resume extcall_stored_nonword_capture_mem[address]:
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   t.vs_data_section = s.vs_data_section /\
   t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
     simp[contract_storage_def, contract_transient_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     qexistsl_tac [`0`, `0`, `sa`] >>
     simp[regions_disjoint_def] >>
     qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def] >> metis_tac[]) >>
  `vv_holds ce cx lt (Value v) vv es t` by
    (drule_all vv_holds_vars_frame >> simp[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by simp[] >>
  `vv_store_bound cx lt lt es (Value v) vv t` by
    (drule_all vv_store_bound_frame_mem_src >> simp[]) >>
  `vv_storage_live cx vv es t` by (Cases_on `vv` >> gvs[vv_operand_def]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x. dst = Var x ==> not_fresh_at sm x` by
    metis_tac[emit_op_safe_operand, safe_operand_def] >>
  suspend "unwrap"
QED

Resume extcall_stored_nonword_capture_mem[unwrap]:
  `read_result cx (Value v) es = (INL v,es)` by EVAL_TAC >>
  `!tag arg. vv = StackValue tag arg ==>
     !x. arg = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> gvs[vv_operand_def]) >>
  `!tag p. vv = LocatedValue tag p ==>
    (p.ptr_location <> LocMemory \/ is_word_type tag \/ is_word_type lt ==> tag = lt) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (p.ptr_location <> LocMemory ==> lt = lt) /\
    (is_word_type lt /\ p.ptr_location = LocMemory ==>
      !w. eval_operand p.ptr_operand u = SOME w ==> w2n w+32 <= u.vs_alloca_next) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region u = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))` by
    (map_every qx_gen_tac [`tag`, `p`] >> strip_tac >> simp[] >>
     `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by gvs[vv_operand_def] >>
     simp[] >> rpt strip_tac
     >- metis_tac[]
     >- (simp[Abbr `u`, eval_operand_def] >>
         Cases_on `region` >> gvs[eval_operand_def] >> metis_tac[]) >>
     fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_extends >> simp[same_blocks_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   stmt_state_rel ctx func ce cx es u /\ vv_storage_live cx vv es u` by
    simp[Abbr `u`, stmt_state_rel_inst_idx] >>
  `u.vs_memory = t.vs_memory /\
   contract_storage u = contract_storage t /\
   contract_transient u = contract_transient t /\
   t.vs_alloca_next <= u.vs_alloca_next` by
    simp_tac (srw_ss()) [Abbr `u`, contract_storage_def, contract_transient_def] >>
  `!x. lookup_var x u = lookup_var x t` by
    simp_tac (srw_ss()) [Abbr `u`, lookup_var_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by simp[] >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) t` by
    (simp_tac (srw_ss()) [Abbr `u`, eval_op_inst_idx]) >>
  `vv_holds ce cx lt (Value v) vv es u` by
    (irule vv_holds_vars_frame >> qexists_tac `t` >> simp[]) >>
  `vv_store_bound cx lt lt es (Value v) vv u` by
    (irule vv_store_bound_frame_mem_src >> qexists_tac `t` >> simp[]) >>
  `local_ptrs_reserved ce sm` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  drule_all extcall_captured_unwrap_mem >> strip_tac >> suspend "store"
QED

Resume extcall_stored_nonword_capture_mem[store]:
  `eval_operand dst u = SOME (n2w (b+off))` by
    simp[Abbr `u`, eval_op_inst_idx, word_add_n2w] >>
  `safe_operand sm dst` by metis_tac[emit_op_safe_operand] >>
  `!lab. dst <> Label lab` by (Cases_on `dst` >> fs[safe_operand_def]) >>
  `eval_operand dst z = SOME (n2w (b+off))` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`sm`, `u`] >> simp[] >> metis_tac[]) >>
  `w2n (n2w (b+off):bytes32) = b+off` by simp[] >>
  `w2n (n2w (b+off):bytes32) + type_memory_size tv <= z.vs_alloca_next` by
    (fs[Abbr `u`] >> decide_tac) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. src = Var x ==> not_fresh_at su x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> gvs[vv_operand_def]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at su x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[] >> simp[]) >>
  `!name a n. local_region ce es.scopes z name a n ==>
    a+n <= b+off \/ b+off+type_memory_size tv <= a` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name a n` by
       metis_tac[copy_buffer_local_region_frame] >> metis_tac[]) >>
  `alloca_inv z` by fs[stmt_state_rel_def] >>
  drule_all extcall_materialize_store_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func ce cx es q` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ z`)) >>
     qexistsl_tac [`b+off`, `type_memory_size tv`, `su`] >>
     simp[] >>
     qpat_x_assum `!name a n. local_region ce es.scopes z name a n ==> _` mp_tac >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _` mp_tac >>
     qpat_x_assum `ce.ce_is_ctor ==> !name itv iv io. _` mp_tac >>
     qpat_x_assum `w2n (n2w (b+off):bytes32) = b+off` mp_tac >>
     rpt (pop_assum kall_tac) >>
     ntac 4 strip_tac >> gvs[GSYM arithmeticTheory.ADD_ASSOC] >>
     rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
  `val_in_memory tv v (b+off) q.vs_memory` by
    (qpat_x_assum `val_in_memory tv v _ q.vs_memory` mp_tac >> simp[]) >>
  qabbrev_tac `out = q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_path_mem ctx func z 0 (OK out) /\ alloca_history func out /\
   stmt_state_rel ctx func ce cx es out /\ ~out.vs_halted /\
   out.vs_current_bb = sb.cs_current_bb /\
   out.vs_inst_idx = LENGTH sb.cs_current_insts /\
   val_in_memory tv v (b+off) out.vs_memory` by
    simp[Abbr `out`, stmt_state_rel_inst_idx] >>
  `out.vs_alloca_next = z.vs_alloca_next /\ out.vs_allocas = z.vs_allocas /\
   contract_storage out = contract_storage z /\
   contract_transient out = contract_transient z /\
   out.vs_data_section = z.vs_data_section /\ out.vs_labels = z.vs_labels` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = z` (SUBST1_TAC o SYM) >>
     simp[Abbr `out`, contract_storage_def, contract_transient_def]) >>
  `!x. lookup_var x out = lookup_var x q` by
    simp_tac (srw_ss()) [Abbr `out`, lookup_var_def] >>
  `!x. not_fresh_at su x ==> lookup_var x out = lookup_var x z` by simp[] >>
  `!a k. a+k <= b+off \/ b+off+type_memory_size tv <= a ==>
    mem_bytes_at a k out.vs_memory = mem_bytes_at a k z.vs_memory` by
    (rpt strip_tac >> simp_tac (srw_ss()) [Abbr `out`] >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _`
       (qspecl_then [`a`, `k`] irule) >> simp[]) >>
  suspend "join"
QED
Resume extcall_stored_nonword_capture_mem[join]:
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s /\
   u.vs_data_section = s.vs_data_section /\ u.vs_labels = s.vs_labels` by
    (simp[Abbr `u`, contract_storage_def, contract_transient_def] >>
     fs[contract_storage_def, contract_transient_def]) >>
  `gas_path_mem ctx func s 0 (OK out)` by
    (qpat_assum `gas_path_mem ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_path_mem_then) >>
     disch_then drule >> simp[] >> strip_tac >>
     qpat_assum `gas_path_mem ctx func s 0 (OK z)`
       (mp_then Any mp_tac gas_path_mem_then) >>
     disch_then drule >> simp[]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry` by simp[Abbr `u`] >>
  `!name a n. local_region ce es.scopes s name a n ==>
    local_region ce es.scopes u name a n` by
    (rpt strip_tac >>
     metis_tac[copy_buffer_local_region_frame]) >>
  qexists_tac `out` >> simp[] >>
  suspend "frames"
QED
Resume extcall_stored_nonword_capture_mem[frames]:
  conj_tac >- suspend "registered" >>
  conj_tac >- suspend "locals" >>
  suspend "immutables"
QED
Resume extcall_stored_nonword_capture_mem[registered]:
  map_every qx_gen_tac [`aid`, `a`, `n`, `x`, `k`] >> strip_tac >>
  `mem_bytes_at x k out.vs_memory = mem_bytes_at x k z.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k out.vs_memory = _`
      (qspecl_then [`x`, `k`] irule) >> simp[]) >>
  `mem_bytes_at x k z.vs_memory = mem_bytes_at x k u.vs_memory` by
    (qpat_x_assum `!aid b sz off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`aid`, `a`, `n`, `x`, `k`] mp_tac) >>
     `aid < sm.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
     simp[]) >> simp[Abbr `u`]
QED
Resume extcall_stored_nonword_capture_mem[locals]:
  map_every qx_gen_tac [`name`, `a`, `n`, `x`, `k`] >> strip_tac >>
  `x+k <= b+off \/ b+off+type_memory_size tv <= x` by
    (`a+n <= b+off \/ b+off+type_memory_size tv <= a` by metis_tac[] >> decide_tac) >>
  `mem_bytes_at x k out.vs_memory = mem_bytes_at x k z.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k out.vs_memory = _`
      (qspecl_then [`x`, `k`] irule) >> simp[]) >>
  `mem_bytes_at x k z.vs_memory = mem_bytes_at x k u.vs_memory` by
    (qpat_x_assum `!name b sz off len. _ ==> mem_bytes_at off len z.vs_memory = _`
      (qspecl_then [`name`, `a`, `n`, `x`, `k`] mp_tac) >> simp[]) >> simp[Abbr `u`]
QED
Resume extcall_stored_nonword_capture_mem[immutables]:
  map_every qx_gen_tac [`name`, `io`, `itv`, `iv`, `x`, `k`] >> strip_tac >>
  `regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)` by
    metis_tac[] >>
  `x+k <= b+off \/ b+off+type_memory_size tv <= x` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at x k out.vs_memory = mem_bytes_at x k z.vs_memory` by metis_tac[] >>
  `mem_bytes_at x k z.vs_memory = mem_bytes_at x k u.vs_memory` by
    (qpat_x_assum `!name io itv iv off len. _ ==> mem_bytes_at off len z.vs_memory = _`
      (qspecl_then [`name`, `io`, `itv`, `iv`, `x`, `k`] mp_tac) >> simp[]) >>
  simp[Abbr `u`]
QED
Finalise extcall_stored_nonword_capture_mem
