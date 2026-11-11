(* Common counted allocation and call endpoint, independent of result policy. *)
Theory rawCallAllocatedOracleMemory
Ancestors
  rawCallOracleMemory exprSimRawCall exprSimRawCallCalldata exprSimWordArgs exprSimDefs loweringPosts loweringStateRelDefs
  exprSafeOperand exprSimProps exprLoweringProps fragGasPathMem
  builtinSystem emitHelperProps compileEnv venomMemDefs venomState
  instIdxIndep entrySinkExtraction valueTypingMemoryProps vfmConstants words finite_map list

Theorem raw_call_allocated_oracle_mem:
  compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sm = (ok,sc) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  ci_mono initial sa /\ wb_frame cenv initial_es es initial s0 s /\
  stmt_state_rel ctx func cenv cx initial_es s0 /\ local_ptrs_reserved cenv initial /\
  MAP FDOM initial_es.scopes = MAP FDOM es.scopes /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand val_op s = SOME val_word /\
  safe_operand sa to_op /\ safe_operand sa dp /\ safe_operand sa dl /\
  safe_operand sa gas_op /\ safe_operand sa val_op /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  cap < dimword (:256) /\
  (0 < cap ==> ((cap+31) DIV 32)*32+32 < dimword (:256)) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_path_mem ctx func s 0 (OK u) /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func u /\ ~u.vs_halted /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    wb_frame cenv initial_es (SND (adopt_call_outcome rq outcome es1)) initial s0 u /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    eval_operand ov u = SOME w /\ safe_operand sc ov /\ safe_operand sc ok /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (w2n w, if cap=0 then 0 else ((cap+31) DIV 32)*32+32) /\
    w2n w + (if cap=0 then 0 else ((cap+31) DIV 32)*32+32) < dimword (:256) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (if cap=0 then w2n w else w2n w+32)
      (LENGTH (TAKE cap outcome.co_returnData)) u.vs_memory = TAKE cap outcome.co_returnData /\
    (0 < cap ==>
      (?alloc q. MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
        alloc.inst_outputs = [q] /\ alloc.inst_id = sa.cs_next_id /\
        not_local_ptr cenv (SND (adopt_call_outcome rq outcome es1)).scopes q /\
        initial.cs_next_id <= alloc.inst_id /\ alloc.inst_id < sc.cs_next_id) /\
      (!aid b sz. aid < initial.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n w) (((cap+31) DIV 32)*32+32) b sz) /\
      (!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
        regions_disjoint (w2n w) (((cap+31) DIV 32)*32+32) b sz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND] >>
  `ci_mono sm sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `safe_operand sm ov /\ safe_operand sm op` by metis_tac[calldata_outbuf_operands] >>
  drule_all raw_call_outbuf_run_mem >>
  disch_then (qx_choose_then `t` (qx_choose_then `w` (map_every assume_tac o CONJUNCTS))) >>
  `!p v. safe_operand sa p /\ eval_operand p s = SOME v ==> eval_operand p t = SOME v` by
    (rpt strip_tac >> Cases_on `p` >> gvs[safe_operand_def, eval_operand_def] >>
     irule wb_frame_vars >> qexistsl_tac [`cenv`,`es`,`es`,`s`,`sa`] >> simp[]) >>
  `wb_frame cenv initial_es es initial s0 t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`sa`,`s`] >> fs[ci_mono_def]) >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `cap <= ((cap+31) DIV 32)*32` by
    (qspec_then `cap` mp_tac word_size_capacity >> simp[word_size_def]) >>
  suspend "separation"
QED

Resume raw_call_allocated_oracle_mem[separation]:
  markerLib.RESUME_TAC >>
  `initial.cs_next_id <= sa.cs_next_id /\ initial.cs_next_var <= sm.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!aid b sz. aid < initial.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n w) (if cap=0 then 0 else ((cap+31) DIV 32)*32+32) b sz` by
    (rpt strip_tac >>
     `aid <> sa.cs_next_id` by decide_tac >>
     fs[stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum (qspecl_then [`sa.cs_next_id`,`aid`,`w2n w`,
       `if cap=0 then 0 else ((cap+31) DIV 32)*32+32`,`b`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    regions_disjoint (w2n w) (if cap=0 then 0 else ((cap+31) DIV 32)*32+32) b sz` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name b sz` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`,`initial`,`initial_es.scopes`] >> fs[wb_frame_def]) >>
     metis_tac[]) >>
  suspend "oracle_pre"
QED

Resume raw_call_allocated_oracle_mem[oracle_pre]:
  markerLib.RESUME_TAC >>
  `~t.vs_halted` by
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts sa sm)` by
       (drule_all raw_call_outbuf_no_gas >> simp[EVERY_MEM] >> metis_tac[]) >>
     drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  qabbrev_tac `a = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `stmt_state_rel ctx func cenv cx es a /\ wb_frame cenv initial_es es initial s0 a /\
   alloca_history func a /\ a.vs_current_bb = sm.cs_current_bb /\
   a.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~a.vs_halted` by
    (simp[Abbr `a`, stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx] >>
     fs[stmt_state_rel_def]) >>
  `eval_operand gas_op a = SOME gas /\ eval_operand to_op a = SOME aw /\
   eval_operand dp a = SOME ao /\ eval_operand dl a = SOME az /\
   eval_operand val_op a = SOME val_word /\
   eval_operand op a = SOME (if cap=0 then w else w+32w) /\
   eval_operand ov a = SOME w` by
    (simp[Abbr `a`, eval_op_inst_idx] >> metis_tac[]) >>
  `take_call_outcome target (read_memory (w2n ao) (w2n az) a) value_opt es =
    (INL (rq,outcome),es1)` by
    (simp[Abbr `a`, read_memory_def] >> fs[read_memory_def]) >>
  Q.SUBGOAL_THEN
    `(w2n az = 0 \/ w2n ao + w2n az <= a.vs_alloca_next) /\
      (cap=0 \/ w2n (if cap=0 then w else w+32w) + cap <= a.vs_alloca_next)`
    (map_every assume_tac o CONJUNCTS)
  >- (simp[Abbr `a`] >> Cases_on `cap=0` >- fs[] >> fs[] >>
     `0 < cap` by decide_tac >>
     `w2n w + (((cap+31) DIV 32)*32+32) <= t.vs_alloca_next` by
       (`alloca_next_valid t` by fs[stmt_state_rel_def, alloca_inv_def] >>
        fs[alloca_next_valid_def] >>
        first_x_assum (drule_then mp_tac) >> simp[]) >>
     fs[] >> decide_tac) >>
  suspend "oracle_sep"

QED

Resume raw_call_allocated_oracle_mem[oracle_sep]:
  markerLib.RESUME_TAC >>
  `!name b sz. local_region cenv es.scopes a name b sz ==>
    b + sz <= w2n (if cap=0 then w else w+32w) \/
    w2n (if cap=0 then w else w+32w) + cap <= b` by
    (simp[Abbr `a`, local_region_def, lookup_var_def] >> rpt strip_tac >>
     qpat_x_assum `!name b sz. local_region cenv es.scopes t name b sz ==> _`
       (qspecl_then [`name`,`b`,`sz`] mp_tac) >>
     Cases_on `cap=0` >> fs[local_region_def, lookup_var_def,
       loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `(cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n (if cap=0 then w else w+32w) \/
    w2n (if cap=0 then w else w+32w) + cap <= off)` by
    (rpt strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then (drule_all_then mp_tac) >>
     Cases_on `cap=0` >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid b sz. aid < initial.cs_next_id /\ FLOOKUP a.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n (if cap=0 then w else w+32w)) cap b sz` by
    (simp[Abbr `a`] >> rpt strip_tac >>
     qpat_x_assum `!aid b sz. _ /\ FLOOKUP t.vs_allocas aid = _ ==> _`
       (drule_all_then mp_tac) >>
     Cases_on `cap=0` >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    regions_disjoint (w2n (if cap=0 then w else w+32w)) cap b sz` by
    (rpt strip_tac >>
     qpat_x_assum `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==> _`
       (drule_all_then mp_tac) >>
     Cases_on `cap=0` >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "call"
QED

Resume raw_call_allocated_oracle_mem[call]:
  markerLib.RESUME_TAC >>
  qpat_assum `emit_op _ _ sm = _`
    (mp_then Any mp_tac raw_call_oracle_run_mem) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ es a`)) >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ initial_es es initial s0 a`)) >>
  disch_then (qspecl_then [`val_word`,`if cap=0 then w else w+32w`,`gas`,`aw`] mp_tac) >>
  (impl_tac >- (gs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `u` strip_assume_tac)) >>
  `safe_operand sc ov /\ safe_operand sc ok` by
    (conj_tac >- (irule safe_operand_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
     metis_tac[emit_op_safe_operand]) >>
  `eval_operand ov u = SOME w` by metis_tac[] >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts))` by
    (drule_all gas_path_mem_then >> simp[]) >>
  suspend "endpoint"
QED

Resume raw_call_allocated_oracle_mem[endpoint]:
  markerLib.RESUME_TAC >>
  `u.vs_memory = r.vs_memory` by
    (qpat_x_assum `u = update_var _ _ r` SUBST1_TAC >> simp[update_var_def]) >>
  `mem_bytes_at (if cap=0 then w2n w else w2n w+32)
    (LENGTH (TAKE cap outcome.co_returnData)) u.vs_memory = TAKE cap outcome.co_returnData` by
    (Cases_on `cap=0` >- fs[valueEncodingDefsTheory.mem_bytes_at_def] >>
     `0 < cap` by decide_tac >> gs[]) >>
  qpat_x_assum `r.vs_memory = _` kall_tac >>
  qpat_x_assum `u.vs_memory = r.vs_memory` kall_tac >>
  qpat_x_assum `u = update_var _ _ r` kall_tac >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sc.cs_current_insts`,`w`] >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx, eval_op_inst_idx] >>
  fs[Abbr `a`] >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  (Cases_on `cap = 0` >- gs[] >>
   strip_tac >>
   conj_tac
   >- (drule_all raw_call_outbuf_allocation_site >>
       disch_then (qspec_then `(SND (adopt_call_outcome rq outcome es1)).scopes`
         (qx_choose_then `alloc` (qx_choose_then `q` strip_assume_tac))) >>
       qexistsl_tac [`alloc`,`q`] >> fs[ci_mono_def] >> decide_tac) >>
   fs[] >> conj_tac >> first_assum ACCEPT_TAC)
QED

Finalise raw_call_allocated_oracle_mem
