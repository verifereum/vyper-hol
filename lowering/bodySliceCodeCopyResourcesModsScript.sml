(* The counted code copy and its length store share one allocation witness. *)
Theory bodySliceCodeCopyResourcesMods
Ancestors
  bodySliceOutputLandingMods bodyFullBuiltinBytestringCopy exprSimSliceExtcodeEntry
  bodyPtrBytestringBuiltinsExternalSlice bodyPtrBytestringBuiltinsCalldataFrame
  immutableMemoryFrame bodyFullBuiltinBytestringBuffer bodyPtrBytestringBuiltinsBuffer
  loweringPosts bodyMemoryDefs localPtrsProps bodyPtrDefs freshWrites
  fragGasOriginPtrLoop emitHelperProps exprLoweringProps allocaHistory
  compileEnv fragExec instIdxIndep codegenRel exprSimProps exprSimCalldataSlice
  ptrDiscipline venomExecSemantics venomState venomInst valueEncodingProofs
  loweringStateRelDefs finite_map list pred_set words arithmetic
Libs horizonTypeLib

Triviality code_slice_write_fields:
  z = mstore b w (write_memory_with_expansion d bytes v) with vs_inst_idx := j ==>
  z.vs_labels = v.vs_labels /\ z.vs_vars = v.vs_vars /\
  z.vs_data_section = v.vs_data_section /\ z.vs_allocas = v.vs_allocas /\
  z.vs_alloca_next = v.vs_alloca_next /\ z.vs_current_bb = v.vs_current_bb /\
  z.vs_accounts = v.vs_accounts /\ z.vs_transient = v.vs_transient /\
  z.vs_call_ctx = v.vs_call_ctx /\ z.vs_immutables = v.vs_immutables /\
  LENGTH v.vs_memory <= LENGTH z.vs_memory
Proof
  disch_then SUBST1_TAC >> reverse (rpt conj_tac)
  >- simp[immutable_mstore_capacity, immutable_write_memory_capacity] >>
  simp_tac bool_ss [mstore_def, write_memory_with_expansion_def, LET_THM,
                    venom_state_accfupds]
QED

Triviality code_slice_nonalloca_history:
  emit_void op ops sa = ((),sb) /\ op <> ALLOCA /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_allocas = s.vs_allocas /\ t.vs_inst_idx = SUC s.vs_inst_idx ==>
  alloca_history func t
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_void >>
  drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id op ops [])` by
    (qpat_assum `!i. i < _ ==> get_instruction _ _ = _` (qspec_then `0` mp_tac) >>
     simp_tac bool_ss [LENGTH, EL, HD, ADD_0, prim_recTheory.LESS_0] >> simp[]) >>
  `alloca_history func (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule history_nonalloca_advance >> conj_tac
     >- (qexistsl_tac [`bb`,`mk_inst sa.cs_next_id op ops []`] >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[mk_inst_def])) >>
     first_assum ACCEPT_TAC) >>
  irule alloca_history_frame >> qexists_tac `s with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Theorem slice_code_copy_resources_mods:
  compile_slice_out_buf N sa = ((out,data),sc) /\
  emit_void opc ops sc = ((),sd) /\
  emit_void MSTORE [out;cnt] sd = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  0 < n /\ n < dimword (:256) /\ 32+n <= N /\ N < dimword (:256) /\
  LENGTH bytes = n /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME (n2w n) /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) /\
  ((opc = CODECOPY /\ ops = [data;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;data;start;cnt] /\
    (?aw. eval_operand addr s = SOME aw) /\ op_taint tn addr = {} /\
    (!x. addr = Var x ==> not_fresh_at sa x))) /\
  (!v wd. v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
    v.vs_code = s.vs_code /\
    eval_operand data v = SOME wd /\ eval_operand start v = SOME wa /\
    eval_operand cnt v = SOME (n2w n) /\
    (opc = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s) ==>
    step_inst_base (mk_inst sc.cs_next_id opc ops []) v =
      OK (write_memory_with_expansion (w2n wd) bytes v)) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p w t HG tm.
    out = Var p /\ not_fresh_at sb p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,HG,tm)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var p t = SOME w /\ ptr_covers HG tm p t N /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bytes)
      (w2n w) t.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
    (!H':(bool # bytes32 # type_value) list # num list. stmt_state_rel H' ctx func cenv cx es s ==>
       stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa sc` by
    (drule compile_slice_out_buf_compiler_parts >> metis_tac[cs_extends_trans]) >>
  `cs_extends sc sd /\ cs_extends sd sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `32 <= N` by decide_tac >>
  drule_all slice_output_landing_mods >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`dst`,`w`,`v`,`G2`,`tn2`] strip_assume_tac)) >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var dst` SUBST_ALL_TAC >>
  `v.vs_labels = s.vs_labels /\ v.vs_memory = s.vs_memory /\
   v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
   v.vs_code = s.vs_code /\ v.vs_data_section = s.vs_data_section /\
   v.vs_transient = s.vs_transient /\ v.vs_immutables = s.vs_immutables` by
    (qpat_assum `v with <| vs_vars := _;vs_allocas := _;vs_alloca_next := _;
       vs_inst_idx := _ |> = s` mp_tac >> simp[venom_state_component_equality]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op v = eval_operand op s /\ op_taint tn2 op = op_taint tn op` by
    (mp_tac (Q.INST [`t` |-> `v`,`HG` |-> `G2`,`tm` |-> `tn2`]
               reserved_operand_ghost_frame) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `eval_operand start v = SOME wa /\ op_taint tn2 start = {} /\
   eval_operand cnt v = SOME (n2w n) /\ op_taint tn2 cnt = {}` by
    (qpat_assum `!op. _ ==> eval_operand op v = _ /\ _`
       (fn th => mp_tac (Q.SPEC `start` th) >> mp_tac (Q.SPEC `cnt` th)) >>
     simp[] >> metis_tac[]) >>
  `opc = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s /\
      op_taint tn2 addr = {}` by
    (strip_tac >> gvs[] >> first_x_assum (qspec_then `addr` mp_tac) >> simp[]) >>
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w+32 < dimword (:256)` by decide_tac >> simp[w2n_add_2,w2n_n2w]) >>
  `ptr_covers G2 tn2 dst v n` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `N-32` >>
     simp[] >> decide_tac) >>
  `step_inst_base (mk_inst sc.cs_next_id opc ops []) v =
     OK (write_memory_with_expansion (w2n (w+32w)) bytes v)` by
    (first_x_assum (qspecl_then [`v`,`w+32w`] match_mp_tac) >>
     simp[eval_operand_def]) >>
  suspend "writes"
QED

Resume slice_code_copy_resources_mods[writes]:
  mp_tac (bytestring_external_copy_length_full_run |> Q.INST
    [`sa` |-> `sc`, `sm` |-> `sd`, `s` |-> `v`, `G` |-> `G2`,
     `tn` |-> `tn2`, `wd` |-> `w+32w`, `wn` |-> `n2w n`, `b` |-> `w`]) >>
  (impl_tac >-
    (simp[eval_operand_def,w2n_n2w] >>
     qpat_assum `(opc = CODECOPY /\ _) \/ _` strip_assume_tac >> gvs[] >>
     metis_tac[])) >>
  disch_then (qx_choosel_then [`u`,`t`,`tm`] strip_assume_tac) >>
  `t = mstore (w2n w) (n2w n) (write_memory_with_expansion (w2n w+32) bytes v)
        with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (qpat_assum `t = mstore _ _ _ with vs_inst_idx := _` mp_tac >>
     qpat_assum `u = write_memory_with_expansion _ _ _ with vs_inst_idx := _` mp_tac >>
     qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts` mp_tac >>
     qpat_assum `w2n (w+32w) = w2n w+32` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[mstore_idx]) >>
  drule_then strip_assume_tac code_slice_write_fields >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G2,tm)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G2`,`v`,`tn2`] >>
     conj_tac >> first_assum irule) >>
  `!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `tm.t_mem = _` SUBST1_TAC >> simp[] >> rpt strip_tac >>
     qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `source_memory_write_ranges (mk_inst sc.cs_next_id opc ops []) v = [(w2n w+32,n)]` by
    (qpat_assum `(opc = CODECOPY /\ _) \/ _` strip_assume_tac >>
     qpat_x_assum `opc = _` SUBST_ALL_TAC >> qpat_x_assum `ops = _` SUBST_ALL_TAC >>
     simp[source_memory_write_ranges_def,sized_source_write_range_def,
          mk_inst_def,eval_operand_def,w2n_n2w,LESS_MOD]) >>
  `!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem` by
    (qpat_assum `tm.t_mem = _` SUBST1_TAC >>
     simp[range_bytes_def] >> rpt strip_tac >> decide_tac) >>
  `alloca_history func t` by
    (`u.vs_current_bb = v.vs_current_bb /\ u.vs_allocas = v.vs_allocas /\
      u.vs_inst_idx = SUC v.vs_inst_idx` by
       (qpat_assum `u = write_memory_with_expansion _ _ _ with vs_inst_idx := _`
          SUBST1_TAC >> simp_tac bool_ss [write_memory_with_expansion_def,LET_THM,
                                          venom_state_accfupds, combinTheory.K_THM]) >>
     `opc <> ALLOCA` by
       (qpat_assum `(opc = CODECOPY /\ _) \/ _` strip_assume_tac >> simp[]) >>
     `alloca_history func u` by (irule code_slice_nonalloca_history >>
       qexistsl_tac [`opc`,`ops`,`v`,`sc`,`sd`] >> simp[]) >>
     `u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts` by
       (qpat_assum `emit_void opc ops sc = ((),sd)` (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
        qpat_assum `emit_void opc ops sc = ((),sd)` (mp_then Any mp_tac emit_void_extends) >>
        simp[same_blocks_def]) >>
     irule code_slice_nonalloca_history >>
     qexistsl_tac [`MSTORE`,`[Var root;cnt]`,`u`,`sd`,`sb`] >>
     `t.vs_current_bb = u.vs_current_bb /\ t.vs_inst_idx = SUC u.vs_inst_idx` by
       (qpat_assum `t = mstore _ _ u with vs_inst_idx := _` SUBST1_TAC >>
        simp_tac bool_ss [mstore_def, LET_THM, venom_state_accfupds, combinTheory.K_THM]) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  suspend "frames"
QED

Resume slice_code_copy_resources_mods[frames]:
  `!off len. regions_disjoint off len (w2n w) N ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >> qpat_assum `t = mstore _ _ (write_memory_with_expansion _ _ _) with vs_inst_idx := _`
       SUBST1_TAC >> simp[NoAsms] >>
     qpat_assum `v.vs_memory = s.vs_memory` (fn th => once_rewrite_tac[GSYM th]) >>
     qpat_assum `LENGTH bytes = n` (fn th => once_rewrite_tac[GSYM th]) >>
     irule bytes_buffer_write_frame >> fs[regions_disjoint_def] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (`local_region cenv es.scopes v name b len` by
           (irule local_region_frame_fwd >> qexistsl_tac [`s`,`sa`,`es.scopes`] >>
            simp[] >> rpt strip_tac >>
            qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _`
              (drule_then strip_assume_tac) >> simp[]) >>
         first_x_assum irule >>
         qpat_assum `!name b len. local_region _ _ v name b len ==> _`
           (drule_then mp_tac) >> simp[regions_disjoint_def, DISJ_COMM]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     `b+len <= s.vs_alloca_next` by (drule_all body_local_region_frontier >> simp[]) >> decide_tac) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _` (drule_then strip_assume_tac) >>
     rpt conj_tac
     >- (qpat_assum `t.vs_vars = v.vs_vars` (fn th => simp_tac bool_ss [lookup_var_def,th]) >>
         qpat_assum `lookup_var x v = lookup_var x s` (ACCEPT_TAC o REWRITE_RULE[lookup_var_def]))
     >- first_assum ACCEPT_TAC >>
     qpat_assum `tm.t_var = tn2.t_var` (fn th => simp_tac bool_ss [op_taint_def,th]) >>
     qpat_assum `op_taint tn2 (Var x) = op_taint tn (Var x)`
       (ACCEPT_TAC o REWRITE_RULE[op_taint_def])) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo v` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id` by
    (drule_all slice_extcode_out_owner_inst >> strip_tac >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [STRING #"%" (toString sa.cs_next_var)]` >>
     simp[mk_inst_def] >>
     qpat_assum `MEM (mk_inst _ ALLOCA _ _) (fn_insts func)` (ACCEPT_TAC o REWRITE_RULE[mk_inst_def])) >>
  rename1 `MEM allocinst (fn_insts func)` >>
  suspend "post"
QED

Resume slice_code_copy_resources_mods[post]:
  `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> b+sz <= s.vs_alloca_next` by
    (`alloca_inv s` by
       (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s` mp_tac >>
        simp_tac bool_ss [stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `alloca_inv s` mp_tac >>
     simp_tac bool_ss [venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tm` by
    (rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (drule_then strip_assume_tac) >> simp[])
     >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
         `off+sz <= s.vs_alloca_next` by
           (first_x_assum irule >> qexists_tac `aid` >> first_assum ACCEPT_TAC) >> decide_tac)
     >> rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ s name b len ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!i. b <= i /\ i < b+sz /\ i IN tm.t_mem ==> _`
       (qspec_then `i` match_mp_tac) >> simp[]) >>
  `locals_kept cenv es es s t` by
    (irule locals_kept_regions >> rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ s name b len ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `pure_frame cenv func es sa s t` by
    (rewrite_tac[pure_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!name b len. local_region _ _ s name b len ==> _`
           (drule_then strip_assume_tac) >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint off len b sz`
       (qspecl_then [`allocinst`,`w2n w`,`N`] match_mp_tac) >> simp[]) >>
  `!H':(bool # bytes32 # type_value) list # num list. stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es t` by
    (rpt strip_tac >> qpat_assum `t = mstore _ _ (write_memory_with_expansion _ _ _) with vs_inst_idx := _`
       SUBST1_TAC >> simp_tac bool_ss [stmt_state_rel_inst_idx] >>
     irule allocated_bytes_write_state_rel >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qexistsl_tac [`N`,`allocinst`] >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE simp[])) >>
     qpat_assum `!H':(bool # bytes32 # type_value) list # num list. stmt_state_rel H' ctx func cenv cx es s ==> _`
       (qspec_then `H'` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume slice_code_copy_resources_mods[finish]:
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `v.vs_memory = s.vs_memory` (fn th => once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`root`,`w`,`t`,`G2`,`tm`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC ORELSE REFL_TAC)
  >~ [`not_fresh_at sb root`]
  >- (irule not_fresh_at_mono >> qexists_tac `sc` >>
      qpat_assum `emit_void opc ops sc = ((),sd)` (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
      qpat_assum `emit_void MSTORE _ sd = ((),sb)` (mp_then Any strip_assume_tac emitted_insts_emit_void) >> simp[])
  >~ [`lookup_var root t = SOME w`]
  >- (qpat_assum `t.vs_vars = v.vs_vars` (fn th => simp_tac bool_ss [lookup_var_def,th]) >>
      qpat_assum `lookup_var root v = SOME w` (ACCEPT_TAC o REWRITE_RULE[lookup_var_def]))
  >~ [`val_in_memory _ _ _ _`]
  >- (qpat_assum `t = mstore _ _ (write_memory_with_expansion _ _ _) with vs_inst_idx := _`
        SUBST1_TAC >> simp[NoAsms] >>
      qpat_assum `LENGTH bytes = n` (fn th => once_rewrite_tac[GSYM th]) >>
      irule bytes_buffer_write_encoding)
  >- simp[]
  >- simp[]
  >- (qpat_assum `allocas_from lo v` mp_tac >>
      qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => simp_tac bool_ss [allocas_from_def,th]))
  >~ [`lo <= t.vs_alloca_next`]
  >- decide_tac
  >- (qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> first_x_assum irule >>
      qpat_assum `!aid b len. aid < _ /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==> _`
        (qspecl_then [`aid`,`b`,`len`] mp_tac) >> simp[regions_disjoint_def,DISJ_COMM])
  >- (first_x_assum irule >> simp[regions_disjoint_def])
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac)
  >> (simp[] >> decide_tac)
QED

Finalise slice_code_copy_resources_mods
