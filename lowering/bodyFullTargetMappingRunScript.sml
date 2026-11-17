Theory bodyFullTargetMappingRun
Ancestors
  bodyFullTargetMappingKey bodyFullTargetMappingScratch targetSubscriptMapping
  exprOperandVar exprSimWordArgs exprSimProps exprSimMapKey
  bodyPtrDefs loweringPosts exprLoweringProps fragGasOriginPtr
  bodyFullUnwrapRun ptrDiscipline loweringStateRelDefs
  allocaHistory venomState compileEnv finite_map words pred_set list pair fragExec

Theorem mapping_suffix_full_run:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  (!x. key = Var x \/ bop = Var x ==> not_fresh_at sn x) /\
  ~ctx_has_dalloca ctx /\
  (if is_bytestring_type kt then
     ?x b base cap bs.
       key = Var x /\ eval_operand key s = SOME (n2w b) /\
       FLOOKUP G x = SOME (base,cap) /\ base <= b /\
       b+32+LENGTH bs <= base+cap /\
       b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
       b+32+LENGTH bs <= s.vs_alloca_next /\
       op_taint tn key = {} /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
       mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
       encode_hashmap_key kt v = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
   else eval_operand key s = SOME (encode_hashmap_key kt v) /\
        op_taint tn key = {} /\ op_prov G key = NONE) /\
  eval_operand bop s = SOME base_slot /\ op_taint tn bop = {} /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. slot = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sn s t /\ pure_frame cenv func es sn s t /\
    ghost_kept_at lo cenv es sn G tn s HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\
      ghost_inv_at (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >>
  `ci_mono sn sp` by
    (Cases_on `is_bytestring_type kt`
     >- (gvs[] >> metis_tac[ci_mono_compile_keccak256_key, SND]) >>
     gvs[ci_mono_def, cs_extends_def]) >>
  `ci_mono sp sb` by metis_tac[ci_mono_compile_mapping_subscript, SND] >>
  `fn_has_code sn sp func /\ fn_has_code sp sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `!x. key = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  `!x. bop = Var x \/ hashed = Var x ==> not_fresh_at sp x` by
    (Cases_on `is_bytestring_type kt` >> gvs[]
     >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
         strip_tac >>
         qpat_x_assum `sp.cs_current_insts = _` kall_tac >>
         rpt strip_tac >> gvs[] >>
         irule compiler_ci_mono_not_fresh >> qexists_tac `sn` >> simp[]) >>
     metis_tac[]) >>
  drule_all mapping_key_prefix_full_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  suspend "slot"
QED
Resume mapping_suffix_full_run[slot]:
  rename1 `run_inst_seq (emitted_insts sn sp) s = OK u` >>
  `sp.cs_current_bb = sn.cs_current_bb /\
   sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sp)` by
    (Cases_on `is_bytestring_type kt` >> gvs[]
     >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
         gvs[same_blocks_def, EVERY_MEM]) >>
     simp[emitted_insts_def]) >>
  `u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\ ~u.vs_halted` by
    (qpat_assum `u with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand bop (u with vs_inst_idx := LENGTH sp.cs_current_insts) = SOME base_slot /\
   op_taint tm bop = {}` by
    (Cases_on `bop` >> gvs[eval_operand_def, lookup_var_def, op_taint_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sp /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x)` by
    metis_tac[local_ptrs_reserved_next_var, compiler_ci_mono_not_fresh, ci_mono_def] >>
  `stmt_state_rel H0 ctx func cenv cx es
     (u with vs_inst_idx := LENGTH sp.cs_current_insts)` by metis_tac[] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sp.cs_current_insts)` by
    (irule emitted_alloca_history >> conj_tac >- simp[] >>
     qexistsl_tac [`emitted_insts sn sp`, `s`, `sn`] >>
     simp[] >> metis_tac[stmt_state_rel_def]) >>
  `allocas_from lo (u with vs_inst_idx := LENGTH sp.cs_current_insts)` by
    (simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  `eval_operand hashed (u with vs_inst_idx := LENGTH sp.cs_current_insts) =
     SOME (encode_hashmap_key kt v)` by gvs[eval_operand_def] >>
  `~(u with vs_inst_idx := LENGTH sp.cs_current_insts).vs_halted /\
   (u with vs_inst_idx := LENGTH sp.cs_current_insts).vs_current_bb = sp.cs_current_bb /\
   (u with vs_inst_idx := LENGTH sp.cs_current_insts).vs_inst_idx = LENGTH sp.cs_current_insts /\
   lo <= (u with vs_inst_idx := LENGTH sp.cs_current_insts).vs_alloca_next` by simp[] >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es
      (u with vs_inst_idx := LENGTH sp.cs_current_insts) /\
    ghost_inv_at (DF H) lo d cenv cx es HG tm
      (u with vs_inst_idx := LENGTH sp.cs_current_insts)` by metis_tac[] >>
  drule_all mapping_slot_full_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  suspend "join"
QED
Resume mapping_suffix_full_run[join]:
  rename1 `eval_operand slot t = SOME _` >>
  qexistsl_tac [`t`, `HG'`, `tm'`] >>
  simp[] >>
  conj_tac >- metis_tac[target_mapping_suffix_shape] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sp x` by metis_tac[compiler_ci_mono_not_fresh] >>
    qpat_assum `!x. not_fresh_at sp x ==> _` drule >>
    qpat_assum `!x. not_fresh_at sn x ==> FLOOKUP _ _ = _ /\ _` drule >>
    qpat_assum `!x. not_fresh_at sn x ==> lookup_var _ _ = _` drule >>
    gvs[compiler_ci_mono_not_fresh, lookup_var_def]) >>
  suspend "frames"
QED
Resume mapping_suffix_full_run[frames]:
  qmatch_asmsub_abbrev_tac `wb_frame cenv es es sp a t` >>
  `wb_frame cenv es es sn s a` by
    (irule wb_frame_readonly_tail >>
     qexistsl_tac [`sn`, `s`] >>
     simp[wb_frame_refl, Abbr `a`, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  `stmt_state_rel H0 ctx func cenv cx es s` by metis_tac[] >>
  `sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id` by
    gvs[ci_mono_def, cs_extends_def] >>
  conj_tac >- (irule wb_frame_trans >> simp[] >> conj_tac
    >- (qexistsl_tac [`es`, `sp`, `a`] >> simp[]) >> metis_tac[]) >>
  `!n b sz. local_region cenv es.scopes a n b sz <=>
     local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     simp[Abbr `a`, lookup_var_def] >>
     metis_tac[local_ptrs_reserved_def, lookup_var_def]) >>
  conj_tac >- (qpat_x_assum `pure_frame cenv func es sp a t` mp_tac >>
    simp[pure_frame_def, Abbr `a`] >> strip_tac >>
    conj_tac >- metis_tac[] >>
    rpt strip_tac >>
    qpat_x_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac >- (
    qpat_x_assum `ghost_kept_at lo cenv es sp HG tm a HG' tm'` mp_tac >>
    simp[ghost_kept_at_def] >> strip_tac >>
    simp[ghost_kept_at_def] >> rpt conj_tac
    >- metis_tac[compiler_ci_mono_not_fresh]
    >- (gvs[Abbr `a`] >> rpt strip_tac >>
        qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` irule >>
        conj_tac >- (qexistsl_tac [`aid`, `off`, `sz`] >> gvs[] >> first_assum ACCEPT_TAC) >> simp[])
    >- metis_tac[] >> metis_tac[]) >>
  conj_tac >- gvs[Abbr `a`] >>
  rpt strip_tac >>
  qpat_x_assum `!H. P H ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _` drule >>
  qpat_x_assum `!H. P H ==> gas_origin_ptr_path _ (a,HG,tm) _ _ /\ _` drule >>
  rpt strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`a`, `HG`, `tm`, `[]`, `OK t`, `HG'`, `tm'`] mp_tac) >>
  simp[]
QED
Finalise mapping_suffix_full_run

(* Apply twice: first to base/index, then to their combined frame and the
   mapping suffix. No effect-free premise is required of the index. *)
Theorem mapping_suffix_frames_join:
  wb_frame cenv es es1 sa s0 s1 /\
  wb_frame cenv es1 es2 sb s1 s2 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sb G1 tn1 s1 G2 tn2 /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  wb_frame cenv es es2 sa s0 s2 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> conj_tac >- metis_tac[wb_frame_trans] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s1 = SOME w` by gvs[wb_frame_def] >>
  `!n b sz. local_region cenv es1.scopes s1 n b sz <=>
      local_region cenv es.scopes s0 n b sz` by
    metis_tac[local_region_frame, local_region_frame_fwd] >>
  gvs[ghost_kept_at_def, wb_frame_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _` drule >>
      qpat_x_assum `!x. not_fresh_at sb x ==> FLOOKUP G2 x = _ /\ _` drule >>
      simp[])
  >- (rpt strip_tac >>
      `aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `!n b sz'. local_region cenv es1.scopes s1 n b sz' ==>
         off+sz <= b \/ b+sz' <= off` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
         simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC)
  >- metis_tac[] >> metis_tac[]
QED
