(* The optional mapping-key prehash is read-only, including for every
   qualified immutable view of the linked unit. *)
Theory bodyMapKeyPrefixMods
Ancestors
  bodyPtrPopTargetSimMapKeyRun bodyFullUnwrapRun bodyFullPostsMods
  bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs ptrDiscipline
  fragGasCopySeqLiftProps fragGasSeqPtr fragExecMem instMemFrontier
  exprSimMapKey exprSimHashBoundary loweringPosts compileEnv exprLoweringProps
  loweringStateRelDefs unitTransformDefs memSafeRun venomMemDefs
  valueEncodingProps contextCodegenRel codegenRel
  venomExecSemantics venomState venomInst words finite_map pred_set rich_list list

Theorem key_mem_checked[local]:
  ALL_DISTINCT [x;p;l;h] /\
  eval_operand (Var x) s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w n /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\
  b+32+n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst ia ADD [Var x;Lit 32w] [p];
     mk_inst il MLOAD [Var x] [l];
     mk_inst ih SHA3 [Var p;Var l] [h]] s
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `mload b s = n2w n` by gvs[mem_word_at_eq_mload] >>
  gvs[ALL_DISTINCT, eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
    inst_dload_in_section_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def, mk_inst_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
    eval_operand_def, lookup_var_def, update_var_def,
    ALL_DISTINCT, word_add_n2w, FLOOKUP_UPDATE,
    memory_range_of_operands_def, mload_def] >>
  gvs[mload_def]
QED

val key_input = ``
  (if is_bytestring_type kt then compile_keccak256_key key F sa
   else (key,sa)) = (hashed,sb) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
        op_taint tn key = {} /\ op_prov G key = NONE)``;

val key_output = ``
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand hashed t = SOME (encode_hashmap_key kt v) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    op_taint tm hashed = {} /\ op_prov HG hashed = NONE /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x))``;

Theorem checked_key_run[local]:
  ^key_input ==>
  ?t HG tm. ^key_output /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!D lo. allocas_from lo s ==>
      inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s HG tm)
Proof
  strip_tac >> Cases_on `is_bytestring_type kt` >> gvs[]
  >- (drule_at (Pat `compile_keccak256_key _ _ _ = _`)
        compile_keccak256_key_run >>
      disch_then (qspecl_then [`s`, `bs`, `b`] mp_tac) >>
      simp[] >> strip_tac >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
      `b+32+LENGTH bs <= base'+cap /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)` by gvs[] >>
      drule_all map_key_inst_seq >>
      disch_then (qspecl_then [`ARB`, `func`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
      drule map_key_shape >> strip_tac >>
      conj_tac
      >- (simp[] >> irule key_mem_checked >> simp[] >>
          qexistsl_tac [`b`, `LENGTH bs`] >> simp[] >>
          gvs[ALL_DISTINCT] >> metis_tac[]) >>
      rpt strip_tac >> irule inst_seq_ptr_lower_bound_transport >>
      simp[mk_inst_def] >> qexists_tac `0` >> simp[] >>
      drule_all map_key_inst_seq >>
      disch_then (qspecl_then [`D`, `func`, `PG`] strip_assume_tac) >>
      gvs[GSYM mk_inst_def] >>
      metis_tac[inst_seq_ptr_ghost_unique]) >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def,
       run_inst_seq_mem_ok_def]
QED

Theorem key_prefix_code[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sa
   else (key,sa)) = (hashed,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)
Proof
  Cases_on `is_bytestring_type kt` >> simp[] >> strip_tac
  >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
      strip_tac >> conj_tac >- fs[same_blocks_def] >>
      drule map_key_shape >> strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
  gvs[emitted_insts_def]
QED

Theorem key_ghost_readonly_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x)) /\
  tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_immutables = s.vs_immutables ==>
  ghost_inv_at_mods D lo d cenv cx es HG tm u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers HG tm p u sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem key_immutable_readonly_mods[local]:
  immutable_frame_mods func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next ==>
  immutable_frame_mods func cenv cx es u
Proof
  strip_tac >> simp[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def] >>
      first_assum ACCEPT_TAC) >>
  fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`, `es`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  qmatch_asmsub_rename_tac `local_region (cenv with ce_module := src) _ _ _ _ _` >>
  `local_region (cenv with ce_module := src) es.scopes u id b sz <=>
   local_region (cenv with ce_module := src) es.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >>
     metis_tac[local_ptrs_reserved_def]) >> gs[]
QED

Theorem mapping_key_prefix_full_run_mods:
  ^key_input /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. P H ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm. ^key_output /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),HG,tm) /\
      stmt_state_rel H ctx func cenv cx es
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      immutable_frame_mods func cenv cx es
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      ghost_inv_at_mods (DF H) lo d cenv cx es HG tm
        (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all checked_key_run >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `HG`, `tm`] >> simp[] >>
  conj_tac >- gvs[ghost_kept_at_def] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. P H ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  drule_then strip_assume_tac key_prefix_code >>
  conj_tac
  >- (irule emitted_origin_ptr_path >> conj_tac >- simp[] >>
      qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[] >>
      rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
      qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _` mp_tac >>
      qpat_x_assum `emitted_insts sa sb = _`
        (fn th => pure_rewrite_tac[th, EVERY_APPEND, EVERY_DEF]) >> simp[]) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule hash_readonly_state_rel >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  conj_tac
  >- (irule key_immutable_readonly_mods >>
      qexistsl_tac [`s`, `sa`] >> fs[lookup_var_def]) >>
  irule key_ghost_readonly_mods >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`] >> fs[lookup_var_def]
QED
