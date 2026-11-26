(* The selected IfExp's ASSIGN/JMP suffix. No source reads occur here. *)
Theory bodyIfExpTailMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodyPtrIfExpAssignFrame
  bodyPtrHashBuiltinsGhostCompose wordArgsPtr exprSimIfExp exprSimCopy
  fragGasOriginPtr fragGasSeqPtr fragGasEmitCtrl instMemFrontier ptrDiscipline
  ptrSafeRun memSafeRun venomExecProofs contextCodegenRel context
  bodySimFull bodyPtrDefs allocaHistory loweringPosts loweringStateRelDefs
  exprSimDefs exprSimMemDefs exprLoweringProps exprLowering compileEnv
  fragExec emitHelperProps unitTransformDefs codegenRel
  venomExecSemantics venomInst venomState vyperState vyperAST finite_map arithmetic

Theorem ifexp_tail_path[local]:
  eval_operand op u = SOME w /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~u.vs_halted /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) []
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)),
     step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u),
     step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn)
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst sd.cs_next_id ASSIGN [op] [rv]` >>
  qabbrev_tac `v = update_var rv w u` >>
  qabbrev_tac `k = LENGTH sy.cs_current_insts` >>
  `sy.cs_blocks = sd.cs_blocks /\ sy.cs_current_bb = sd.cs_current_bb /\
   sy.cs_current_insts = sd.cs_current_insts ++ [i]` by
    (qpat_assum `emit_inst ASSIGN _ _ _ = _` (mp_then Any mp_tac emit_inst_extends) >>
     simp[Abbr `i`]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb u.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base i u = OK v` by
    simp[Abbr `i`, Abbr `v`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure1_def, comp_bind_def, comp_return_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i u` by
    (simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
          comp_bind_def, comp_return_def, update_var_def, allocas_from_def, Abbr `v`]) >>
  `inst_mem_below_frontier i u` by
    (irule below_frontier_no_ranges >> simp[Abbr `i`, mk_inst_def]) >>
  `inst_dload_in_section i u` by simp[Abbr `i`, inst_dload_in_section_def, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tn) []
     (OK (v with vs_inst_idx := k),step_prov PG G i v,step_taint i u v tn)` by
    (`~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by
       simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
     `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     mp_tac (Q.INST [`s` |-> `u`, `i` |-> `i`, `u` |-> `v`]
               straight_line_origin_ptr_edge) >>
     (impl_tac >- simp[Abbr `i`, dalloca_no_wrap_def, mk_inst_def]) >>
     simp[Abbr `k`, ADD1]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (v with vs_inst_idx := k,step_prov PG G i v,step_taint i u v tn) []
     (OK (jump_to xl (v with vs_inst_idx := k)),step_prov PG G i v,step_taint i u v tn)` by
    (irule emit_jmp_origin_ptr >>
     simp[Abbr `k`, Abbr `v`, allocas_from_def, allocas_below_fmp_def, update_var_def] >>
     conj_tac >- fs[allocas_below_fmp_def] >>
     conj_tac >- fs[allocas_from_def] >>
     qexistsl [`sy`,`sz`] >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem ifexp_tail_immutable_frame[local]:
  immutable_frame_mods func ce cx ee u /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> x <> rv) ==>
  immutable_frame_mods func ce cx ee (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >> qabbrev_tac `z = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `z.vs_memory = u.vs_memory /\ z.vs_data_section = u.vs_data_section /\
   z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next` by
    simp[Abbr `z`, jump_to_def, update_var_def] >>
  `!src n b sz. local_region (ce with ce_module := src) ee.scopes z n b sz ==>
    local_region (ce with ce_module := src) ee.scopes u n b sz` by
    (rpt gen_tac >> simp[local_region_def, Abbr `z`, jump_to_def, update_var_def,
                          lookup_var_def, AllCaseEqs()] >>
     rpt strip_tac >>
     `p <> rv` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[FLOOKUP_UPDATE]) >>
  fs[immutable_frame_mods_def] >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ u` mp_tac >>
      simp[immutables_rel_mods_def, immutables_rel_def]) >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl [`u`,`ee`] >>
  simp[] >> metis_tac[]
QED

Theorem ifexp_assign_ghost_inv_mods[local]:
  eval_operand src s = SOME w /\ ghost_inv_at_mods D lo d cenv cx es G tn s /\
  (!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> x <> out) ==>
  ghost_inv_at_mods D lo d cenv cx es
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
    (update_var out w s)
Proof
  strip_tac >> drule assign_taint >> simp[] >> strip_tac >>
  fs[ghost_inv_at_mods_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
      conj_tac >- (drule_all assign_other_covers >> simp[assign_taint]) >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      first_x_assum drule_all >> simp[lookup_var_def]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >>
      `x <> out` by metis_tac[] >> conj_tac
      >- gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      drule_all assign_other_covers >> simp[assign_taint]) >>
  conj_tac
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >>
      simp[op_taint_def, FLOOKUP_UPDATE] >> gvs[op_taint_def]) >>
  gvs[stor_taint_ok_at_def, update_var_def, allocas_from_def] >>
  rpt strip_tac >> gvs[assign_other_prov, op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ifexp_jump_ghost_inv_mods[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn (jump_to xl (s with vs_inst_idx := k)) <=>
  ghost_inv_at_mods D lo d ce cx ee G tn s
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem ifexp_tail_owned[local]:
  vv_own ce cx ty sc sd es tv (LocatedValue ty (mk_ptr op LocMemory)) u /\
  eval_operand op u = SOME w /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_id <= sc.cs_next_id /\ sd.cs_next_id <= sb.cs_next_id ==>
  vv_own ce cx ty sa sb es tv (LocatedValue ty (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qabbrev_tac `z = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `z.vs_allocas = u.vs_allocas /\ lookup_var rv z = SOME w` by
    simp[Abbr `z`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u` by
    (rpt strip_tac >> `x <> rv` by metis_tac[] >>
     simp[Abbr `z`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `!n b sz. local_region ce es.scopes z n b sz <=>
            local_region ce es.scopes u n b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `sa` >> simp[]) >>
  qpat_x_assum `vv_own _ _ _ sc sd _ _ _ u` mp_tac >>
  simp[vv_own_def, mk_ptr_def, eval_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[] >>
  disj1_tac >> qexistsl [`aid`,`b`,`sz`] >>
  `sa.cs_next_id <= aid /\ aid < sb.cs_next_id` by decide_tac >>
  simp[] >> first_assum ACCEPT_TAC
QED

(* The ordinary VV post is usable here because this suffix's output is never
   LocCode, and conditional_result cannot return an immutable place. *)
Theorem ifexp_tail_vv_post[local]:
  expr_post H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee v (Var rv) z /\
  immutable_frame_mods func cenv cx ee z /\
  read_result cx tv ee = (INL v,ee) /\
  (!src id ps. tv <> PlaceR (ImmutablePlace src id ps)) /\
  (~is_word_type t ==>
    vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr (Var rv) LocMemory)) z) /\
  (~is_word_type t ==>
    vv_place_ptr cenv cx ee z tv (LocatedValue t (mk_ptr (Var rv) LocMemory))) ==>
  vv_post_mods H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory)) z
Proof
  strip_tac >>
  `vv_post H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
     (if is_word_type t then StackValue t (Var rv)
      else LocatedValue t (mk_ptr (Var rv) LocMemory)) z` by
    (irule (SIMP_RULE bool_ss [expr_type_def, post_value_type_def]
       (Q.INST [`e` |-> `IfExp t c a b`] ifexp_root_vv_post_of_expr_post_read)) >>
     simp[] >> qexists `v` >> simp[]) >>
  `!p. vv_place_ptr_mods cenv cx ee z tv p = vv_place_ptr cenv cx ee z tv p` by
    (gen_tac >> Cases_on `tv` >> simp[vv_place_ptr_mods_def] >>
     Cases_on `p` >> Cases_on `p'` >> fs[vv_place_ptr_mods_def]) >>
  Cases_on `is_word_type t` >>
  fs[vv_post_mods_def, vv_post_def, vv_holds_mods_def, mk_ptr_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem ifexp_tail_scalar_posts[local]:
  eval_operand op u = SOME w /\ ptr_val_ok cx t v op G tn u /\
  read_result cx tv ee = (INL v,ee) /\
  expr_store_bound cx t v op u /\
  (~is_word_type t ==>
    !rt. evaluate_type (get_tenv cx) t = SOME rt ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= u.vs_alloca_next) /\
  (~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) op G u) ==>
  let z = jump_to xl (update_var rv w u with vs_inst_idx := k);
      Gz = step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u);
      tf = step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn;
      vv = if is_word_type t then StackValue t (Var rv)
           else LocatedValue t (mk_ptr (Var rv) LocMemory)
  in
    vv_store_bound cx t (lowered_value_type cenv (IfExp t c a b)) ee tv vv z /\
    ptr_vv_ok cx t tv vv ee Gz tf z /\
    (~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) (Var rv) Gz z)
Proof
  strip_tac >> simp[] >>
  `ptr_val_ok cx t v (Var rv)
     (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
     (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
     (update_var rv w u)` by (irule assign_ptr_val_ok >> simp[]) >>
  conj_tac
  >- (Cases_on `is_word_type t` >- simp[vv_store_bound_stack_word] >>
      gvs[vv_store_bound_def, lowered_value_type_def, expr_type_def, mk_ptr_def,
          jump_to_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, expr_store_bound_def]) >>
  reverse conj_tac
  >- (strip_tac >> `ptr_buf_ok cenv (IfExp t c a b) op G u` by simp[] >>
      drule_all ifexp_assign_ptr_buf_ok >>
      disch_then (qspecl_then [`rv`,`id`,`PG`] mp_tac) >>
      simp[ptr_buf_ok_def, jump_to_def, eval_operand_def, lookup_var_def]) >>
  Cases_on `is_word_type t`
  >- fs[ptr_vv_ok_def, ptr_val_ok_def] >>
  fs[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, mk_ptr_def,
     jump_to_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem ifexp_cond_kept[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sc G1 tn1 (jump_to lbl tt) G tn /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  expr_post H ctx func cenv cx c es sa s1 s0 mid cv cop tt /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >> irule ghost_kept_at_trans >>
  qexistsl [`G1`,`mid`,`jump_to lbl tt`,`sc`,`tn1`] >> simp[] >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
  simp[] >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP (jump_to lbl tt).vs_allocas aid = SOME b` by fs[expr_post_def, jump_to_def] >>
  simp[] >>
  `local_ptrs_rel func cenv es.scopes s0` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all hash_expr_post_local_regions >>
  simp[local_region_def, jump_to_def, lookup_var_def]
QED

Theorem ifexp_arm_finish_mods:
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     expr_post_mods H ctx func cenv cx c es sa s1 s0 mid cv cop tt /\
     expr_post_mods H ctx func cenv cx e mid sc sd (jump_to lbl tt) ee v op u /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u) /\
  s0.vs_alloca_next <= tt.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  read_result cx tv ee = (INL v,ee) /\
  (!src id ps. tv <> PlaceR (ImmutablePlace src id ps)) /\
  (~is_word_type t ==>
   vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~is_word_type t ==>
   vv_place_ptr cenv cx ee u tv (LocatedValue t (mk_ptr op LocMemory))) /\
  (!v'. tv = Value v' /\ ~is_word_type t /\ ~is_bytestring_type t ==>
    vv_own cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  expr_store_bound cx t v op u /\
  u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next /\
  ptr_val_ok cx t v op G tn u /\
  (~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) op G u) /\
  (~is_word_type t ==>
   !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op u = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= u.vs_alloca_next) /\
  ghost_kept_at lo cenv mid sc G1 tn1 (jump_to lbl tt) G tn /\
  expr_type e = t /\ post_value_type cenv e = t /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func ==>
  ?z Gz tf. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,Gz,tf) /\
    let vv = if is_word_type t then StackValue t (Var rv)
             else LocatedValue t (mk_ptr (Var rv) LocMemory)
    in
    vv_post_mods H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv vv z /\
    vv_store_bound cx t (lowered_value_type cenv (IfExp t c a b)) ee tv vv z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tf z /\
    ptr_vv_ok cx t tv vv ee Gz tf z /\
    (!v'. tv = Value v' /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own cenv cx t sa sb ee tv (LocatedValue t (mk_ptr (Var rv) LocMemory)) z) /\
    (~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) (Var rv) Gz z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tf
Proof
  strip_tac >> reverse (Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`)
  >- (qexistsl [`ARB`,`ARB`,`ARB`] >> fs[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `?w. eval_operand op u = SOME w` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `expr_post_mods H0 _ _ _ _ e _ _ _ _ _ _ _ u` mp_tac >>
     simp[NoAsms, expr_post_mods_def, expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexistsl
    [`jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)`,
     `step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u)`,
     `step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
  simp[expr_post_mods_def] >> strip_tac >>
  conj_tac
  >- (irule ifexp_tail_path >>
      `allocas_from lo u` by fs[ghost_inv_at_mods_def] >>
      simp[] >> qexists `sz` >> simp[]) >>
  `~not_fresh_at sa rv` by metis_tac[] >>
  simp[] >>
  conj_tac
  >- (irule ifexp_tail_vv_post >> simp[] >>
      conj_tac
      >- (strip_tac >> irule ifexp_place_ptr_root_var >>
          qpat_assum `eval_operand op u = SOME w` (irule_at Any) >>
          qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
          simp[] >> qexists `t` >> simp[]) >>
      conj_tac
      >- (strip_tac >> irule ifexp_vv_at_root_frame >>
          qpat_assum `eval_operand op u = SOME w` (irule_at Any) >>
          qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
          simp[] >> qexistsl [`sd`,`sc`] >> simp[] >> decide_tac) >>
      conj_tac
      >- (irule ifexp_tail_immutable_frame >> simp[] >> qexists `sa` >> simp[]) >>
      irule expr_post_ifexp >>
      qpat_assum `expr_post H _ _ _ _ c _ _ _ _ _ _ _ tt` (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ e _ _ _ _ _ _ _ u` (irule_at Any) >> simp[]) >>
  mp_tac (Q.INST [`id` |-> `sd.cs_next_id`, `k` |-> `LENGTH sy.cs_current_insts`,
                  `PG` |-> `PG`, `xl` |-> `xl`] ifexp_tail_scalar_posts) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!tl k. alloca_history func (jump_to tl (update_var rv w u with vs_inst_idx := k))` by
    (rpt gen_tac >> irule alloca_history_jump >>
     simp[jump_to_def, update_var_def] >> qexists `u` >> simp[]) >>
  `!tl k. allocas_below_fmp (jump_to tl (update_var rv w u with vs_inst_idx := k)) <=>
          allocas_below_fmp u` by simp[allocas_below_fmp_def, jump_to_def, update_var_def] >>
  simp[] >>
  `((jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)).vs_current_bb = xl) /\
   ((jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)).vs_inst_idx = 0) /\
   ((jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)).vs_alloca_next = u.vs_alloca_next)` by
     simp[jump_to_def, update_var_def] >>
  simp[ifexp_jump_ghost_inv_mods] >>
  conj_tac
  >- (irule ifexp_assign_ghost_inv_mods >> simp[] >>
      fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule ifexp_tail_owned >>
      qpat_assum `eval_operand op u = SOME w` (irule_at Any) >>
      qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
      simp[] >> qexistsl [`sd`,`sc`] >>
      `sa.cs_next_id <= sc.cs_next_id` by decide_tac >> gvs[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (drule_all ifexp_cond_kept >> simp[]) >>
  irule assign_ghost_kept_at >> simp[]
QED
