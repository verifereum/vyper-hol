(* The end of a ternary's selected arm: the arm's value is in op at u;
   ASSIGN it to the result variable and jump to the exit block, as one
   joint path with no GAS site, and give the ternary's root posts at one
   horizon H. *)
Theory bodyFullIfExpFinish
Ancestors
  bodySimFull fragGasOriginPtr fragGasSeqPtr fragGasEmitCtrl exprSimIfExp
  freshWrites exprSimProps loweringStateRelDefs allocaHistory codegenRel
  contextCodegenRel instMemFrontier memSafeRun ptrSafeRun ptrDiscipline
  venomInst venomExecSemantics venomExecProofs
  exprSimDefs exprSimMemDefs bodyPtrDefs bodyPtrIfExpAssignFrame
  loweringPosts exprLowering exprLoweringProps fragExec emitHelper
  emitHelperProps compileEnv allocaHistory stmtSimDefs vyperAST
  vyperInterpreter vyperState venomState finite_map arithmetic

(* H moved the arm's obligations: the root's vv_post needs the arm's
   value placed (vv_at) when it is not a word, and the root is pure only
   when the selected arm is. *)
Theorem ifexp_arm_finish_full:
  (* the root's premises *)
  stmt_state_rel H ctx func cenv cx es s0 /\ return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\ ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ dead_lo_ok H D lo cenv cx /\
  (* the condition's posts at tt *)
  expr_post H ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  s0.vs_alloca_next <= tt.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (* the selected arm's posts at u, from the jump to its block *)
  stmt_state_rel H ctx func cenv cx es1 (jump_to lbl tt) /\
  read_result cx tv ee = (INL v,ee) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  expr_post H ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  (~is_word_type t ==>
   vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  expr_store_bound cx t v op u /\
  u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn u /\
  ptr_val_ok cx t v op G tn u /\
  (~is_word_type t ==>
   !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G u) /\
  (~is_word_type t ==>
   !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op u = SOME w ==>
          type_memory_size rt = 0 \/
          w2n w + type_memory_size rt <= u.vs_alloca_next) /\
  ghost_kept_at lo cenv es1 sc G1 tn1 (jump_to lbl tt) G tn /\
  (* the layout *)
  expr_type e = t /\ post_value_type cenv e = t /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func ==>
  ?z Gz tf.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (u, G, tn) [] (OK z, Gz, tf) /\
    vv_post H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
    vv_store_bound cx (expr_type (IfExp t c a b))
      (lowered_value_type cenv (IfExp t c a b)) ee tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee Gz tf z /\
    ptr_vv_ok cx (post_value_type cenv (IfExp t c a b)) tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) ee Gz tf z /\
    (~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) (Var rv) Gz z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tf
Proof
  strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  `(!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
   (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> x <> rv)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qabbrev_tac `i0 = mk_inst sd.cs_next_id ASSIGN [op] [rv]` >>
  qabbrev_tac `u1 = update_var rv w u` >>
  qabbrev_tac `k = LENGTH sy.cs_current_insts` >>
  `u1.vs_allocas = u.vs_allocas /\ u1.vs_current_bb = u.vs_current_bb /\
   u1.vs_inst_idx = u.vs_inst_idx /\ ~u1.vs_halted /\
   u1.vs_alloca_next = u.vs_alloca_next /\ lookup_var rv u1 = SOME w` by
    simp[Abbr `u1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  (* the code: ASSIGN then JMP at the end of sd's block *)
  `sy.cs_blocks = sd.cs_blocks /\ sy.cs_current_bb = sd.cs_current_bb /\
   sy.cs_current_insts = sd.cs_current_insts ++ [i0]` by
    (simp[Abbr `i0`] >> metis_tac[emit_inst_extends]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb u.vs_inst_idx = SOME i0` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base i0 u = OK u1` by
    simp[Abbr `i0`, Abbr `u1`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure1_def, comp_bind_def, comp_return_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i0 u` by
    (simp[Abbr `i0`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
          comp_bind_def, comp_return_def, update_var_def, allocas_from_def, Abbr `u1`]) >>
  `inst_mem_below_frontier i0 u` by
    (irule below_frontier_no_ranges >> simp[Abbr `i0`, mk_inst_def]) >>
  `inst_dload_in_section i0 u` by
    simp[Abbr `i0`, inst_dload_in_section_def, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tn) []
     (OK (u1 with vs_inst_idx := k), step_prov PG G i0 u1,
      step_taint i0 u u1 tn)` by
    (`~is_terminator i0.inst_opcode /\ i0.inst_opcode <> INVOKE /\
      i0.inst_opcode <> GAS` by simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
     `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     mp_tac (Q.INST [`s` |-> `u`, `i` |-> `i0`, `u` |-> `u1`]
               straight_line_origin_ptr_edge) >>
     impl_tac >- simp[] >>
     simp[Abbr `k`, ADD1]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (u1 with vs_inst_idx := k, step_prov PG G i0 u1, step_taint i0 u u1 tn) []
     (OK (jump_to xl (u1 with vs_inst_idx := k)), step_prov PG G i0 u1,
      step_taint i0 u u1 tn)` by
    (irule emit_jmp_origin_ptr >> simp[Abbr `k`] >>
     gvs[allocas_from_def, Abbr `u1`, update_var_def] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`sy`, `sz`] >> gvs[]) >>
  qexistsl_tac [`jump_to xl (u1 with vs_inst_idx := k)`,
                `step_prov PG G i0 u1`, `step_taint i0 u u1 tn`] >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >> simp[]) >>
  (* the root's value post *)
  conj_tac
  >- (simp[Abbr `u1`] >>
      irule (SRULE [vyperASTTheory.expr_type_def]
        (Q.INST [`e` |-> `IfExp t c a b`] ifexp_root_vv_post_of_expr_post_read)) >>
      conj_tac
      >- (strip_tac >>
          `vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u`
            by fs[] >>
          `sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
          qpat_x_assum `local_ptrs_reserved cenv sa` mp_tac >>
          qpat_x_assum `!x. not_fresh_at sa x ==> x <> rv` mp_tac >>
          qpat_x_assum `sa.cs_next_id <= sc.cs_next_id` mp_tac >>
          qpat_x_assum `sd.cs_next_id <= sb.cs_next_id` mp_tac >>
          qpat_x_assum `eval_operand op u = SOME w` mp_tac >>
          qpat_x_assum `vv_at cenv cx t sc sd ee tv _ u` mp_tac >>
          rpt (pop_assum kall_tac) >> rpt strip_tac >>
          qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
          `ss.vs_allocas = u.vs_allocas /\ lookup_var rv ss = SOME w /\
           (!x. x <> rv ==> lookup_var x ss = lookup_var x u)` by
            simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
                 FLOOKUP_UPDATE] >>
          `!n b sz. local_region cenv ee.scopes ss n b sz <=>
                    local_region cenv ee.scopes u n b sz` by
            (rpt gen_tac >> simp[local_region_def] >> eq_tac >> rpt strip_tac >>
             fs[local_ptrs_reserved_def] >> metis_tac[]) >>
          qpat_x_assum `vv_at _ _ _ _ _ _ _ _ u` mp_tac >>
          simp[vv_at_def, contextTheory.mk_ptr_def, eval_operand_def] >>
          rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
          >~ [`FLOOKUP u.vs_allocas aid = SOME _`]
          >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
              `sa.cs_next_id <= aid /\ aid < sb.cs_next_id` by decide_tac >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
          disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qexists_tac `v` >> simp[] >>
      irule expr_post_ifexp >>
      `~not_fresh_at sa rv` by metis_tac[] >> simp[] >>
      qexistsl_tac [`op`, `cop`, `e`, `es1`, `lbl`, `s1`, `sc`, `sd`, `tt`, `v1`] >>
      simp[]) >>
  (* the store bound *)
  conj_tac
  >- (Cases_on `is_word_type t`
      >- simp[expr_type_def, vv_store_bound_stack_word] >>
      gvs[vv_store_bound_def, expr_type_def, lowered_value_type_def,
          contextTheory.mk_ptr_def, jump_to_def, Abbr `u1`, update_var_def,
          eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
          expr_store_bound_def] >> metis_tac[]) >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (irule alloca_history_jump >> simp[jump_to_def] >>
      qexists_tac `u` >> simp[]) >>
  conj_tac >- simp[jump_to_def] >>
  (* the ghosts after the ASSIGN *)
  `ghost_inv_at D lo d cenv cx ee (step_prov PG G i0 u1) (step_taint i0 u u1 tn) u1` by
    (simp[Abbr `i0`, Abbr `u1`] >> irule assign_ghost_inv_at >> simp[] >>
     metis_tac[]) >>
  conj_tac
  >- (`jump_to xl (u1 with vs_inst_idx := k) = jump_to xl u1` by
        simp[jump_to_def] >>
      pop_assum SUBST1_TAC >>
      `ee with gas_obs := ee.gas_obs = ee` by
        simp[evaluation_state_component_equality] >>
      mp_tac (Q.INST [`es` |-> `ee`, `gs` |-> `ee.gas_obs`, `l` |-> `xl`,
                      `s` |-> `u1`, `G` |-> `step_prov PG G i0 u1`,
                      `tn` |-> `step_taint i0 u u1 tn`] ghost_inv_at_jump_to) >>
      simp[]) >>
  conj_tac
  >- (drule_all assign_ptr_val_ok >>
      disch_then (qspecl_then [`rv`, `sd.cs_next_id`, `PG`] mp_tac) >>
      Cases_on `is_word_type t` >>
      simp[Abbr `i0`, Abbr `u1`, post_value_type_def, expr_type_def,
           ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def,
           contextTheory.mk_ptr_def, jump_to_def, eval_operand_def,
           lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  conj_tac
  >- (strip_tac >>
      `ptr_buf_ok cenv (IfExp t c a b) op G u` by
        (first_x_assum irule >> simp[lowered_value_type_def, expr_type_def]) >>
      drule_all ifexp_assign_ptr_buf_ok >>
      disch_then (qspecl_then [`rv`, `sd.cs_next_id`, `PG`] mp_tac) >>
      simp[Abbr `i0`, Abbr `u1`, ptr_buf_ok_def, jump_to_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  (* the root's kept ghosts: the condition's, then the arm's *)
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (`local_ptrs_rel func cenv es.scopes s0` by
       fs[stmt_state_rel_def, state_rel_def] >>
     `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x (jump_to lbl tt) = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP (jump_to lbl tt).vs_allocas aid = SOME b)` by
       fs[expr_post_def, jump_to_def, lookup_var_def] >>
     `!n b sz. local_region cenv es.scopes s0 n b sz <=>
               local_region cenv es1.scopes (jump_to lbl tt) n b sz` by
       (qx_genl_tac [`n0`, `b0`, `z0`] >> eq_tac >> strip_tac
        >- (qspecl_then [`cenv`, `es.scopes`, `sa`, `es1.scopes`, `s0`,
                         `jump_to lbl tt`, `n0`, `b0`, `z0`] mp_tac
              local_region_frame_fwd >>
            asm_simp_tac std_ss [])
        >- (qspecl_then [`func`, `cenv`, `es.scopes`, `s0`, `sa`, `es1.scopes`,
                         `jump_to lbl tt`, `n0`, `b0`, `z0`] mp_tac
              local_region_frame >>
            asm_simp_tac std_ss [])) >>
     `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
       decide_tac >>
     qpat_x_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
     qpat_x_assum `ghost_kept_at lo cenv es1 sc G1 tn1 (jump_to lbl tt) G tn`
       mp_tac >>
     qpat_x_assum `!n b sz. local_region _ _ s0 _ _ _ <=> _` mp_tac >>
     qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` mp_tac >>
     qpat_x_assum `sa.cs_next_var <= sc.cs_next_var` mp_tac >>
     qpat_x_assum `sa.cs_next_id <= sc.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >>
     qabbrev_tac `t1 = jump_to lbl tt` >>
     simp[ghost_kept_at_def] >> rpt strip_tac
     >- (`not_fresh_at sc x` by metis_tac[not_fresh_at_mono] >>
         res_tac >> gvs[])
     >- (`not_fresh_at sc x` by metis_tac[not_fresh_at_mono] >>
         res_tac >> gvs[])
     >- (`aid < sc.cs_next_id` by decide_tac >>
         `FLOOKUP t1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
         `i IN tn1.t_mem` by
           (qpat_x_assum `!aid off sz i. FLOOKUP t1.vs_allocas aid = _ /\ _ ==> _`
              irule >> metis_tac[]) >>
         qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
           irule >> metis_tac[]) >>
     metis_tac[]) >>
  simp[Abbr `i0`, Abbr `u1`] >> irule assign_ghost_kept_at >> simp[] >>
  metis_tac[]
QED
