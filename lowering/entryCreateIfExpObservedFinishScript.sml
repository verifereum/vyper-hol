(* The selected materialization, finish path and VV post share their handoff. *)
Theory entryCreateIfExpObservedFinish
Ancestors
  entryCreateIfExpAdmin entryCreatePathScope entryCreateFocusSpec
  bodyFullIfExpPrepare exprSimDefs loweringPosts vyperAST vyperState
  vyperStorageFootprint context fragExec venomState

Theorem ifexp_materialized_finish_handoff:
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
     expr_post H ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
     stmt_state_rel H ctx func cenv cx es1 (jump_to lbl tt) /\
     expr_post H ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn u) /\
  s0.vs_alloca_next <= tt.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  read_result cx tv ee = (INL v,ee) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  (~is_word_type t ==>
   vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~is_word_type t ==>
   vv_place_ptr cenv cx ee u tv (LocatedValue t (mk_ptr op LocMemory))) /\
  (!v. tv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
    vv_own cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  expr_store_bound cx t v op u /\ create_operand_at sd u /\ ~u.vs_halted /\
  alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next /\
  ptr_val_ok cx t v op G tn u /\
  (~is_word_type t ==>
   !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G u) /\
  (~is_word_type t ==>
   !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op u = SOME w ==>
          type_memory_size rt = 0 \/
          w2n w + type_memory_size rt <= u.vs_alloca_next) /\
  ghost_kept_at lo cenv es1 sc G1 tn1 (jump_to lbl tt) G tn /\
  expr_type e = t /\ post_value_type cenv e = t /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  sd.cs_current_bb <> xl /\ sz.cs_next_id <= sb.cs_next_id /\
  sm.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= sb.cs_next_id /\
  (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids sm sd) /\
  create_operand_full_scope sm sd explicit ctx func j [] (OK u) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  vv = (if is_word_type t then StackValue t (Var rv)
        else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,G,tn)) ==>
  ?fin Gf tf.
    create_operand_full_scope sd sb explicit ctx func u [] (OK fin) /\
    create_operand_full_scope sm sb explicit ctx func j [] (OK fin) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,G,tn) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK fin,Gf,tf) /\
      create_operand_vv_post (DF,lo,d,ctx,func) cenv cx (IfExp t c a b)
        (es,sa,sb,s0,vv,G0,tn0) H (INL tv) (ee with gas_obs := []) Gf tf fin /\
      create_operand_at sb fin
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by metis_tac[storage_trace_domain_def] >>
  mp_tac (Q.INST [`tr` |-> `ee.storage_trace`,
    `finish_at` |-> `\fin. create_operand_full_scope sd sb explicit ctx func u [] (OK fin)`]
    ifexp_arm_finish_vv_family_observed) >> BETA_TAC >>
  impl_tac
  >- (fs[create_operand_at_def] >> rpt strip_tac >>
      irule ifexp_finish_scope >> simp[create_operand_at_def] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`fin`,`Gf`,`tf`] strip_assume_tac) >>
  `create_operand_full_scope sd sb explicit ctx func u [] (OK fin)` by
    (first_x_assum irule >> qexists `H0` >> simp[]) >>
  qexistsl [`fin`,`Gf`,`tf`] >> simp[] >>
  conj_tac
  >- (drule_all create_operand_full_scope_prepend >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ (u,G,tn) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[create_operand_vv_post_def, create_operand_at_def, post_value_type_def, expr_type_def] >>
  Cases_on `is_word_type t` >> gvs[post_value_type_def, expr_type_def]
QED
