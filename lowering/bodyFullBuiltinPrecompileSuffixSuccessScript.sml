Theory bodyFullBuiltinPrecompileSuffixSuccess
Ancestors
  bodyFullBuiltinPrecompileSuffixPath bodyFullBuiltinPrecompileSuffixFrame
  bodySimFull exprSimPrecompiles exprLoweringProps exprSimRawCallCalldata
  vyperStorageFootprint bodyPtrDefs finite_map list rich_list

Theorem precompile_suffix_success_full_family:
  ((addr = 1w /\ an = 128w /\ rn = 32w) \/
   (addr = 6w /\ an = 128w /\ rn = 64w) \/
   (addr = 7w /\ an = 96w /\ rn = 64w)) /\
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit addr; Var src; Lit an; Var dst; Lit rn];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  emitted_insts sm sb = [gi;ci;ai] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s addr 0w wi an T) /\
  precompile_result (venom_call_request s addr 0w wi an T).cr_target
    (venom_call_request s addr 0w wi an T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  src <> gv /\ dst <> gv /\ dst <> cv /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (lo <> 0 ==> !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\
  w2n wi + w2n an <= s.vs_alloca_next /\
  w2n wo + w2n rn <= s.vs_alloca_next /\ lo <= w2n wo /\
  (addr <> 1w ==> 64 <= LENGTH data) /\
  (!H. valid_horizon cx st0 H trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    stmt_state_rel H ctx func cenv cx es s /\
    local_ptrs_rel func cenv es.scopes s /\
    ptr_covers G tn src s (w2n an) /\ ptr_covers G tn dst s (w2n rn) /\
    allocas_from lo s /\
    tn.t_stor SUBSET (DF H).d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET (DF H).d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address) /\
    (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tn.t_mem) /\
    (addr = 1w ==> !i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      regions_disjoint (w2n wo) (w2n rn) b sz) /\
    (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n wo) (w2n rn) b sz) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
      regions_disjoint (w2n wo) (w2n rn) off (type_memory_size tv))) ==>
  ?t G' tn'. t = (q with vs_inst_idx := s.vs_inst_idx + 3) /\
    G' = G2 /\ tn' = tn2 /\
    (!H. valid_horizon cx st0 H trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F] (OK t,G',tn') /\
      ghost_inv_at (DF H) lo d cenv cx
        (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t /\
      ghost_kept_at lo cenv es sf G tn s G' tn' /\
      stmt_state_rel H ctx func cenv cx
        (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
      wb_frame cenv es (es with outcomes := SOME (DROP 1 s.vs_outcomes)) sf s t /\
      ptr_covers G' tn' dst t (w2n rn) /\
      (!i. w2n wo <= i /\ i < w2n wo + w2n rn ==> i NOTIN tn'.t_mem) /\
      eval_operand (Var dst) t = SOME wo /\
      t.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n rn) data) s).vs_memory /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_immutables = s.vs_immutables /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s))
Proof
  strip_tac >>
  qexistsl [`q with vs_inst_idx := s.vs_inst_idx + 3`, `G2`, `tn2`] >>
  simp[NoAsms] >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F]
     (OK (q with vs_inst_idx := s.vs_inst_idx + 3),G2,tn2)` by
    (irule precompile_suffix_origin_path >> metis_tac[]) >>
  drule_all precompile_suffix_ghost_output_at >> strip_tac >>
  drule_all computed_suffix_preserves >> strip_tac >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx]
QED
