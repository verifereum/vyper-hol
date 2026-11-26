(* Choose the reached branch without inspecting or reconstructing its launch. *)
Theory bodyECArithStageSelectMods
Ancestors
  bodyECArithSuccessRunMods bodyECArithSuccessVVMods gasExplicitSites
Libs monadsyntax

Theorem ec_arith_stage_select_mods:
  let staged =
    ?sm res out_alloc gi ci ai gv cv src dst wi wo bb u Gu tnu.
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
          emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
      vv = StackValue a (Var dst) /\
      gi = mk_inst sm.cs_next_id GAS [] [gv] /\
      ci = mk_inst (sm.cs_next_id+1) STATICCALL
        [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
      ai = mk_inst (sm.cs_next_id+2) ASSERT [Var cv] [] /\
      emitted_insts sm sb = [gi;ci;ai] /\
      ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func u /\
      lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions) /\
      (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx /\
      src <> gv /\ dst <> gv /\ dst <> cv /\
      not_fresh_at sm src /\ not_fresh_at sm dst /\
      ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
      s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
      local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv sm /\
      (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
      (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
      eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
      w2n wi + w2n an <= u.vs_alloca_next /\ w2n wo + 64 <= u.vs_alloca_next /\
      lo <= w2n wo /\ t2.vs_alloca_next <= u.vs_alloca_next /\
      allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u 64 /\
      (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
      mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n p) t2.vs_memory /\
      mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n p+32) t2.vs_memory /\
      (if bt = ECAdd then
         mem_word_at (w2n wi+64) u.vs_memory = mem_word_at (w2n q) t2.vs_memory /\
         mem_word_at (w2n wi+96) u.vs_memory = mem_word_at (w2n q+32) t2.vs_memory
       else mem_word_at (w2n wi+64) u.vs_memory = q) /\
      es2.outcomes = SOME u.vs_outcomes /\
      MEM (mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
      FLOOKUP u.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64) /\
      s2.cs_next_id <= out_alloc.cs_next_id /\ out_alloc.cs_next_id < sb.cs_next_id /\
      (!name b sz. local_region cenv es2.scopes u name b sz ==>
        regions_disjoint (w2n wo) 64 b sz) /\
      (!aid b sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n wo) 64 b sz) /\
      (cenv.ce_is_ctor ==> !name tv iv off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
        regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
      wb_frame cenv es2 es2 s2 t2 u /\ pure_frame cenv func es2 s2 t2 u /\
      immutable_frame_mods func cenv cx es2 u /\ local_ptrs_rel func cenv es2.scopes u /\
      ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu /\
      !H. valid_horizon cx st0 H es2.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t2,G2,tn2) [] (OK u,Gu,tnu) /\
        stmt_state_rel H ctx func cenv cx es2 u /\
        ghost_inv_at_mods (DF H) lo d cenv cx es2 Gu tnu u /\
        stor_taint_ok_at (DF H) tnu u
  in
    ((bt = ECAdd ==> staged) /\ (bt = ECMul ==> staged) /\ (bt = ECAdd \/ bt = ECMul)) ==>
    ((bt = ECAdd /\ staged) \/ (bt = ECMul /\ staged))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "add")
    (CONJUNCTS_THEN2 (mk_asm "mul") DISJ_CASES_TAC))
  >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      asm "add" irule >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      asm "mul" irule >> first_assum ACCEPT_TAC)
QED
