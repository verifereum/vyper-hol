(* Concat's linked operand loop, after scratch installation and before
   the length header is written. *)
Theory bodyConcatElementsMods
Ancestors
  bodyConcatHeadStepMods bodyConcatElementsFoldMods bodyConcatFrameLawsMods
  bodyConcatCutsMods gasOutcomeFullPostMods exprSimFullBundleProps
  valueEncodingProps vyperInterpreter vyperState venomState
  arithmetic words list finite_map pred_set

Theorem concat_elements_mods:
  !args P k DF lo d ctx shadow_ctx PG mods exps src tops func shadow_func cenv cx env st0
   es sa sb shadow_sa shadow_sb s0 G0 tn0 dv ov ow binst B bsz oinst.
    compile_concat compile_expr cenv args (Var dv) (concat_infos_mods args)
      (Var ov) sa = ((),sb) /\
    compile_concat compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args)
      (Var dv) (concat_infos_mods args) (Var ov) shadow_sa = ((),shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
    local_ptrs_reserved cenv sa /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
                 ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    (!e ee. MEM e args /\ expr_sim_inv_mods mods cenv cx env ee ==>
       expr_body_pre_mods mods cenv cx env e ee) /\
    body_exprs_full_ok_mods mods exps cx args /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var dv s0 = SOME (n2w (B+32)) /\ lookup_var ov s0 = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\ FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\ FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
    (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
    B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    B+bsz <= s0.vs_alloca_next /\ w2n ow+64 <= s0.vs_alloca_next /\
    allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\ lo <= B /\ lo <= w2n ow /\
    ptr_covers G0 tn0 dv s0 (bsz-32) /\ ptr_covers G0 tn0 ov s0 32 /\
    (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn0.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn0.t_mem) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32+P+SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
    32+concat_data_bound P (MAP expr_type args) <= bsz ==>
    gas_outcome_full_mods
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
      (\H res ee G tn t. ?vs. res = INL vs /\ ee.gas_obs = [] /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
         expr_sim_inv_mods mods cenv cx env ee /\
         stmt_state_rel H ctx func cenv cx ee t /\
         immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
         allocas_from lo t /\ lo <= t.vs_alloca_next /\
         B+bsz <= t.vs_alloca_next /\ w2n ow+64 <= t.vs_alloca_next /\
         return_buf_frame d cenv sb t /\
         ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
         MAP FDOM es.scopes = MAP FDOM ee.scopes /\
         (!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
            local_region cenv es.scopes s0 name lb lsz) /\
         LIST_REL (\e v. ?tv.
           evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)
           args vs /\
         lookup_var dv t = SOME (n2w (B+32)) /\ lookup_var ov t = SOME ow /\
         FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
         FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
         ptr_covers G tn dv t (bsz-32) /\ ptr_covers G tn ov t 32 /\
         not_fresh_at sb dv /\ not_fresh_at sb ov /\
         sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
         binst.inst_id < sb.cs_next_id /\ oinst.inst_id < sb.cs_next_id /\
         (!name lb lsz. local_region cenv ee.scopes t name lb lsz ==>
            (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
         32+k+LENGTH (FLAT (MAP concat_payload_mods vs)) <= bsz /\
         (!i. B+32 <= i /\ i < B+32+k+LENGTH (FLAT (MAP concat_payload_mods vs)) ==>
            i NOTIN tn.t_mem) /\
         (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
         mem_bytes_at (B+32) (k+LENGTH (FLAT (MAP concat_payload_mods vs))) t.vs_memory =
           mem_bytes_at (B+32) k s0.vs_memory ++ FLAT (MAP concat_payload_mods vs) /\
         mload (w2n ow) t = n2w (k+LENGTH (FLAT (MAP concat_payload_mods vs))) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t = SOME w) /\
         (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
         (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
            (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
            (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
               p+n <= lb \/ lb+lsz <= p) ==>
            mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
         locals_kept cenv es ee s0 t /\
         (~EXISTS expr_has_effect args ==>
           (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
              mem_bytes_at lb lsz t.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
           (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
              (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                 sa.cs_next_id <= inst.inst_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                 regions_disjoint p n b sz) ==>
              mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory)))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `32+k <= bsz` by decide_tac >>
  drule_all_then strip_assume_tac concat_anchor_start_mods >>
  `concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,~EXISTS expr_has_effect args)
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s0,G0,tn0) args (sb,shadow_sa,shadow_sb) (es,sa,s0,G0,tn0)
    (mem_bytes_at (B+32) k s0.vs_memory) P` by
    (simp_tac bool_ss [concat_loop_entry_mods_def,concat_loop_code_mods_def,
         LENGTH_mem_bytes_at,concat_horizon_mods_def,LET_THM,pairTheory.UNCURRY_DEF] >>
     asm_rewrite_tac[]) >>
  drule_then assume_tac
    (MATCH_MP (BETA_RULE concat_elements_from_head_mods)
       (CONJ concat_cut_gas_obs_mods concat_head_step_mods)) >>
  irule gas_outcome_full_mods_post_source >>
  qhdtm_x_assum `gas_outcome_full_mods` (irule_at Any) >>
  BETA_TAC >> simp_tac bool_ss [] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?vs. _` strip_assume_tac >> qexists_tac `vs` >>
  qhdtm_x_assum `concat_live_mods`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE[concat_live_mods_def,LENGTH_APPEND,LENGTH_mem_bytes_at,ADD_ASSOC]) >>
  qhdtm_x_assum `concat_old_frame_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[concat_old_frame_mods_def]) >>
  qhdtm_x_assum `concat_horizon_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[concat_horizon_mods_def]) >>
  pure_rewrite_tac[ADD_ASSOC] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
