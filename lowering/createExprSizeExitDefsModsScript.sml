(* Completed-operand replay and the oversized CREATE exit for a linked unit. *)
Theory createExprSizeExitDefsMods
Ancestors
  createExprSizeExitDefs bodyFullPostsMods exprBodyPreProps
  exprSimFullBundleProps s1PrefixDefs bodyInvSplit bodyInvCodeProps exprSimHypsDefs
  bodyCallSupport bodyFullShadowBodyInv sourceExemptMods bodySim contractInvContextProps
  bodyFullExtCallPosList bodyFullExtCallDirectState alist list option
  compileEnv loweringPosts loweringStateRelDefs exprLoweringProps vyperContext gasContext
  vfmConstants venomInst venomState words integer_word finite_map

Definition expr_sim_full_pre_mods_def:
  expr_sim_full_pre_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es
    (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) <=>
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
        (op, shadow_sb) /\
      expr_sim_full_code (ctx, shadow_ctx, func, shadow_func)
        (sa, sb, shadow_sa, shadow_sb) /\
      local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition expr_vv_sim_full_pre_mods_def:
  expr_vv_sim_full_pre_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es
    (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) <=>
      compile_expr cenv ty e sa = (vv, sb) /\
      compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv, shadow_sb) /\
      expr_sim_full_code (ctx, shadow_ctx, func, shadow_func)
        (sa, sb, shadow_sa, shadow_sb) /\
      local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition expr_sim_full_post_mods_def:
  expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,op,G0,tn0) =
    \H res ee G tn t. ?v. res = INL v /\
          expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (post_value_type cenv e) v op t /\
          expr_sim_full_endpoint func sb s0 t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
          ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
          (~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Definition gas_completed_operand_mods_def:
  gas_completed_operand_mods (DF, lo, explicit, ctx, func, PG)
      mods cx st0 sa sb source (es, s0, G0, tn0) Q <=>
    !H0 marks s tail res ee.
      create_expr_prefix sa sb explicit ctx func s0 marks s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (res, ee) /\
      valid_horizon cx st0 H0 ee.storage_trace ==>
      (?G tn.
         ee.gas_obs = tail /\
         !H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
             (s0,G0,tn0) marks (OK s,G,tn) /\
           Q H res (ee with gas_obs := []) G tn s) \/
      (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err)
End

Definition create_operand_completed_ok_mods_def:
  create_operand_completed_ok_mods mods exps cx e <=>
    !DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      expr_body_pre_mods mods cenv cx env e es ==>
      (!st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
        expr_sim_full_pre_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) ==>
        gas_completed_operand_mods
          (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
          mods cx st0 sa sb (bind (eval_expr cx e) (read_result cx))
          (es, s0, G0, tn0)
          (expr_sim_full_post_mods (DF, lo, d, ctx, func) cenv cx e
            (es, sa, sb, s0, op, G0, tn0))) /\
      (!st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
        expr_vv_sim_full_pre_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
        gas_completed_operand_mods
          (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
          mods cx st0 sa sb (eval_expr cx e) (es, s0, G0, tn0)
          (\H res ee G tn t. ?tv. res = INL tv /\
            vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
            vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
              ee tv vv t /\
            alloca_history func t /\
            (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
            s0.vs_alloca_next <= t.vs_alloca_next /\
            ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
            ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
            (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
               (!t' p. vv = LocatedValue t' p ==>
                       p.ptr_location = LocMemory)) /\
            (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?val. read_result cx tv ee = (INL val, ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                          SOME rt /\
                        eval_operand (vv_operand vv) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
            (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                     ptr_buf_ok cenv e op G t) /\
            (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
            ghost_kept_at lo cenv es sa G0 tn0 s0 G tn))
End

Definition create_expr_size_exit_mods_def:
  create_expr_size_exit_mods mods exps cx e <=>
    !DF lo d (PG : (num # num) option list) src tops
      ctx shadow_ctx func shadow_func cenv env ty es
      st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      contract_inv mods exps ctx cenv cx /\
      module_body_inv mods src tops cenv cx /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      expr_body_pre_mods mods cenv cx env e es /\
      expr_vv_sim_full_pre_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      !H marks s bb inst value off sz salt w tail res ee.
        create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx)
          ctx func s0 marks s /\
        (s.vs_current_bb <> sb.cs_current_bb \/
         s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
        lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst /\
        inst.inst_id IN frag_ids sa sb /\
        (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
             MEM j.inst_opcode [CREATE; CREATE2] ==> j.inst_id <= inst.inst_id) /\
        ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz]) \/
         (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value; off; sz; salt])) /\
        eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w /\
        eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (res, ee) /\
        valid_horizon cx st0 H ee.storage_trace ==>
        res = INR (Error (RuntimeError "create initcode too large")) \/
        (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err)
End

Definition extcall_positional_post_mods_def:
  extcall_positional_post_mods mods keep_pure DF lo d ctx func cenv cx env
    kw_es xs svs sa sb es s0 G0 tn0 =
    \H res ee G tn t. ?vs.
      res = INL vs /\ LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v.
        (?si sm ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,sm) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
          (~copy ==> ~exprs_can_mutate cenv kw_es) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) t = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              sm.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes t n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
          sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
        vv_storage_live H cx sv ee t /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G t) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\
      (keep_pure /\ ~EXISTS expr_has_effect xs ==> pure_frame cenv func es sa s0 t) /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv_mods mods cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
End

Definition abi_encode_saved_state_mods_def:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu <=>
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee u /\
      immutable_frame_mods func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
    wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts /\
    se.cs_next_var <= a.cs_next_var /\ se.cs_next_id <= shared /\ shared < a.cs_next_id /\
    not_fresh_at a root /\ not_fresh_at a dst /\
    eval_operand (Var root) u = SOME (n2w pbase) /\ ptr_covers Gu tu root u capacity /\
    eval_operand (Var dst) u = SOME (n2w (pbase+dst_offset)) /\
    ptr_covers Gu tu dst u (capacity-dst_offset) /\
    FLOOKUP u.vs_allocas shared = SOME (pbase,capacity) /\
    LENGTH prefix <= dst_offset /\ dst_offset <= capacity /\
    read_memory (pbase+dst_offset-LENGTH prefix) (LENGTH prefix) u = prefix /\
    (!i. pbase+dst_offset-LENGTH prefix <= i /\ i < pbase+dst_offset ==> i NOTIN tu.t_mem)
End

Theorem create_size_immutable_frame_singleton[local]:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (stmt_state_rel H ctx func cenv cx es s /\
   immutable_frame_mods func cenv cx es s /\ P <=>
   stmt_state_rel H ctx func cenv cx es s /\ P)
Proof
  strip_tac >>
  `cenv with ce_module := NONE = cenv` by
    simp[compile_env_component_equality] >>
  simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       immutable_frame_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_mods_def, ALOOKUP_def, FORALL_OPTION] >>
  eq_tac >> strip_tac >> asm_rewrite_tac[]
QED

Theorem expr_sim_full_pre_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (expr_sim_full_pre_mods cfg cenv cx ty e es input <=>
   expr_sim_full_pre cfg cenv cx ty e es input)
Proof
  strip_tac >> PairCases_on `cfg` >> PairCases_on `input` >>
  simp[expr_sim_full_pre_mods_def, expr_sim_full_pre_def, expr_sim_full_code_def,
       dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton,
       SF CONJ_ss, create_size_immutable_frame_singleton] >>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED

Theorem expr_vv_sim_full_pre_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (expr_vv_sim_full_pre_mods cfg cenv cx ty e es input <=>
   expr_vv_sim_full_pre cfg cenv cx ty e es input)
Proof
  strip_tac >> PairCases_on `cfg` >> PairCases_on `input` >>
  simp[expr_vv_sim_full_pre_mods_def, expr_vv_sim_full_pre_def, expr_sim_full_code_def,
       dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton,
       SF CONJ_ss, create_size_immutable_frame_singleton] >>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED

Theorem expr_sim_full_post_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  expr_sim_full_post_mods cfg cenv cx e input =
  expr_sim_full_post cfg cenv cx e input
Proof
  strip_tac >> PairCases_on `cfg` >> PairCases_on `input` >>
  simp[expr_sim_full_post_mods_def, expr_sim_full_post_def,
       Q.INST [`tops` |-> `cx_tops cx`] expr_post_mods_singleton,
       ghost_inv_at_mods_singleton]
QED

Theorem gas_completed_operand_mods_singleton:
  gas_completed_operand_mods cfg [(NONE,tops)] cx st0 sa sb source input Q <=>
  gas_completed_operand cfg tops cx st0 sa sb source input Q
Proof
  PairCases_on `cfg` >> PairCases_on `input` >>
  simp[gas_completed_operand_mods_def, gas_completed_operand_def,
       unspecified_behaviour_exempt_mods_singleton]
QED

Theorem create_size_body_inv_singleton[local]:
  (contract_inv [(NONE,tops)] [] ctx cenv cx /\
   module_body_inv [(NONE,tops)] src active_tops cenv cx) <=>
  src = NONE /\ active_tops = tops /\ body_inv tops ctx cenv cx
Proof
  `contract_inv [(NONE,tops)] [] ctx cenv cx ==>
    cenv_module_pins_mods [(NONE,tops)] cenv` by simp[contract_inv_def] >>
  Cases_on `src` >>
  simp[body_inv_split_def, module_body_inv_def, cenv_module_pins_split_def] >>
  metis_tac[]
QED

Theorem create_size_body_pre_singleton[local]:
  body_inv tops ctx cenv cx ==>
  (expr_body_pre_mods [(NONE,tops)] cenv cx env e es <=>
   expr_body_pre cenv cx env e es)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      drule body_inv_main_code >> strip_tac >>
      drule body_inv_contract >> strip_tac >>
      drule contract_inv_module_codes >> strip_tac >>
      drule contract_inv_immutable_section_layout >> strip_tac >>
      drule body_inv_module_locations >> strip_tac >>
      `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
        (drule contract_inv_singleton_source_modules >> simp[]) >>
      `EVERY (\c. FST c = NONE) (int_calls_expr e)` by
        (drule expr_body_pre_mods_int_calls >>
         simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
         rename1 `FST call = NONE` >>
         first_x_assum (drule_then mp_tac) >>
         simp[source_body_call_supported_def, ALOOKUP_def] >>
         Cases_on `FST call` >> simp[]) >>
      fs[expr_body_pre_split_def, expr_body_pre_mods_def,
         expr_sim_inv_mods_singleton, type_env_all_modules_def, type_env_def,
         FUNION_FEMPTY_2]) >>
  metis_tac[body_inv_expr_body_pre_mods]
QED

Theorem create_size_body_singleton_fields[local]:
  body_inv tops ctx cenv cx ==>
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE
Proof
  strip_tac >>
  drule body_inv_main_code >> strip_tac >>
  drule body_inv_module_locations >> strip_tac >>
  drule body_inv_contract >> strip_tac >>
  drule contract_inv_cenv_modules >> simp[] >>
  metis_tac[contract_inv_singleton_source_modules]
QED

Theorem create_operand_completed_ok_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (create_operand_completed_ok_mods [(NONE,tops)] [] cx e <=>
   create_operand_completed_ok cx e)
Proof
  strip_tac >>
  simp[create_operand_completed_ok_mods_def, create_operand_completed_ok_def,
       CONJ_ASSOC, create_size_body_inv_singleton, shadow_body_inv_split_def] >>
  (eq_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
   drule create_size_body_singleton_fields >> strip_tac >>
   drule create_size_body_pre_singleton >> strip_tac >> gvs[]) >| [
    first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`,
      `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ty`, `es`] mp_tac),
    first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`,
      `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ty`, `es`] mp_tac)
  ] >>
  simp[expr_sim_full_pre_mods_singleton, expr_vv_sim_full_pre_mods_singleton,
       expr_sim_full_post_mods_singleton, gas_completed_operand_mods_singleton,
       Q.INST [`tops` |-> `cx_tops cx`] vv_post_mods_singleton,
       ghost_inv_at_mods_singleton]
QED

Theorem create_expr_size_exit_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
  (create_expr_size_exit_mods [(NONE,tops)] [] cx e <=>
   create_expr_size_exit cx e)
Proof
  strip_tac >>
  simp[create_expr_size_exit_mods_def, create_expr_size_exit_def,
       CONJ_ASSOC, create_size_body_inv_singleton, shadow_body_inv_split_def] >>
  (eq_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
   drule create_size_body_singleton_fields >> strip_tac >>
   drule create_size_body_pre_singleton >> strip_tac >>
   gvs[expr_vv_sim_full_pre_mods_singleton]) >| [
    first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`,
      `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ty`, `es`,
      `st0`, `sa`, `sb`, `shadow_sa`, `shadow_sb`, `vv`, `s0`, `G0`, `tn0`] mp_tac),
    first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`,
      `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ty`, `es`,
      `st0`, `sa`, `sb`, `shadow_sa`, `shadow_sb`, `vv`, `s0`, `G0`, `tn0`] mp_tac)
  ] >>
  simp[expr_vv_sim_full_pre_mods_singleton, unspecified_behaviour_exempt_mods_singleton]
QED

Theorem extcall_positional_post_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE /\
  immutable_section_layout_mods [(NONE,tops)] cenv ==>
  extcall_positional_post_mods [(NONE,tops)] keep DF lo d ctx func cenv cx env
    kw_es xs svs sa sb es s0 G0 tn0 =
  extcall_positional_post keep DF lo d ctx func cenv cx env
    kw_es xs svs sa sb es s0 G0 tn0
Proof
  strip_tac >>
  `cx_tops cx = tops` by simp[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
  simp[extcall_positional_post_mods_def, extcall_positional_post_def,
       Q.INST [`tops` |-> `cx_tops cx`] vv_holds_mods_singleton,
       ghost_inv_at_mods_singleton,
       expr_sim_inv_mods_singleton, SF CONJ_ss, create_size_immutable_frame_singleton]
QED

Theorem abi_encode_saved_state_mods_singleton:
  ce.ce_modules = [(NONE,cx_tops cx)] /\ ce.ce_module = NONE ==>
  (abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
     shared pbase capacity root dst dst_offset prefix a u Gu tu <=>
   abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
     shared pbase capacity root dst dst_offset prefix a u Gu tu)
Proof
  strip_tac >>
  simp[abi_encode_saved_state_mods_def, abi_encode_saved_state_def,
       ghost_inv_at_mods_singleton, SF CONJ_ss, create_size_immutable_frame_singleton]
QED
