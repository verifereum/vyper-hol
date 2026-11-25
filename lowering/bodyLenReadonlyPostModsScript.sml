(* Transport a fixed Len load endpoint into the linked post package. *)
Theory bodyLenReadonlyPostMods
Ancestors
  bodyLenVvPostMods bodyFullUnwrapRun bodyFullPostsMods
  bodyForRangeScalarFrameMods bodyPtrSignedConvertSourceFrame
  bodyFullHashKeccakFixed freshWrites exprSimUnwrap exprLowering
  exprLoweringProps loweringPosts loweringStateRelDefs bodyPtrDefs
  fragGasOriginPtr gasShadowState allocaHistory compileEnv
  vyperInterpreter vyperState venomState venomInst finite_map list

Theorem len_readonly_post_mods:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op n z G2 tn2 inst.
    result_array_length cx tv ee = (INL n,ee) /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    op = Var (STRING #"%" (toString sm.cs_next_var)) /\
    z = (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t)
          with vs_inst_idx := SUC t.vs_inst_idx /\
    sb.cs_current_bb = sm.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
    inst.inst_opcode <> ALLOCA /\
    (!bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb ==>
      get_instruction bb (LENGTH sm.cs_current_insts) = SOME inst) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      gas_origin_ptr_edge
        (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
      (!x. not_fresh_at sm x ==>
        FLOOKUP G2 x = FLOOKUP G x /\
        op_taint tn2 (Var x) = op_taint tn (Var x)) /\
      tn2.t_mem = tn.t_mem /\
      tn2.t_stor = tn.t_stor /\
      tn2.t_trans = tn.t_trans /\
      tn2.t_imm = tn.t_imm /\
      op_taint tn2 op = {} /\
      op_prov G2 op = NONE) ==>
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path
        (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
      expr_post_mods H ctx func cenv cx
        (Builtin (BaseT (UintT 256)) Len [e])
        es sa sb s0 ee (IntV (&n)) op z /\
      expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sm.cs_current_insts + 1 /\
      alloca_history func z /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 z /\
      ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `~z.vs_halted` by simp[update_var_def] >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sm.cs_next_var)` by fs[not_fresh_at_def] >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee z` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`t`,`sm`] >>
     simp[update_var_def]) >>
  conj_tac
  >- (qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
      qpat_x_assum `~z.vs_halted` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  conj_tac
  >- (pure_rewrite_tac[expr_post_mods_def] >> conj_tac
      >- (irule expr_post_of_vv_post_stack >> qexists_tac `BaseT (UintT 256)` >>
          irule len_vv_post_load_mods >> conj_tac
          >- simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl [`t`,`sm`,`tv`,`vv`] >> simp[update_var_def] >>
          rpt strip_tac >>
          qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _` drule >> simp[])
      >> irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`t`,`sm`] >>
      simp[update_var_def]) >>
  conj_tac
  >- simp[exprSimMemDefsTheory.expr_store_bound_def, is_word_type_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac
  >- (qpat_x_assum `alloca_history _ _` mp_tac >>
      simp[alloca_history_def, update_var_def] >>
      strip_tac >> rpt strip_tac >> Cases_on `k = LENGTH sm.cs_current_insts`
      >- (gvs[] >> first_x_assum drule >> simp[]) >>
      `k < LENGTH sm.cs_current_insts` by decide_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl [`G`,`ee`,`t`,`sm`,`tn`] >> simp[update_var_def]) >>
  conj_tac
  >- simp[ptr_val_ok_def, is_word_type_def] >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]
QED
