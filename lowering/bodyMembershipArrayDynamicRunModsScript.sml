(* Join the linked dynamic-array header with the bounded physical search. *)
Theory bodyMembershipArrayDynamicRunMods
Ancestors
  bodyMembershipArrayHeaderMods bodyFullBopRestWordFullControl
  bodyMembershipArrayDynamicAdapterMods
  bodyPtrBopInLoopContract bodyPtrBopInElementLoad
  bodyFullPostsMods loweringPosts exprLowering compileEnv
  context venomState ptrDiscipline list words
Libs monadsyntax

Theorem membership_array_dynamic_run_mods:
  bd = Dynamic cap /\ LENGTH ws <= cap /\ cap < dimword (:256) /\
  compile_var_array_membership cenv needle vv (ArrayT ety bd) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!x. needle = Var x ==> not_fresh_at sm x) /\
  (!H. guard H ==> ~u.vs_halted /\
    allocas_from lo u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand needle u = SOME needleword /\
    op_prov Gu needle = NONE /\
    op_taint Tu needle = {}) /\
  (?len sl sh Gh Th.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case vv_location vv of NONE => LocMemory | SOME l => l)
      (vv_operand vv) sm = (len,sl) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv
        (case vv_location vv of NONE => LocMemory | SOME l => l) ety)
      (word_scale (case vv_location vv of NONE => LocMemory | SOME l => l))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
        (case vv_location vv of NONE => LocMemory | SOME l => l))
      (SOME cap) is_in sl = (out,ct) /\
    fn_has_code sl ct fn /\
    (!H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (u,Gu,Tu) [] (OK sh,Gh,Th) /\
      membership_loop_frame sm Gu Tu u Gh Th sh /\
      eval_operand len sh = SOME (n2w (LENGTH ws)) /\
      op_prov Gh len = NONE /\
      op_taint Th len = {} /\
      ~sh.vs_halted /\
      allocas_from lo sh /\
      sh.vs_current_bb = sl.cs_current_bb /\
      sh.vs_inst_idx = LENGTH sl.cs_current_insts /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp sh) /\
      eval_operand needle sh = SOME needleword /\
      op_prov Gh needle = NONE /\
      op_taint Th needle = {}) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp sh) /\
    (!x. len = Var x ==> not_fresh_at sl x) /\
    (!i s Gs Ts. i < LENGTH ws /\
      (!H. guard H ==>
        membership_loop_frame sl Gh Th sh Gs Ts s /\
        membership_loop_registers sl i 0w Gs Ts s /\
        ~s.vs_halted /\
        allocas_from lo s /\
        s.vs_current_bb = fresh_label_output "in_body" (sl.cs_next_label+2) /\
        s.vs_inst_idx = 0) ==>
      ?t Gt Tt. !H. guard H ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
          (s,Gs,Ts) [] (OK t,Gt,Tt) /\
        membership_loop_frame sl Gh Th sh Gt Tt t /\
        membership_loop_registers sl i 0w Gt Tt t /\
        ~t.vs_halted /\
        allocas_from lo t /\
        t.vs_current_bb = fresh_label_output "in_body" (sl.cs_next_label+2) /\
        t.vs_inst_idx = 2 +
          (if 0 < word_scale (case vv_location vv of NONE => LocMemory | SOME l => l)
           then 1 else 0) +
          (if cenv.ce_is_ctor /\
              (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode /\
              IS_SOME cenv.ce_imm_alloca then 2 else 1) /\
        eval_operand
          (Var ("%" ++ toString (sl.cs_next_var+4+2+
            (if 0 < word_scale (case vv_location vv of NONE => LocMemory | SOME l => l)
             then 1 else 0) +
            (if cenv.ce_is_ctor /\
                (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode /\
                IS_SOME cenv.ce_imm_alloca then 2 else 1)))) t =
          SOME (EL i ws) /\
        op_prov Gt
          (Var ("%" ++ toString (sl.cs_next_var+4+2+
            (if 0 < word_scale (case vv_location vv of NONE => LocMemory | SOME l => l)
             then 1 else 0) +
            (if cenv.ce_is_ctor /\
                (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode /\
                IS_SOME cenv.ce_imm_alloca then 2 else 1)))) = NONE /\
        op_taint Tt
          (Var ("%" ++ toString (sl.cs_next_var+4+2+
            (if 0 < word_scale (case vv_location vv of NONE => LocMemory | SOME l => l)
             then 1 else 0) +
            (if cenv.ce_is_ctor /\
                (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode /\
                IS_SOME cenv.ce_imm_alloca then 2 else 1)))) = {})
  ) ==>
  ?q Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (u,Gu,Tu) [] (OK q,Gt,Tt) /\
      membership_loop_frame sm Gu Tu u Gt Tt q /\
      eval_operand out q = SOME
        (bool_to_word (if is_in then MEM needleword ws else ~MEM needleword ws)) /\
      op_prov Gt out = NONE /\
      op_taint Tt out = {} /\
      ~q.vs_halted /\
      allocas_from lo q /\
      q.vs_current_bb = ct.cs_current_bb /\
      q.vs_inst_idx = LENGTH ct.cs_current_insts
Proof
  strip_tac >>
  pop_assum $ mk_asm "loop" >>
  `LENGTH ws < dimword (:256)` by decide_tac >>
  `sm.cs_next_var <= sl.cs_next_var` by
    (irule exprSafeOperandBuiltinsTheory.compile_ptr_load_next_var >>
     qpat_assum `compile_ptr_load _ _ _ _ _ = _` (irule_at Any)) >>
  `!x. needle = Var x ==> not_fresh_at sl x` by
    (rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[]) >>
  `?q Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (sh,Gh,Th) [] (OK q,Gt,Tt) /\
      membership_loop_frame sl Gh Th sh Gt Tt q /\
      eval_operand out q = SOME
        (bool_to_word (if is_in then MEM needleword ws else ~MEM needleword ws)) /\
      op_prov Gt out = NONE /\ op_taint Tt out = {} /\
      ~q.vs_halted /\ allocas_from lo q /\
      q.vs_current_bb = ct.cs_current_bb /\
      q.vs_inst_idx = LENGTH ct.cs_current_insts` by
    (irule rest_word_membership_loop_const_full_horizon_joint_all >>
     qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`
       (irule_at Any) >>
     conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. guard H ==> gas_origin_ptr_path _ (u,Gu,Tu) _ _ /\ _`
           (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. guard H ==> gas_origin_ptr_path _ (u,Gu,Tu) _ _ /\ _`
           (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (pure_rewrite_tac[GSYM dynamic_loop_bound_some_offset_adapter] >>
         asm "loop" ACCEPT_TAC) >>
     simp[]) >>
  qmatch_asmsub_rename_tac
    `gas_origin_ptr_path _ (sh,Gh,Th) _ (OK qf,Gf,Tf)` >>
  qexistsl_tac [`qf`,`Gf`,`Tf`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!H. guard H ==> gas_origin_ptr_path _ (sh,Gh,Th) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!H. guard H ==> gas_origin_ptr_path _ (u,Gu,Tu) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qpat_assum `gas_origin_ptr_path _ (sh,Gh,Th) _ (OK qf,Gf,Tf)`
        (irule_at Any) >> asm_rewrite_tac[]) >>
  conj_tac
  >- (irule membership_loop_frame_source >>
      qpat_assum `membership_loop_frame sl Gh Th sh Gf Tf qf` (irule_at Any) >>
      asm_rewrite_tac[] >> rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  asm_rewrite_tac[]
QED
