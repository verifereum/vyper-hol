(* The physical length load before an ordinary dynamic membership loop. *)
Theory bodyMembershipArrayHeaderMods
Ancestors
  bodyPtrBopInHeaderCode bodyFullBopRestWordLoads bodyFullBopRestWordCtorHeader
  bodyPtrBopInLoopContract bodyPtrBopInElementLoad
  context exprLowering emitHelper

Theorem membership_dynamic_located[local]:
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap))
    is_in sm = (out,ct) ==>
  ?nv. vv_location nv = SOME loc /\ vv_operand nv = vv_operand vv /\
    compile_var_array_membership cenv needle nv (ArrayT ety (Dynamic cap))
      is_in sm = (out,ct)
Proof
  Cases_on `vv`
  >- (simp[vv_location_def] >> strip_tac >>
      rename1 `compile_var_array_membership _ _ (StackValue ann arr_op) _ _ _ = _` >>
      qexists_tac `LocatedValue ann (mk_ptr arr_op LocMemory)` >>
      fs[membership_dynamic_compile_split, vv_operand_def, vv_location_def, mk_ptr_def]) >>
  strip_tac >>
  rename1 `compile_var_array_membership _ _ (LocatedValue ann p) _ _ _ = _` >>
  qexists_tac `LocatedValue ann p` >> fs[vv_location_def]
QED

Theorem membership_array_header_mods:
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  loc <> LocCalldata /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap))
    is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!x. needle = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sm x) /\
  (!H:'h. guard H ==> ~u.vs_halted /\ allocas_from lo u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand (vv_operand vv) u = SOME w /\ op_taint Tu (vv_operand vv) = {} /\
    (if cenv.ce_is_ctor /\ loc = LocCode then
       lo <= u.vs_alloca_next /\ op_prov Gu (vv_operand vv) = NONE /\
       w2n w + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
       mload (w2n w) u = n2w (LENGTH ws) /\
       (!ib. cenv.ce_imm_alloca = SOME ib ==>
         eval_operand ib u = SOME 0w /\ op_prov Gu ib = NONE /\ op_taint Tu ib = {})
     else case loc of
       LocMemory => (?x. vv_operand vv = Var x /\ ptr_covers Gu Tu x u 32) /\
         w2n w + 32 <= u.vs_alloca_next /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
         mload (w2n w) u = n2w (LENGTH ws)
     | LocStorage => key_taint Tu.t_stor w = {} /\ sload w u = n2w (LENGTH ws)
     | LocTransient => key_taint Tu.t_trans w = {} /\ tload w u = n2w (LENGTH ws)
     | LocCode => w2n w <= LENGTH u.vs_data_section /\
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) = n2w (LENGTH ws)
     | _ => F)) ==>
  ?len sl sh Gh Th.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (vv_operand vv) sm = (len,sl) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv loc ety) (word_scale loc)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) (SOME cap) is_in sl = (out,ct) /\
    (!H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (u,Gu,Tu) [] (OK sh,Gh,Th) /\
      membership_loop_frame sm Gu Tu u Gh Th sh /\
      eval_operand len sh = SOME (n2w (LENGTH ws)) /\
      op_prov Gh len = NONE /\ op_taint Th len = {} /\
      ~sh.vs_halted /\ allocas_from lo sh /\ sh.vs_current_bb = sl.cs_current_bb /\
      sh.vs_inst_idx = LENGTH sl.cs_current_insts /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp sh) /\
      eval_operand needle sh = eval_operand needle u /\
      op_prov Gh needle = op_prov Gu needle /\ op_taint Th needle = op_taint Tu needle /\
      eval_operand (vv_operand vv) sh = eval_operand (vv_operand vv) u /\
      op_prov Gh (vv_operand vv) = op_prov Gu (vv_operand vv) /\
      op_taint Th (vv_operand vv) = op_taint Tu (vv_operand vv))
Proof
  strip_tac >> drule_all_then (qx_choose_then `nv` strip_assume_tac) membership_dynamic_located >>
  `?len sl sh Gh Th.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (vv_operand vv) sm = (len,sl) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv loc ety) (word_scale loc)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) (SOME cap) is_in sl = (out,ct) /\
    (!H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (u,Gu,Tu) [] (OK sh,Gh,Th) /\
      membership_loop_frame sm Gu Tu u Gh Th sh /\
      eval_operand len sh = SOME (n2w (LENGTH ws)) /\
      op_prov Gh len = NONE /\ op_taint Th len = {} /\
      ~sh.vs_halted /\ allocas_from lo sh /\ sh.vs_current_bb = sl.cs_current_bb /\
      sh.vs_inst_idx = LENGTH sl.cs_current_insts)` by suspend "header" >>
  qexistsl_tac [`len`, `sl`, `sh`, `Gh`, `Th`] >> simp[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac membership_loop_frame_allocas_below_fmp >>
  drule membership_loop_frame_operand >>
  disch_then (qspec_then `needle` mp_tac) >> simp[] >> strip_tac >>
  drule membership_loop_frame_operand >>
  disch_then (qspec_then `vv_operand vv` mp_tac) >> simp[]
QED

Resume membership_array_header_mods[header]:
  qpat_x_assum `loc = case _ of _ => _ | _ => _` kall_tac >>
  qpat_x_assum `compile_var_array_membership _ _ vv _ _ _ = _` kall_tac >>
  qpat_x_assum `vv_operand nv = vv_operand vv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `cenv.ce_is_ctor /\ loc = LocCode`
  >- (qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode` strip_assume_tac >>
      qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
      irule rest_word_membership_ctor_header_const_full_joint >>
      reverse conj_tac >- simp[] >>
      qexists_tac `w` >> gen_tac >> disch_tac >>
      qpat_assum `!H. guard H ==> ~u.vs_halted /\ _` (drule_then strip_assume_tac) >>
      qpat_x_assum `if _ then _ else _` mp_tac >> simp[]) >>
  irule rest_word_membership_header_joint_const >>
  reverse conj_tac
  >- (simp[] >> Cases_on `loc` >> fs[]) >>
  qexists_tac `w` >> gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> ~u.vs_halted /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[]
QED

Finalise membership_array_header_mods
