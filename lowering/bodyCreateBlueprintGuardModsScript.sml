(* Compose guard and append without changing the dispatch witnesses. *)
Theory bodyCreateBlueprintGuardMods
Ancestors
  bodyCreateBlueprintGuardEntryMods bodyCreateBlueprintEndpointRebaseMods
  builtinCreate vyperCreate words venomState venomInst venomLayout
  fragExec fragGasOriginPtr ptrDiscipline bodyPtrDefs loweringShapeDefs

Theorem blueprint_guard_prepare_from_append:
  let n = blueprint_copy_size (w2n ow) code_bytes;
      pref = take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                       (DROP (w2n ow) code_bytes) in
  (!u Gu tu.
     compile_create_blueprint_append target amount sop off code args_ptr cnt rof sm = (result,sb) /\
     fn_has_code sm sb func /\
     (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
     MEM func ctx.ctx_functions /\
     gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu) /\
     (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
     ctx_has_dalloca ctx /\ allocas_below_fmp u /\ allocas_from lo u /\
     u.vs_alloca_next <= w2n u.vs_fmp /\
     ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
     eval_operand target u = SOME aw /\ op_taint tu target = {} /\
     eval_operand off u = SOME ow /\ op_taint tu off = {} /\
     take_pad_0 (LENGTH pref) (DROP (w2n ow) (lookup_account (w2w aw) u.vs_accounts).code) = pref /\
     eval_operand code u = SOME (n2w (LENGTH pref)) /\
     eval_operand cnt u = SOME (n2w (LENGTH args)) /\
     op_taint tu code = {} /\ op_taint tu cnt = {} /\
     op_prov Gu code = NONE /\ op_prov Gu cnt = NONE /\
     (!x. MEM (Var x) [target;off;code;args_ptr;cnt] ==> not_fresh_at sm x) /\
     (cnt <> Lit 0w ==>
       ?q a. args_ptr = Var q /\ lookup_var q u = SOME a /\ ptr_covers Gu tu q u (LENGTH args) /\
         (args = [] \/ w2n a + LENGTH args <= u.vs_alloca_next) /\
         (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tu.t_mem) /\
         read_memory (w2n a) (LENGTH args) u = args) /\
     LENGTH pref + LENGTH args < dimword (:256) /\
     venomLayout$ceil32 (LENGTH pref + LENGTH args) <= 2 ** 255 + 2 ** 64 ==>
     ?sc p size t H z.
       compile_create_dispatch (Var p) size amount sop rof sc = (result,sb) /\
       fn_has_code sc sb func /\ cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
       (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,H,z)) /\
       ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
       (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx;
                 vs_memory := u.vs_memory; vs_fmp := u.vs_fmp|>) = u /\
       lookup_var p t = SOME u.vs_fmp /\ ptr_covers H z p t (LENGTH pref + LENGTH args) /\
       eval_operand size t = SOME (n2w (LENGTH pref + LENGTH args)) /\ op_taint z size = {} /\
       (!x. Var x = size \/ x = p ==> not_fresh_at sc x) /\
       w2n u.vs_initial_fmp <= w2n u.vs_fmp /\
       w2n t.vs_fmp = w2n u.vs_fmp + venomLayout$ceil32 (LENGTH pref + LENGTH args) /\
       w2n u.vs_fmp + LENGTH pref + LENGTH args <= LENGTH t.vs_memory /\
       LENGTH u.vs_memory <= LENGTH t.vs_memory /\
       read_memory (w2n u.vs_fmp) (LENGTH pref + LENGTH args) t = pref ++ args /\
       (!j k. j+k <= w2n u.vs_fmp ==> read_memory j k t = read_memory j k u) /\
       (!i. w2n u.vs_fmp <= i /\ i < w2n u.vs_fmp + LENGTH pref + LENGTH args ==> i NOTIN z.t_mem) /\
       (!i. i < w2n u.vs_fmp /\ i IN z.t_mem ==> i IN tu.t_mem) /\
       z.t_stor = tu.t_stor /\ z.t_trans = tu.t_trans /\ z.t_imm = tu.t_imm /\
       (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\
         FLOOKUP H x = FLOOKUP Gu x /\ op_taint z (Var x) = op_taint tu (Var x))) /\
  (compile_create_blueprint_check lit target off sa = (code,sm) /\
   compile_create_blueprint_append target amount sop off code args_ptr cnt rof sm = (result,sb) /\
   fn_has_code sa sb func /\
   (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
   MEM func ctx.ctx_functions /\
   gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
   (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
   ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
   s.vs_alloca_next <= w2n s.vs_fmp /\
   ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   eval_operand target s = SOME aw /\ op_taint tn target = {} /\
   eval_operand off s = SOME ow /\ op_taint tn off = {} /\ op_prov G off = NONE /\
   code_bytes = (lookup_account (w2w aw) s.vs_accounts).code /\ LENGTH code_bytes <= 24576 /\
   eval_operand cnt s = SOME (n2w (LENGTH args)) /\ op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
   LENGTH args < 2 ** 64 /\
   (!x. MEM (Var x) [target;off;args_ptr;cnt;amount] \/ sop = SOME (Var x) ==> not_fresh_at sa x) /\
   (cnt <> Lit 0w ==>
     ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\ ptr_covers G tn q s (LENGTH args) /\
       (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
       (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
       read_memory (w2n a) (LENGTH args) s = args)) ==>
  if (if lit then blueprint_size_ok n else w2n ow < LENGTH code_bytes) then
    ?sc p size t H z.
      compile_create_dispatch (Var p) size amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
      eval_operand (Var p) t = SOME s.vs_fmp /\ ptr_covers H z p t (n + LENGTH args) /\
      eval_operand size t = SOME (n2w (n + LENGTH args)) /\ op_taint z (Var p) = {} /\ op_taint z size = {} /\
      (!x. Var x = size \/ x = p ==> not_fresh_at sc x) /\
      n + LENGTH args < dimword (:256) /\ w2n t.vs_initial_fmp <= w2n s.vs_fmp /\
      w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (n + LENGTH args) /\
      w2n s.vs_fmp + (n + LENGTH args) <= w2n t.vs_fmp /\
      w2n s.vs_fmp + (n + LENGTH args) <= LENGTH t.vs_memory /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\ allocas_below_fmp t /\
      read_memory (w2n s.vs_fmp) (n + LENGTH args) t = blueprint_initcode n (w2n ow) code_bytes args /\
      (!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = read_memory j k s) /\
      (!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + (n + LENGTH args) ==> i NOTIN z.t_mem) /\
      (!i. i < w2n s.vs_fmp /\ i IN z.t_mem ==> i IN tn.t_mem) /\
      z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x))
  else ?t H z. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort t,H,z)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "append")
    (fn th =>
      mk_asm "guard" (CONV_RULE (DEPTH_CONV BETA_CONV)
        (PURE_REWRITE_RULE[LET_THM] (MATCH_MP blueprint_guard_append_entry th))) >>
      map_every assume_tac (CONJUNCTS th))) >>
  qabbrev_tac `good = if lit then blueprint_size_ok (blueprint_copy_size (w2n ow) code_bytes)
                      else w2n ow < LENGTH code_bytes` >>
  asm_x "guard" mp_tac >> reverse (Cases_on `good`) >> pure_rewrite_tac[COND_CLAUSES]
  >- (disch_then ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`]
    (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS)
      (fn th => map_every assume_tac (CONJUNCTS th) >>
        asm_x "append" (qspecl_then [`u`,`Gu`,`tu`] (mp_tac o C MATCH_MP th))))) >>
  disch_then (qx_choosel_then [`sc1`,`p1`,`sz1`,`t1`,`H1`,`z1`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`sc1`,`p1`,`sz1`,`t1`,`H1`,`z1`] >>
  match_mp_tac blueprint_append_endpoint_rebase >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
