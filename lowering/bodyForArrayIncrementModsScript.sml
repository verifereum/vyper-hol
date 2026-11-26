(* Execute the popped Array back-edge and rebuild its linked header. *)
Theory bodyForArrayIncrementMods
Ancestors bodyFullPostsMods[qualified,ignore_grammar] unitTransformDefs[qualified,ignore_grammar] typedCopyLoopHeaderPtr[qualified,ignore_grammar] bodyForRangeHeaderMods[qualified,ignore_grammar] marker[qualified,ignore_grammar] bodyFullPredsMods[qualified,ignore_grammar] bodyFullShadowBodyInv[qualified,ignore_grammar]
  bodyForArrayControlFrameMods bodyForArrayHeaderMods bodyFullForArrayRound
  bodyFullForRange bodyFullIfExpReach bodyFullShared allocaHistory
  exprSimOperands exprLoweringProps stmtSimDefs stmtSimProps loweringPosts
  venomInst venomInstProps venomState finite_map fragGasOriginPtr fragExec
  ptrDiscipline bodyPtrDefs bodySimFull

Theorem for_array_increment_header_path_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  rs = DROP (SUC k) vs /\ a = EL k vs /\
  lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [next_var];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var next_var] [idx];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
  s.vs_current_bb = incr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var idx s = SOME (n2w k) /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand base_op s = SOME bw /\ op_taint tn base_op = {} /\
  op_prov G base_op = NONE /\
  eval_operand len_op s = SOME (n2w (LENGTH vs)) /\
  op_taint tn len_op = {} /\ op_prov G len_op = NONE /\
  (!x. base_op = Var x \/ len_op = Var x ==> not_fresh_at saL x) /\
  sa.cs_next_var <= saL.cs_next_var /\
  local_ptrs_reserved c sa /\
  ~not_fresh_at saL next_var /\ ~not_fresh_at saL idx /\
  xd <> next_var /\ xd <> idx /\
  (!q sz. c.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  (!q sz. c.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  for_array_item_mods c sa saExpr (xd,dw,capacity,aidItem) ee G tn s /\
  stmt_state_rel H ctx func c cx ee s /\
  immutable_frame_mods func c cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok c sa s /\ return_buf_frame d c sa s /\
  return_buf_sep d c ee s /\
  ghost_inv_at_mods (DF H) lo d c cx ee G tn s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn s /\
  for_array_capture_frame_mods c (em,saExpr,saL,u,tu) ee tn s /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods c cx env ee /\
  lookup_scopes id ee.scopes = NONE /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!fn inst q. frag_reachable ctx func s fn inst q ==> dalloca_fmp_headroom inst q) ==>
  let v = n2w k + 1w;
      t = jump_to cond (update_var idx v (update_var next_var v s));
      G1 = DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx});
      tn1 = tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{})
  in
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa,s0,G0,tn0) (em,saExpr,saL,u,tu)
      (xd,dw,capacity,aidItem) vs (base_op,bw,len_op,idx)
      cond Route H rs ee G1 tn1 t
Proof
  strip_tac >> simp[LET_THM, Excl "DRESTRICT_DRESTRICT"] >>
  qabbrev_tac `v = n2w k + (1w:bytes32)` >>
  qabbrev_tac `u1 = update_var next_var v s` >>
  qabbrev_tac `u2 = update_var idx v u1` >>
  qabbrev_tac `t = jump_to cond u2` >>
  qabbrev_tac `G1 = DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{})` >>
  conj_asm1_tac >- suspend "path" >>
  `!x. x <> idx /\ x <> next_var ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t`, Abbr `u1`, Abbr `u2`, Abbr `G1`, Abbr `tn1`,
         jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
         FLOOKUP_DRESTRICT, op_taint_def] >>
  `!x. not_fresh_at saL x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `x <> idx /\ x <> next_var` by
       (conj_tac >> CCONTR_TAC >> gvs[]) >>
     qpat_assum `!x. x <> idx /\ x <> next_var ==> _` irule >>
     simp[]) >>
  `eval_operand base_op t = SOME bw /\ op_prov G1 base_op = NONE /\
   op_taint tn1 base_op = {}` by
    (Cases_on `base_op`
     >- (`c' = bw` by
           (qpat_assum `eval_operand (Lit c') s = SOME bw` mp_tac >>
            simp[eval_operand_def] >> (gvs[eval_operand_def, op_prov_def, op_taint_def]) ) >>
         simp[eval_operand_def,op_prov_def,op_taint_def])
     >- (rename1 `Var x` >>
         `not_fresh_at saL x` by
           (qpat_assum `!x. base_op = Var x \/ len_op = Var x ==> _`
              (qspec_then `x` mp_tac) >> simp[]) >>
         qpat_assum `!x. not_fresh_at saL x ==> _`
           (qspec_then `x` mp_tac) >> simp[] >>
         qpat_assum `eval_operand (Var x) s = SOME bw`
           (strip_assume_tac o REWRITE_RULE [eval_operand_def]) >>
         qpat_assum `op_prov G (Var x) = NONE`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >>
         simp[eval_operand_def,op_prov_def,op_taint_def])
     >- (qpat_assum `eval_operand (Label s') s = SOME bw`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [eval_operand_def]) >>
         simp[eval_operand_def,op_prov_def,op_taint_def,jump_to_def,
              update_var_def,Abbr `t`,Abbr `u1`,Abbr `u2`])) >>
  `eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
   op_prov G1 len_op = NONE /\ op_taint tn1 len_op = {}` by
    (Cases_on `len_op`
     >- (`c' = n2w (LENGTH vs)` by
           (qpat_assum `eval_operand (Lit c') s = SOME (n2w (LENGTH vs))`
             (strip_assume_tac o SIMP_RULE (srw_ss()) [eval_operand_def]) >>
            first_assum ACCEPT_TAC) >>
         simp[eval_operand_def,op_prov_def,op_taint_def])
     >- (rename1 `Var x` >>
         `not_fresh_at saL x` by
           (qpat_assum `!x. base_op = Var x \/ len_op = Var x ==> _`
              (qspec_then `x` mp_tac) >> simp[]) >>
         qpat_assum `!x. not_fresh_at saL x ==> _`
           (qspec_then `x` mp_tac) >> simp[] >>
         qpat_assum `eval_operand (Var x) s = SOME (n2w (LENGTH vs))`
           (strip_assume_tac o REWRITE_RULE [eval_operand_def]) >>
         qpat_assum `op_prov G (Var x) = NONE`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >>
         simp[eval_operand_def,op_prov_def,op_taint_def])
     >- (qpat_assum `eval_operand (Label s') s = SOME (n2w (LENGTH vs))`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [eval_operand_def]) >>
         simp[eval_operand_def,op_prov_def,op_taint_def,jump_to_def,
              update_var_def,Abbr `t`,Abbr `u1`,Abbr `u2`])) >>
  drule_all for_array_control_scalar_frame_mods >>
  simp[for_array_header_mods_def, Abbr `t`, Abbr `u1`, Abbr `u2`,
       Abbr `G1`, Abbr `tn1`] >>
  (gvs[bodyForArrayControlFrameModsTheory.for_array_control_scalar_frame_mods, bodyForArrayHeaderModsTheory.for_array_header_mods_def, bodyFullForRangeTheory.range_full_increment_frame, typedCopyLoopHeaderPtrTheory.typed_copy_loop_test_frame, bodyForRangeHeaderModsTheory.range_header_init_mods, bodyForRangeHeaderModsTheory.range_header_mods_def, bodyForArrayHeaderModsTheory.for_array_done_mods_def, bodyFullForRangeTheory.range_full_increment_path, bodyForArrayHeaderModsTheory.for_array_capture_frame_mods_def, bodyForArrayHeaderModsTheory.for_array_item_mods_def, bodyForArrayHeaderModsTheory.for_array_index_mods_def, bodyForArrayHeaderModsTheory.for_array_outer_frame_mods_def, markerTheory.Abbrev_def, bodyFullForArrayRoundTheory.for_nonslot_layout_def, bodyFullPredsModsTheory.body_const_cells_agree_mods_def, bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def])
QED

Resume for_array_increment_header_path_mods[path]:
  `op_prov G (Var idx) = NONE` by fs[op_prov_def] >>
  simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, Abbr `u1`, Abbr `u2`, Abbr `v`] >>
  `?bb i1 i2 i3. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (SUC (SUC s.vs_inst_idx)) =
        SOME (mk_inst i3 JMP [Label cond] []) /\
      get_instruction bb (SUC s.vs_inst_idx) =
        SOME (mk_inst i2 ASSIGN [Var next_var] [idx]) /\
      get_instruction bb s.vs_inst_idx =
        SOME (mk_inst i1 ADD [Var idx;Lit 1w] [next_var])` by
    (qexistsl [`<|bb_label := incr; bb_instructions :=
                  [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [next_var];
                   mk_inst (sj.cs_next_id + 1) ASSIGN [Var next_var] [idx];
                   mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|>`,
               `sj.cs_next_id`,`sj.cs_next_id + 1`,`sj.cs_next_id + 2`] >>
     qpat_assum `s.vs_current_bb = incr` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = 0` SUBST1_TAC >>
     qpat_assum `lookup_block incr func.fn_blocks = SOME _`
       (fn th => simp[th,get_instruction_def])) >>
  irule (SRULE [NoAsms] range_full_increment_path) >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- (qexistsl [`<|bb_label := incr; bb_instructions :=
                  [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [next_var];
                   mk_inst (sj.cs_next_id + 1) ASSIGN [Var next_var] [idx];
                   mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|>`,
               `sj.cs_next_id`,`sj.cs_next_id + 1`,`sj.cs_next_id + 2`] >>
      qpat_assum `s.vs_current_bb = incr` SUBST1_TAC >>
      qpat_assum `s.vs_inst_idx = 0` SUBST1_TAC >>
      qpat_assum `lookup_block incr func.fn_blocks = SOME _`
        (fn th => simp[th,get_instruction_def]))
  >- simp[]
  >- ((simp[] >> (fn g => if length (fst g) = 49 andalso String.translate (fn c => if Char.isSpace c then "" else String.str c) (PP.pp_to_string 100 Parse.pp_term (snd g)) = "ctx_has_dallocactx⇒allocas_below_fmps" then (gvs[bodyForArrayHeaderModsTheory.for_array_header_mods_def, bodyForRangeHeaderModsTheory.range_header_init_mods, bodyFullForArrayRoundTheory.for_nonslot_array_entry_full, bodyForArrayControlFrameModsTheory.for_array_control_scalar_frame_mods, bodyForRangeHeaderModsTheory.range_header_mods_def, bodyFullForArrayRoundTheory.for_nonslot_array_layout_full, bodyFullForArrayRoundTheory.for_nonslot_array_layout_full_with_increment, bodyFullForRangeTheory.range_full_increment_path, bodyForArrayHeaderModsTheory.for_array_capture_frame_mods_def, bodyForArrayHeaderModsTheory.for_array_item_mods_def, bodyForArrayHeaderModsTheory.for_array_outer_frame_mods_def, bodyFullForArrayRoundTheory.for_nonslot_layout_def, bodyFullPredsModsTheory.body_const_cells_agree_mods_def, bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def, bodyFullPostsModsTheory.immutable_frame_mods_def, unitTransformDefsTheory.dalloca_fmp_headroom_def]) g else (ALL_TAC) g)) >> (fn g => if length (fst g) = 49 andalso String.translate (fn c => if Char.isSpace c then "" else String.str c) (PP.pp_to_string 100 Parse.pp_term (snd g)) = "∃bbi1i2i3.lookup_blocks.vs_current_bbfunc.fn_blocks=SOMEbb∧get_instructionbb(SUC(SUCs.vs_inst_idx))=SOME(mk_insti3JMP[Labelcond][])∧get_instructionbb(SUCs.vs_inst_idx)=SOME(mk_insti2ASSIGN[Varnext_var][idx])∧get_instructionbbs.vs_inst_idx=SOME(mk_insti1ADD[Varidx;Lit1w][next_var])" then (metis_tac[]) g else (ALL_TAC) g))
  >- simp[]
QED

Finalise for_array_increment_header_path_mods
