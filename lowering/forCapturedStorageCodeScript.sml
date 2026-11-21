(* Static code facts at the already chosen storage iterator expression cut. *)
Theory forCapturedStorageCode
Ancestors
  bodyFullForArrayRound copyExecution exprPtrUnwrapRuntimeFrame
  exprSafeOperand exprSafeOperandBuiltins exprLowering emitHelperProps
  exprLoweringProps loweringPosts stmtLowering targetPlaceSim
  vyperTypeContract[qualified,ignore_grammar] loweringStateRelDefs
  fragExec context compileEnv emitHelper venomInst venomExecSemantics
  vyperAST rich_list list arithmetic ASCIInumbers

Theorem nested_iterator_operand_not_label[local]:
  compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\
  loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
  ~(?ty nid. e = TopLevelName ty nid) ==>
  !lbl. vv_operand vv <> Label lbl
Proof
  Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def] >>
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
  rpt strip_tac >> gvs[target_root_def]
  >- (drule compile_subscript_not_label >> simp[]) >>
  drule compile_attribute_safe_operand >> simp[safe_operand_def]
QED

Theorem captured_storage_address[local]:
  emit_op MUL [Var idx; Lit (n2w stride)] sa = (off_op,sm) /\
  (if dyn then emit_op ADD [Lit 1w;off_op] sm = (sum_op,sn)
   else sum_op = off_op /\ sn = sm) /\
  emit_op ADD [bop;sum_op] sn = (addr,saCopy) /\
  sa.cs_current_insts = [] /\ sa.cs_current_bb = bod /\
  not_fresh_at sa done_var /\ fn_has_code sa saCopy func ==>
  ?ov tot ep bb.
    off_op = Var ov /\ sum_op = Var (if dyn then tot else ov) /\ addr = Var ep /\
    saCopy.cs_current_bb = bod /\
    saCopy.cs_current_insts =
      [mk_inst sa.cs_next_id MUL [Var idx; Lit (n2w stride)] [ov]] ++
      (if dyn then [mk_inst (sa.cs_next_id + 1) ADD [Lit 1w; Var ov] [tot]]
       else []) ++
      [mk_inst (sa.cs_next_id + if dyn then 2 else 1) ADD
         [bop;Var (if dyn then tot else ov)] [ep]] /\
    lookup_block bod func.fn_blocks = SOME bb /\
    (!j. j < LENGTH saCopy.cs_current_insts ==>
         get_instruction bb j = SOME (fEL saCopy.cs_current_insts j)) /\
    ALL_DISTINCT (if dyn then [done_var;ov;tot;ep] else [done_var;ov;ep]) /\
    (!x. not_fresh_at sa x ==> ~MEM x (if dyn then [ov;tot;ep] else [ov;ep])) /\
    not_fresh_at saCopy ep
Proof
  Cases_on `dyn` >> simp[] >> strip_tac >>
  imp_res_tac emit_op_same_blocks >> imp_res_tac emitted_insts_emit_op >>
  gvs[same_blocks_def] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
     !j. j < LENGTH saCopy.cs_current_insts ==>
         get_instruction bb j = SOME (fEL saCopy.cs_current_insts j)` by
    (drule fn_has_code_same_block >>
     disch_then (qspec_then `saCopy.cs_current_insts` mp_tac) >> simp[]) >>
  qexists_tac `bb` >>
  gvs[ADD_ASSOC, toString_11, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem captured_storage_copy[local]:
  compile_iter_elem_copy c addr (Var xd) stride (slot_loc tr) T fty sty
    saCopy = ((),sbCopy) ==>
  compile_slot_to_memory addr (Var xd) stride (slot_loc tr) saCopy =
    (slot_copy_body saCopy,sbCopy) /\
  sbCopy = slot_copy_final saCopy addr (Var xd) stride (if tr then TLOAD else SLOAD)
Proof
  Cases_on `tr` >>
  simp[slot_loc_def, compile_iter_elem_copy_def, compile_slot_to_memory_shape,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem for_captured_storage_code:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  not_fresh_at sa done_var /\ loc = slot_loc tr /\
  loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
  ~(?ty nid. e = TopLevelName ty nid) ==>
  let bop = vv_operand vv; h = sa.cs_next_id;
      dyn = case bd of Fixed _ => F | Dynamic _ => T in
    (!lbl. bop <> Label lbl) /\
    (case bd of Fixed cnt => len_op = Lit (n2w cnt) /\ saL = sbExpr
     | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca (slot_loc tr)
                   bop sbExpr = (len_op,saL)) /\
    stride = elem_size_in_location c (slot_loc tr) sty /\
    ?ov tot ep cb bb.
      off_op = Var ov /\ sum_op = Var (if dyn then tot else ov) /\ addr = Var ep /\
      lookup_block cond func.fn_blocks = SOME cb /\
      cb.bb_instructions =
        [mk_inst (h - 2) EQ [Var idx;len_op] [done_var];
         mk_inst (h - 1) JNZ [Var done_var;Label exit;Label bod] []] /\
      lookup_block bod func.fn_blocks = SOME bb /\ saCopy.cs_current_bb = bod /\
      saCopy.cs_current_insts =
        [mk_inst h MUL [Var idx; Lit (n2w stride)] [ov]] ++
        (if dyn then [mk_inst (h + 1) ADD [Lit 1w;Var ov] [tot]] else []) ++
        [mk_inst (h + if dyn then 2 else 1) ADD [bop;Var (if dyn then tot else ov)] [ep]] /\
      (!j. j < LENGTH saCopy.cs_current_insts ==>
           get_instruction bb j = SOME (fEL saCopy.cs_current_insts j)) /\
      let outs = if dyn then [done_var;ov;tot;ep] else [done_var;ov;ep] in
        ALL_DISTINCT outs /\ ~MEM idx outs /\ ~MEM xd outs /\
        (!x. len_op = Var x \/ bop = Var x ==> ~MEM x outs) /\
        (!x. MEM x outs ==> ~not_fresh_at sa0 x) /\
        compile_slot_to_memory (Var ep) (Var xd) stride (slot_loc tr) saCopy =
          (slot_copy_body saCopy,sbCopy) /\
        sbCopy = slot_copy_final saCopy (Var ep) (Var xd) stride
                   (if tr then TLOAD else SLOAD) /\
        slot_copy_external saCopy (Var ep)
Proof
  strip_tac >> qpat_x_assum `loc = slot_loc tr` SUBST_ALL_TAC >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [for_nonslot_layout_def, LET_THM]) >>
  qpat_x_assum `slot_loc tr = _` kall_tac >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  conj_tac >- (irule nested_iterator_operand_not_label >> metis_tac[]) >>
  conj_tac >- (Cases_on `bd` >> gvs[comp_return_def]) >>
  conj_tac >- simp[] >>
  `word_scale (slot_loc tr) = 1 /\ is_slot_addressed (slot_loc tr)` by
    (Cases_on `tr` >> simp[slot_loc_def, word_scale_def, is_slot_addressed_def]) >>
  `if (case bd of Fixed _ => F | Dynamic _ => T) then
     emit_op ADD [Lit 1w;off_op] sm = (sum_op,sn)
   else sum_op = off_op /\ sn = sm` by
    (Cases_on `bd` >> gvs[]) >>
  qpat_assum `not_fresh_at sa done_var`
    (mp_then (Pat `not_fresh_at _ _`) (drule_all_then strip_assume_tac)
       captured_storage_address) >>
  `compile_iter_elem_copy c (Var ep) (Var xd) stride (slot_loc tr) T fty sty
     saCopy = ((),sbCopy)` by gvs[] >>
  drule captured_storage_copy >> strip_tac >>
  qpat_assum `not_fresh_at saCopy ep`
    (mp_then Any assume_tac slot_copy_not_fresh_external) >>
  qexistsl [`ov`,`tot`,`ep`] >> simp[] >>
  `ci_mono saL sa` by (irule ci_mono_trans >> qexists `saA` >> simp[]) >>
  `sa0.cs_next_var <= saL.cs_next_var /\ saL.cs_next_var <= sa.cs_next_var` by
    fs[ci_mono_def] >>
  map_every (fn p => qpat_assum p mp_tac)
    [`!x. not_fresh_at sa x ==> _`, `not_fresh_at sa idx`, `not_fresh_at sa xd`,
     `idx <> done_var`, `xd <> done_var`, `~not_fresh_at saL done_var`,
     `!x. vv_operand vv = Var x \/ len_op = Var x ==> not_fresh_at saL x`,
     `sa0.cs_next_var <= saL.cs_next_var`, `saL.cs_next_var <= sa.cs_next_var`] >>
  POP_ASSUM_LIST (K all_tac) >> Cases_on `bd` >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
