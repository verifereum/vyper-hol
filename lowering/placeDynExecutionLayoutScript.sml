Theory placeDynExecutionLayout
Ancestors
  placeDynCompile fragExec loweringSlice compileEnv emitHelper exprLoweringProps
  list rich_list arithmetic emitHelperProps

Theorem place_dyn_closed_slice[local]:
  same_blocks a z /\ isPREFIX a.cs_current_insts z.cs_current_insts /\
  emit_inst opc args outs z = ((),y) /\
  new_block label y = (old,q) /\ fn_has_code z q func ==>
  ?bb. lookup_block a.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts a z ++ [mk_inst z.cs_next_id opc args outs])
      (DROP (LENGTH a.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >>
  `?bb. lookup_block z.cs_current_bb func.fn_blocks = SOME bb /\
    bb.bb_instructions = z.cs_current_insts ++
      [mk_inst z.cs_next_id opc args outs]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     qpat_x_assum `new_block _ _ = _` mp_tac >>
     qpat_x_assum `fn_has_code z q func` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
       new_block_def, fn_has_code_def, emitted_blocks_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qexists_tac `bb` >>
  qpat_x_assum `isPREFIX a.cs_current_insts _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  qpat_x_assum `same_blocks _ _` (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
  conj_tac >- metis_tac[] >>
  pure_asm_rewrite_tac [emitted_insts_def, GSYM APPEND_ASSOC,
    DROP_LENGTH_APPEND] >>
  simp[]
QED

Theorem place_dyn_execution_layout:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?lv ctr tv dv nv cond body_lbl exit stb ste ih it ix bb0 bbh bbt bbx.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
    isPREFIX [mk_inst sa.cs_next_id MLOAD [src] [lv];
              mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr];
              mk_inst (sa.cs_next_id+2) JMP [Label cond] []]
      (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions) /\
    lookup_block cond func.fn_blocks = SOME bbh /\
    isPREFIX [mk_inst ih LT [Var ctr;Var lv] [tv];
              mk_inst (ih+1) ISZERO [Var tv] [dv];
              mk_inst (ih+2) JNZ [Var dv;Label exit;Label body_lbl] []]
      bbh.bb_instructions /\
    lookup_block ste.cs_current_bb func.fn_blocks = SOME bbt /\
    isPREFIX [mk_inst it ADD [Var ctr;Lit 1w] [nv];
              mk_inst (it+1) ASSIGN [Var nv] [ctr];
              mk_inst (it+2) JMP [Label cond] []]
      (DROP (LENGTH ste.cs_current_insts) bbt.bb_instructions) /\
    lookup_block exit func.fn_blocks = SOME bbx /\
    isPREFIX [mk_inst ix (if transient then TSTORE else SSTORE)
                [dst;Var lv] []] bbx.bb_instructions /\
    sb.cs_current_bb = exit /\ LENGTH sb.cs_current_insts = 1 /\
    stb.cs_current_bb = body_lbl /\ stb.cs_current_insts = [] /\
    fn_has_code stb ste func /\
    (if ew = 1 then
       ?mul off sp value slot dp b1 b2 b3 b4 b5 b6.
         emit_op MUL [Var ctr;Lit 32w] stb = (mul,b1) /\
         emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
         emit_op ADD [src;off] b2 = (sp,b3) /\
         emit_op MLOAD [sp] b3 = (value,b4) /\
         emit_op ADD [Var ctr;Lit 1w] b4 = (slot,b5) /\
         emit_op ADD [dst;slot] b5 = (dp,b6) /\
         emit_void (if (if transient then LocTransient else LocStorage) = LocStorage
           then SSTORE else TSTORE) [dp;value] b6 = ((),ste)
     else
       ?mul off sp smul slot dp oldcopy b1 b2 b3 b4 b5 b6.
         emit_op MUL [Var ctr;Lit (n2w ems)] stb = (mul,b1) /\
         emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
         emit_op ADD [src;off] b2 = (sp,b3) /\
         emit_op MUL [Var ctr;Lit (n2w ew)] b3 = (smul,b4) /\
         emit_op ADD [Lit 1w;smul] b4 = (slot,b5) /\
         emit_op ADD [dst;slot] b5 = (dp,b6) /\
         compile_word_copy_loop sp dp ew LocMemory
           (if transient then LocTransient else LocStorage) F b6 = (oldcopy,ste) /\
         fn_has_code b6 ste func) /\
    ALL_DISTINCT [lv;ctr;tv;dv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [lv;ctr;tv;dv]) /\
    (!x. not_fresh_at sa x ==> not_fresh_at stb x) /\
    EVERY (not_fresh_at stb) [lv;ctr;tv;dv] /\
    (!x. not_fresh_at stb x ==> not_fresh_at ste x) /\
    (!x. not_fresh_at ste x ==> x <> nv)
Proof
  strip_tac >> drule place_dyn_compile_boundaries >> strip_tac >>
  drule_all place_dyn_prefix_layout >> strip_tac >>
  drule_all place_dyn_tail_layout >> strip_tac >>
  qpat_x_assum `!func. fn_has_code sa sb func ==> _` drule >> strip_tac >>
  `?bb0. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
    isPREFIX (emitted_insts sa s6 ++
      [mk_inst s6.cs_next_id JMP [Label cond] []])
      (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions)` by
    (qpat_assum `same_blocks sa s6`
       (mp_then Any mp_tac place_dyn_closed_slice) >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[Excl "isPREFIX"]) >>
  `?bbh. lookup_block sth.cs_current_bb func.fn_blocks = SOME bbh /\
    isPREFIX (emitted_insts sth s9 ++
      [mk_inst s9.cs_next_id JNZ [done;Label exit;Label body_lbl] []])
      (DROP (LENGTH sth.cs_current_insts) bbh.bb_instructions)` by
    (qpat_assum `same_blocks sth s9`
       (mp_then Any mp_tac place_dyn_closed_slice) >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[Excl "isPREFIX"]) >>
  `?bbt. lookup_block ste.cs_current_bb func.fn_blocks = SOME bbt /\
    isPREFIX (emitted_insts ste s12 ++
      [mk_inst s12.cs_next_id JMP [Label cond] []])
      (DROP (LENGTH ste.cs_current_insts) bbt.bb_instructions)` by
    (qpat_assum `same_blocks ste s12`
       (mp_then Any mp_tac place_dyn_closed_slice) >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[Excl "isPREFIX"]) >>
  suspend "package"
QED
Resume place_dyn_execution_layout[package]:
  `s5.cs_next_id = s4.cs_next_id` by
    (qpat_x_assum `fresh_var s4 = _` mp_tac >>
     simp[fresh_var_def] >> strip_tac >> gvs[]) >>
  imp_res_tac fresh_label_props >>
  imp_res_tac new_block_props >>
  imp_res_tac emit_inst_extends >>
  imp_res_tac emitted_insts_emit_op >>
  `s6.cs_next_id = sa.cs_next_id+2 /\
   s9.cs_next_id = sth.cs_next_id+2 /\
   s12.cs_next_id = ste.cs_next_id+2` by decide_tac >>
  imp_res_tac emitted_insts_emit_void >>
  `sb.cs_current_bb = exit /\
   sb.cs_current_insts = [mk_inst s14.cs_next_id
     (if transient then TSTORE else SSTORE) [dst;Var lv] []]` by
    (fs[same_blocks_def, Excl "isPREFIX"]) >>
  `?bbx. lookup_block exit func.fn_blocks = SOME bbx /\
    isPREFIX [mk_inst s14.cs_next_id (if transient then TSTORE else SSTORE)
      [dst;Var lv] []] bbx.bb_instructions` by
    (qpat_assum `fn_has_code s14 sb func`
       (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     metis_tac[]) >>
  qexistsl_tac [`lv`, `ctr`, `tv`, `dv`, `nv`, `cond`, `body_lbl`, `exit`,
    `stb`, `ste`, `sth.cs_next_id`, `ste.cs_next_id`, `s14.cs_next_id`,
    `bb0`, `bbh`, `bbt`, `bbx`] >>
  simp[Excl "isPREFIX"] >>
  suspend "remaining"
QED
Resume place_dyn_execution_layout[remaining]:
  conj_tac >-
    (qpat_x_assum `isPREFIX (emitted_insts sa s6 ++ _) _` mp_tac >>
     simp[Excl "isPREFIX"]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qpat_x_assum `isPREFIX (emitted_insts sth s9 ++ _) _` mp_tac >>
     qpat_assum `emitted_insts sth s9 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `done = Var dv` (fn th => rewrite_tac[th]) >>
     qpat_assum `s9.cs_next_id = sth.cs_next_id + 2`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `sth.cs_current_insts = []` (fn th => rewrite_tac[th]) >>
     simp[Excl "isPREFIX"]) >>
  conj_tac >-
    (qpat_x_assum `isPREFIX (emitted_insts ste s12 ++ _) _` mp_tac >>
     simp[Excl "isPREFIX"]) >>
  conj_tac >-
    (qpat_x_assum `if ew = 1 then _ else _` mp_tac >>
     qpat_assum `fn_has_code sa sb func` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `ew = 1` >> Cases_on `transient` >>
     simp[] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `ci_mono stb ste` mp_tac >>
     simp[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED
Finalise place_dyn_execution_layout
