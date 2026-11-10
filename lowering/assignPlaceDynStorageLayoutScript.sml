(* Compiler boundaries for runtime-length memory-to-storage copies. *)
Theory assignPlaceDynStorageLayout
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  immutableCopyExecution fragExec loweringSlice list rich_list
Libs
  monadsyntax

Theorem dyn_storage_compile_boundaries:
  compile_dynarray_to_storage src dst ew ems tr sa = ((),sb) ==>
  ?len hdr body exit cv lt done oldh oldb olde
    s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    scaled off sp slot_scaled slot_off dp value next
    b1 b2 b3 b4 b5 b6 b7 b8 b9 be bx b1' u.
    emit_op MLOAD [src] sa = (len,s1) /\
    fresh_label "dyn_cond" s1 = (hdr,s2) /\
    fresh_label "dyn_body" s2 = (body,s3) /\
    fresh_label "dyn_exit" s3 = (exit,s4) /\
    fresh_var s4 = (cv,s5) /\
    emit_inst ASSIGN [Lit 0w] [cv] s5 = ((),s6) /\
    emit_inst JMP [Label hdr] [] s6 = ((),s7) /\
    new_block hdr s7 = (oldh,s8) /\
    emit_op LT [Var cv;len] s8 = (lt,s9) /\
    emit_op ISZERO [lt] s9 = (done,s10) /\
    emit_inst JNZ [done;Label exit;Label body] [] s10 = ((),s11) /\
    new_block body s11 = (oldb,b1) /\
    emit_op MUL [Var cv;Lit (n2w (if ew = 1 then 32 else ems))] b1 = (scaled,b2) /\
    emit_op ADD [Lit 32w;scaled] b2 = (off,b3) /\
    emit_op ADD [src;off] b3 = (sp,b4) /\
    (if ew = 1 then
       emit_op MLOAD [sp] b4 = (value,b5) /\
       emit_op ADD [Var cv;Lit 1w] b5 = (slot_off,b6) /\
       emit_op ADD [dst;slot_off] b6 = (dp,b7) /\
       emit_void (if tr then TSTORE else SSTORE) [dp;value] b7 = ((),b8)
     else
       emit_op MUL [Var cv;Lit (n2w ew)] b4 = (slot_scaled,b5) /\
       emit_op ADD [Lit 1w;slot_scaled] b5 = (slot_off,b6) /\
       emit_op ADD [dst;slot_off] b6 = (dp,b7) /\
       compile_word_copy_loop sp dp ew LocMemory
         (if tr then LocTransient else LocStorage) F b7 = (u,b8)) /\
    emit_op ADD [Var cv;Lit 1w] b8 = (next,b9) /\
    emit_inst ASSIGN [next] [cv] b9 = ((),be) /\
    emit_inst JMP [Label hdr] [] be = ((),bx) /\
    new_block exit bx = (olde,b1') /\
    emit_void (if tr then TSTORE else SSTORE) [dst;len] b1' = ((),sb) /\
    (!func. fn_has_code sa sb func ==>
      fn_has_code sa b7 func /\ fn_has_code b7 b8 func /\
      fn_has_code b8 sb func)
Proof
  strip_tac >> Cases_on `ew = 1` >> Cases_on `tr` >>
  gvs[Once compile_dynarray_to_storage_def, comp_ignore_bind_def,
      comp_bind_assoc, immutable_comp_bind_cases]
  >> IF (rename1 `compile_word_copy_loop sp dp ew LocMemory loc F mid = (u,en)`)
    (`cs_extends mid en` by
      (qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` mp_tac >>
       rpt (pop_assum kall_tac) >>
       metis_tac[ci_mono_compile_word_copy_loop, ci_mono_def, pairTheory.SND]))
    all_tac >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac cs_extends_fresh_label >>
  imp_res_tac cs_extends_fresh_var >> imp_res_tac cs_extends_new_block >>
  gen_tac >> strip_tac >> rpt conj_tac >>
  match_mp_tac fn_has_code_mid >> goal_assum (drule_at Any) >>
  simp[cs_extends_refl] >> rpt conj_tac >>
  rpt (irule cs_extends_trans >> first_assum (irule_at (Pos hd)) >>
       simp[cs_extends_refl])
QED

Theorem dyn_storage_entry_layout:
  !src sa len s1 hdr s2 body s3 exit s4 cv s5 s6.
  emit_op MLOAD [src] sa = (len,s1) /\
  fresh_label "dyn_cond" s1 = (hdr,s2) /\
  fresh_label "dyn_body" s2 = (body,s3) /\
  fresh_label "dyn_exit" s3 = (exit,s4) /\
  fresh_var s4 = (cv,s5) /\
  emit_inst ASSIGN [Lit 0w] [cv] s5 = ((),s6) ==>
  ?lv. len = Var lv /\ lv <> cv /\
    same_blocks sa s6 /\ isPREFIX sa.cs_current_insts s6.cs_current_insts /\
    s6.cs_next_id = sa.cs_next_id + 2 /\
    s6.cs_next_var = sa.cs_next_var + 2 /\
    emitted_insts sa s6 =
      [mk_inst sa.cs_next_id MLOAD [src] [lv];
       mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [cv]] /\
    (!x. not_fresh_at sa x ==> x <> lv /\ x <> cv)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, fresh_label_def, fresh_var_def, emit_inst_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem dyn_storage_header_layout:
  emit_op LT [Var cv;len] sa = (lt,s1) /\
  emit_op ISZERO [lt] s1 = (done,s2) ==>
  ?tv dv. lt = Var tv /\ done = Var dv /\ tv <> dv /\
    same_blocks sa s2 /\ isPREFIX sa.cs_current_insts s2.cs_current_insts /\
    s2.cs_next_id = sa.cs_next_id + 2 /\
    s2.cs_next_var = sa.cs_next_var + 2 /\
    emitted_insts sa s2 =
      [mk_inst sa.cs_next_id LT [Var cv;len] [tv];
       mk_inst (sa.cs_next_id+1) ISZERO [Var tv] [dv]] /\
    (!x. not_fresh_at sa x ==> x <> tv /\ x <> dv)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem dyn_storage_scaled_address_layout:
  emit_op MUL [Var cv;Lit (n2w stride)] sa = (scaled,s1) /\
  emit_op ADD [Lit bias;scaled] s1 = (off,s2) /\
  emit_op ADD [src;off] s2 = (sp,s3) ==>
  ?mv ov pv. scaled = Var mv /\ off = Var ov /\ sp = Var pv /\
    ALL_DISTINCT [mv;ov;pv] /\
    same_blocks sa s3 /\ isPREFIX sa.cs_current_insts s3.cs_current_insts /\
    s3.cs_next_var = sa.cs_next_var + 3 /\
    emitted_insts sa s3 =
      [mk_inst sa.cs_next_id MUL [Var cv;Lit (n2w stride)] [mv];
       mk_inst (sa.cs_next_id+1) ADD [Lit bias;Var mv] [ov];
       mk_inst (sa.cs_next_id+2) ADD [src;Var ov] [pv]] /\
    (!x. not_fresh_at sa x ==> ~MEM x [mv;ov;pv])
Proof
  strip_tac >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem dyn_storage_increment_layout:
  emit_op ADD [Var cv;Lit 1w] sa = (next,s1) /\
  emit_inst ASSIGN [next] [cv] s1 = ((),s2) ==>
  ?nv. next = Var nv /\
    same_blocks sa s2 /\ isPREFIX sa.cs_current_insts s2.cs_current_insts /\
    s2.cs_next_var = sa.cs_next_var + 1 /\
    emitted_insts sa s2 =
      [mk_inst sa.cs_next_id ADD [Var cv;Lit 1w] [nv];
       mk_inst (sa.cs_next_id+1) ASSIGN [Var nv] [cv]] /\
    (!x. not_fresh_at sa x ==> x <> nv)
Proof
  strip_tac >>
  gvs[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem dyn_storage_singleton_layout:
  emit_op MLOAD [sp] sa = (value,s1) /\
  emit_op ADD [Var cv;Lit 1w] s1 = (off,s2) /\
  emit_op ADD [dst;off] s2 = (dp,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dp;value] s3 = ((),s4) ==>
  ?vv ov pv. value = Var vv /\ off = Var ov /\ dp = Var pv /\
    ALL_DISTINCT [vv;ov;pv] /\
    same_blocks sa s4 /\ isPREFIX sa.cs_current_insts s4.cs_current_insts /\
    s4.cs_next_var = sa.cs_next_var + 3 /\
    emitted_insts sa s4 =
      [mk_inst sa.cs_next_id MLOAD [sp] [vv];
       mk_inst (sa.cs_next_id+1) ADD [Var cv;Lit 1w] [ov];
       mk_inst (sa.cs_next_id+2) ADD [dst;Var ov] [pv];
       mk_inst (sa.cs_next_id+3) (if tr then TSTORE else SSTORE) [Var pv;Var vv] []] /\
    (!x. not_fresh_at sa x ==> ~MEM x [vv;ov;pv])
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED
