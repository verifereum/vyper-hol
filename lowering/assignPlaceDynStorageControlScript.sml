(* Phase certificates for the dynamic storage loop.  The nested copy may
   change blocks, so the body is kept as compiler slices, not a flat list. *)
Theory assignPlaceDynStorageControl
Ancestors
  assignPlaceDynStorageLayout fragExec exprLoweringProps compileEnv
  emitHelper emitHelperProps list rich_list


Theorem dyn_storage_compile_phase_certificate:
  compile_dynarray_to_storage src dst ew ems tr sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?len hdr body exit cv lt done
    s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    scaled off sp slot_scaled slot_off dp value next
    b1 b2 b3 b4 b5 b6 b7 b8 b9 be bx ex oldh oldb olde u.
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
    new_block exit bx = (olde,ex) /\
    emit_void (if tr then TSTORE else SSTORE) [dst;len] ex = ((),sb) /\
    fn_has_code sa s6 func /\ fn_has_code s6 ex func /\
    fn_has_code s8 s10 func /\ fn_has_code b1 b4 func /\
    fn_has_code b4 b7 func /\ fn_has_code b7 b8 func /\
    fn_has_code b4 b8 func /\ fn_has_code b8 be func /\
    fn_has_code ex sb func /\ cs_extends b1 be /\ cs_extends s8 s10 /\
    s5.cs_next_var <= b1.cs_next_var /\
    b1.cs_next_var <= b4.cs_next_var /\
    b4.cs_next_var <= b7.cs_next_var /\
    b7.cs_next_var <= b8.cs_next_var /\
    b8.cs_next_var <= be.cs_next_var
Proof
  strip_tac >> drule dyn_storage_compile_boundaries >> strip_tac >>
  Cases_on `ew = 1` >> gvs[] >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  `cs_extends b7 b8` by
    (metis_tac[ci_mono_compile_word_copy_loop, ci_mono_def, pairTheory.SND]) >>
  imp_res_tac cs_extends_fresh_label >>
  imp_res_tac cs_extends_fresh_var >> imp_res_tac cs_extends_new_block >>
  `cs_extends b1 be` by
    (rpt (irule cs_extends_trans >> first_assum (irule_at (Pos hd)) >>
          simp[cs_extends_refl])) >>
  `cs_extends s8 s10` by metis_tac[cs_extends_trans] >>
  `s5.cs_next_var <= b1.cs_next_var /\
   b1.cs_next_var <= b4.cs_next_var /\
   b4.cs_next_var <= b7.cs_next_var /\
   b7.cs_next_var <= b8.cs_next_var /\
   b8.cs_next_var <= be.cs_next_var` by
    (`b7.cs_next_var <= b8.cs_next_var` by
       metis_tac[ci_mono_compile_word_copy_loop, ci_mono_emit_void,
                 ci_mono_def, pairTheory.SND] >>
     gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
         fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, new_block_def] >> decide_tac) >>
  rpt (goal_assum (drule_at Any)) >>
  qpat_x_assum `cs_extends b1 be` kall_tac >>
  qpat_x_assum `cs_extends s8 s10` kall_tac >>
  rpt conj_tac >> (
  irule fn_has_code_mid >>
  conj_tac >- (rpt (irule cs_extends_trans >>
    first_assum (irule_at (Pos hd)) >> simp[cs_extends_refl])) >>
  goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >>
  simp[cs_extends_refl] >>
  rpt conj_tac >>
  rpt (irule cs_extends_trans >> first_assum (irule_at (Pos hd)) >>
       simp[cs_extends_refl]))
QED

Theorem dyn_storage_entry_live:
  emit_op MLOAD [src] sa = (len,s1) /\
  fresh_label "dyn_cond" s1 = (hdr,s2) /\
  fresh_label "dyn_body" s2 = (loop_body,s3) /\
  fresh_label "dyn_exit" s3 = (exit,s4) /\
  fresh_var s4 = (cv,s5) /\ s5.cs_next_var <= mid.cs_next_var ==>
  ?lv. len = Var lv /\ not_fresh_at mid lv /\ not_fresh_at mid cv /\
    (!x. not_fresh_at sa x ==> not_fresh_at mid x)
Proof
  strip_tac >>
  gvs[emit_op_def, fresh_label_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[not_fresh_at_def] >> rpt strip_tac >>
  gvs[fresh_var_distinct] >> first_x_assum irule >> simp[]
QED
