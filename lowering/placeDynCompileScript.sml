Theory placeDynCompile
Ancestors
  list rich_list
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  placeStoreDynPrepare stmtLoweringMono loweringSlice fragExec
Libs
  monadsyntax

Theorem place_dyn_bind_eq[local]:
  comp_bind m f s = (u,t) <=>
  ?v mid. m s = (v,mid) /\ f v mid = (u,t)
Proof
  Cases_on `m s` >> simp[comp_bind_def]
QED

Theorem place_dyn_mono_then[local]:
  f a = (u,b) /\ (!s. ci_mono s (SND (f s))) /\ ci_mono b c ==>
  ci_mono a c
Proof
  strip_tac >>
  `ci_mono a b` by (first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gvs[ci_mono_def] >> rpt conj_tac
  >- (irule cs_extends_trans >> qexists_tac `b` >> simp[]) >>
  decide_tac
QED

val place_dyn_mono_tac =
  rpt (simp[ci_mono_refl] >>
    first_assum (mp_then (Pos hd) irule place_dyn_mono_then) >>
    (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
      ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_new_block,
      ci_mono_compile_word_copy_loop])) >> simp[ci_mono_refl];

val place_dyn_extends_tac =
  irule (cj 1 (iffLR ci_mono_def)) >> place_dyn_mono_tac;

Theorem place_dyn_compile_boundaries:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) ==>
  ?len cond body_lbl exit ctr lt done next old0 old1 old2
   s1 s2 s3 s4 s5 s6 s7 sth s8 s9 s10 stb ste s11 s12 s13 s14.
    emit_op MLOAD [src] sa = (len,s1) /\
    fresh_label "dyn_cond" s1 = (cond,s2) /\
    fresh_label "dyn_body" s2 = (body_lbl,s3) /\
    fresh_label "dyn_exit" s3 = (exit,s4) /\
    fresh_var s4 = (ctr,s5) /\
    emit_inst ASSIGN [Lit 0w] [ctr] s5 = ((),s6) /\
    emit_inst JMP [Label cond] [] s6 = ((),s7) /\
    new_block cond s7 = (old0,sth) /\
    emit_op LT [Var ctr;len] sth = (lt,s8) /\
    emit_op ISZERO [lt] s8 = (done,s9) /\
    emit_inst JNZ [done;Label exit;Label body_lbl] [] s9 = ((),s10) /\
    new_block body_lbl s10 = (old1,stb) /\
    (if ew = 1 then
       ?mul off sp value slot dp b1 b2 b3 b4 b5 b6.
         emit_op MUL [Var ctr;Lit 32w] stb = (mul,b1) /\
         emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
         emit_op ADD [src;off] b2 = (sp,b3) /\
         emit_op MLOAD [sp] b3 = (value,b4) /\
         emit_op ADD [Var ctr;Lit 1w] b4 = (slot,b5) /\
         emit_op ADD [dst;slot] b5 = (dp,b6) /\
         emit_void (if transient then TSTORE else SSTORE) [dp;value] b6 = ((),ste)
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
         (!func. fn_has_code sa sb func ==> fn_has_code b6 ste func)) /\
    emit_op ADD [Var ctr;Lit 1w] ste = (next,s11) /\
    emit_inst ASSIGN [next] [ctr] s11 = ((),s12) /\
    emit_inst JMP [Label cond] [] s12 = ((),s13) /\
    new_block exit s13 = (old2,s14) /\
    emit_void (if transient then TSTORE else SSTORE) [dst;len] s14 = ((),sb) /\
    ci_mono sa s6 /\ ci_mono s6 sth /\ ci_mono sth s9 /\
    ci_mono s9 stb /\ ci_mono stb ste /\ ci_mono ste s12 /\
    ci_mono s12 s14 /\ ci_mono s14 sb /\
    (!func. fn_has_code sa sb func ==>
      fn_has_code sa s6 func /\ fn_has_code s6 sth func /\
      fn_has_code sth s9 func /\ fn_has_code s9 stb func /\
      fn_has_code stb ste func /\ fn_has_code ste s12 func /\
      fn_has_code s12 s14 func /\ fn_has_code s14 sb func)
Proof
  strip_tac >> Cases_on `ew = 1` >> Cases_on `transient` >>
  gvs[compile_dynarray_to_storage_def, comp_ignore_bind_def,
      comp_bind_assoc, place_dyn_bind_eq] >>
  rpt conj_tac >> place_dyn_mono_tac >>
  rpt gen_tac >> strip_tac >> rpt conj_tac >>
  irule (cj 2 fn_has_code_split) >>
  (conj_tac >- place_dyn_extends_tac) >> qexists_tac `sa` >>
  (conj_tac >- place_dyn_extends_tac) >>
  irule (cj 1 fn_has_code_split) >>
  (conj_tac >- place_dyn_extends_tac) >> qexists_tac `sb` >>
  simp[] >> place_dyn_extends_tac
QED

Theorem place_dyn_prefix_layout:
  emit_op MLOAD [src] sa = (len,s1) /\
  fresh_label "dyn_cond" s1 = (cond,s2) /\
  fresh_label "dyn_body" s2 = (body_lbl,s3) /\
  fresh_label "dyn_exit" s3 = (exit,s4) /\
  fresh_var s4 = (ctr,s5) /\
  emit_inst ASSIGN [Lit 0w] [ctr] s5 = ((),s6) /\
  emit_inst JMP [Label cond] [] s6 = ((),s7) /\
  new_block cond s7 = (old0,sth) /\
  emit_op LT [Var ctr;len] sth = (lt,s8) /\
  emit_op ISZERO [lt] s8 = (done,s9) /\
  emit_inst JNZ [done;Label exit;Label body_lbl] [] s9 = ((),s10) /\
  new_block body_lbl s10 = (old1,stb) ==>
  ?lv tv dv.
    len = Var lv /\ lt = Var tv /\ done = Var dv /\
    ALL_DISTINCT [lv;ctr;tv;dv] /\ ALL_DISTINCT [cond;body_lbl;exit] /\
    (!x. not_fresh_at sa x ==> ~MEM x [lv;ctr;tv;dv]) /\
    (!x. not_fresh_at sa x ==> not_fresh_at stb x) /\
    EVERY (not_fresh_at stb) [lv;ctr;tv;dv] /\
    same_blocks sa s6 /\ isPREFIX sa.cs_current_insts s6.cs_current_insts /\
    emitted_insts sa s6 =
      [mk_inst sa.cs_next_id MLOAD [src] [lv];
       mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr]] /\
    same_blocks sth s9 /\ isPREFIX sth.cs_current_insts s9.cs_current_insts /\
    emitted_insts sth s9 =
      [mk_inst sth.cs_next_id LT [Var ctr;Var lv] [tv];
       mk_inst (sth.cs_next_id+1) ISZERO [Var tv] [dv]] /\
    stb.cs_next_var = sa.cs_next_var + 4 /\
    stb.cs_next_id = sa.cs_next_id + 6
Proof
  strip_tac >>
  gvs[fresh_label_def, fresh_var_def, new_block_def, emit_inst_def,
      emit_op_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, not_fresh_at_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def, fresh_var_distinct] >>
  strip_tac >> drule fresh_label_output_inj >> simp[]
QED

Theorem place_dyn_single_body_layout:
  !ctr stb mul b1 off b2 src sp b3 value b4 slot b5 dst dp b6 transient ste.
  emit_op MUL [Var ctr;Lit 32w] stb = (mul,b1) /\
  emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
  emit_op ADD [src;off] b2 = (sp,b3) /\
  emit_op MLOAD [sp] b3 = (value,b4) /\
  emit_op ADD [Var ctr;Lit 1w] b4 = (slot,b5) /\
  emit_op ADD [dst;slot] b5 = (dp,b6) /\
  emit_void (if transient then TSTORE else SSTORE) [dp;value] b6 = ((),ste) ==>
  ?mv ov sv vv kv dv.
    mul = Var mv /\ off = Var ov /\ sp = Var sv /\
    value = Var vv /\ slot = Var kv /\ dp = Var dv /\
    ALL_DISTINCT [mv;ov;sv;vv;kv;dv] /\
    (!x. not_fresh_at stb x ==> ~MEM x [mv;ov;sv;vv;kv;dv]) /\
    same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
    ste.cs_next_var = stb.cs_next_var + 6 /\ ste.cs_next_id = stb.cs_next_id + 7 /\
    emitted_insts stb ste =
      [mk_inst stb.cs_next_id MUL [Var ctr;Lit 32w] [mv];
       mk_inst (stb.cs_next_id+1) ADD [Lit 32w;Var mv] [ov];
       mk_inst (stb.cs_next_id+2) ADD [src;Var ov] [sv];
       mk_inst (stb.cs_next_id+3) MLOAD [Var sv] [vv];
       mk_inst (stb.cs_next_id+4) ADD [Var ctr;Lit 1w] [kv];
       mk_inst (stb.cs_next_id+5) ADD [dst;Var kv] [dv];
       mk_inst (stb.cs_next_id+6) (if transient then TSTORE else SSTORE)
         [Var dv;Var vv] []]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, not_fresh_at_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[] >> first_x_assum irule >> simp[]
QED

Theorem place_dyn_multi_address_layout:
  !ctr ems stb mul b1 off b2 src sp b3 ew smul b4 slot b5 dst dp b6.
  emit_op MUL [Var ctr;Lit (n2w ems)] stb = (mul,b1) /\
  emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
  emit_op ADD [src;off] b2 = (sp,b3) /\
  emit_op MUL [Var ctr;Lit (n2w ew)] b3 = (smul,b4) /\
  emit_op ADD [Lit 1w;smul] b4 = (slot,b5) /\
  emit_op ADD [dst;slot] b5 = (dp,b6) ==>
  ?mv ov sv km kv dv.
    mul = Var mv /\ off = Var ov /\ sp = Var sv /\
    smul = Var km /\ slot = Var kv /\ dp = Var dv /\
    ALL_DISTINCT [mv;ov;sv;km;kv;dv] /\
    (!x. not_fresh_at stb x ==> ~MEM x [mv;ov;sv;km;kv;dv]) /\
    same_blocks stb b6 /\ isPREFIX stb.cs_current_insts b6.cs_current_insts /\
    b6.cs_next_var = stb.cs_next_var + 6 /\ b6.cs_next_id = stb.cs_next_id + 6 /\
    emitted_insts stb b6 =
      [mk_inst stb.cs_next_id MUL [Var ctr;Lit (n2w ems)] [mv];
       mk_inst (stb.cs_next_id+1) ADD [Lit 32w;Var mv] [ov];
       mk_inst (stb.cs_next_id+2) ADD [src;Var ov] [sv];
       mk_inst (stb.cs_next_id+3) MUL [Var ctr;Lit (n2w ew)] [km];
       mk_inst (stb.cs_next_id+4) ADD [Lit 1w;Var km] [kv];
       mk_inst (stb.cs_next_id+5) ADD [dst;Var kv] [dv]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, not_fresh_at_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[] >> first_x_assum irule >> simp[]
QED

Theorem place_dyn_tail_layout:
  emit_op ADD [Var ctr;Lit 1w] ste = (next,s11) /\
  emit_inst ASSIGN [next] [ctr] s11 = ((),s12) /\
  emit_inst JMP [Label cond] [] s12 = ((),s13) /\
  new_block exit s13 = (old2,s14) /\
  emit_void (if transient then TSTORE else SSTORE) [dst;len] s14 = ((),sb) ==>
  ?nv. next = Var nv /\
    (!x. not_fresh_at ste x ==> x <> nv) /\
    same_blocks ste s12 /\ isPREFIX ste.cs_current_insts s12.cs_current_insts /\
    emitted_insts ste s12 =
      [mk_inst ste.cs_next_id ADD [Var ctr;Lit 1w] [nv];
       mk_inst (ste.cs_next_id+1) ASSIGN [Var nv] [ctr]] /\
    same_blocks s14 sb /\ isPREFIX s14.cs_current_insts sb.cs_current_insts /\
    emitted_insts s14 sb =
      [mk_inst s14.cs_next_id (if transient then TSTORE else SSTORE) [dst;len] []] /\
    sb.cs_next_var = ste.cs_next_var + 1 /\ sb.cs_next_id = ste.cs_next_id + 4
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, new_block_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, not_fresh_at_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[] >> first_x_assum irule >> simp[]
QED
