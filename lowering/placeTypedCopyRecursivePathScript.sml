Theory placeTypedCopyRecursivePath
Ancestors
  placeTypedCopyPath placeCopyControlPath typedMemoryCopy fragExec fragGasMode
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv context valueEncoding valueEncodingProps
  venomState venomInst venomExecSemantics words list arithmetic
  vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping pair

Definition typed_copy_forward_entry_def:
  typed_copy_forward_entry cenv ctx dty sty dtv stv v <=>
    !func dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\
          val_in_memory dtv v (w2n dw) t.vs_memory /\
          typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem typed_copy_forward_entry_run:
  typed_copy_forward_entry cenv ctx dty sty dtv stv v /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  (* Instantiate the definition directly; metis_tac[] took 3.3 s. *)
  simp_tac std_ss [typed_copy_forward_entry_def] >> strip_tac >>
  first_x_assum (qspecl_then [`func`,`dst`,`src`,`sa`,`sb`,`s`,`dw`,`sw`]
    mp_tac) >>
  asm_rewrite_tac[]
QED

Theorem typed_copy_forward_offset_path:
  typed_copy_forward_entry cenv ctx dty sty dtv stv v /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
   w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb` by
    metis_tac[typed_copy_offset_mono, cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
   cs_extends s1 sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 sb func` by metis_tac[fn_has_code_split] >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. dp = Var x ==> not_fresh_at s1 x) /\
   (!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x) /\
   (!x. src = Var x ==> not_fresh_at s1 x)` by
    metis_tac[typed_copy_offset_fresh, typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then Any mp_tac place_typed_copy_offset_path) >>
  disch_then drule >>
  disch_then (qspecl_then [`func`, `ctx`, `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `eval_operand src t = SOME sw` by
    (drule_all typed_copy_state_frame_operand >> simp[]) >>
  qpat_assum `compile_with_byte_offset src _ _ = _`
    (mp_then Any mp_tac place_typed_copy_offset_path) >>
  disch_then drule >>
  disch_then (qspecl_then [`func`, `ctx`, `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `eval_operand dp t' = SOME (dw + n2w doff)` by
    (qpat_assum `typed_copy_state_frame s1 _ _ t t'`
       (mp_then Any mp_tac typed_copy_state_frame_operand) >>
     disch_then (qspec_then `dp` mp_tac) >> simp[]) >>
  drule typed_copy_forward_entry_run >> disch_then drule >>
  disch_then (qspecl_then [`sw + n2w soff`, `t'`, `func`, `dw + n2w doff`] mp_tac) >>
  (impl_tac >- gvs[arithmeticTheory.ADD_COMM]) >> strip_tac >>
  `typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t''` by
    (gvs[] >>
     `typed_copy_state_frame sa (doff + w2n dw) (type_memory_size dtv) t t'` by
       (irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[]) >>
     `ci_mono sa s2` by (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
     `typed_copy_state_frame sa (doff + w2n dw) (type_memory_size dtv) t' t''` by
       (irule typed_copy_state_frame_mono >> qexists_tac `s2` >> simp[]) >>
     simp[arithmeticTheory.ADD_COMM] >>
     irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_trans >> qexists_tac `t'` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t')`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t''` >> gvs[]
QED

Definition typed_copy_forward_entries_def:
  (typed_copy_forward_entries cenv ctx [] stys dtvs stvs vs <=>
     stys = [] /\ dtvs = [] /\ stvs = [] /\ vs = []) /\
  (typed_copy_forward_entries cenv ctx (dty::dtys) stys dtvs stvs vs <=>
     case (stys,dtvs,stvs,vs) of
       (sty::stys,dtv::dtvs,stv::stvs,v::vs) =>
         type_memory_bytes cenv dty = type_memory_size dtv /\
         type_memory_bytes cenv sty = type_memory_size stv /\
         typed_copy_forward_entry cenv ctx dty sty dtv stv v /\
         typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs
     | _ => F)
End

Theorem typed_copy_forward_entries_nil[simp]:
  typed_copy_forward_entries cenv ctx [] stys dtvs stvs vs <=>
  stys = [] /\ dtvs = [] /\ stvs = [] /\ vs = []
Proof
  simp[typed_copy_forward_entries_def]
QED

Theorem typed_copy_forward_entries_cons[simp]:
  typed_copy_forward_entries cenv ctx (dty::dtys) (sty::stys)
    (dtv::dtvs) (stv::stvs) (v::vs) <=>
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  typed_copy_forward_entry cenv ctx dty sty dtv stv v /\
  typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs
Proof
  simp[typed_copy_forward_entries_def]
QED

Theorem typed_copy_forward_entries_lengths:
  !dtys stys dtvs stvs vs.
    typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs ==>
    LENGTH dtys = LENGTH vs /\ LENGTH stys = LENGTH vs /\
    LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs
Proof
  Induct >> simp[typed_copy_forward_entries_def] >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[typed_copy_forward_entries_def] >> metis_tac[]
QED

Theorem typed_copy_forward_fields_path:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw func.
    typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw + doff)
          (type_memory_size_list dtvs) s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[typed_copy_forward_entries_def, compile_store_memory_typed_def,
          comp_return_def, val_in_memory_def, type_memory_size_def] >>
      qexists_tac `s` >> simp[typed_copy_state_frame_refl,
        gas_marked_path_def, fragGasPathTheory.gas_path_rules]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[typed_copy_forward_entries_def] >>
  rename1 `typed_copy_forward_entry cenv ctx dty sty dtv stv v` >>
  rename1 `typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dst_ptr dty src_ptr sty cs'' = (u,sc)` >>
  Cases_on `u` >> suspend "cons"
QED

Resume typed_copy_forward_fields_path[cons]:
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst' src' doff' soff' sa' sb' s'' dw' sw' func'. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs''` by metis_tac[typed_copy_offset_mono] >>
     `ci_mono cs'' sc` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
     `ci_mono sc sb` by metis_tac[cj 2 ci_mono_typed_memory_family, pairTheory.SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends sa sc /\ cs_extends sc sb` by gvs[ci_mono_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
      typed_copy_forward_offset_path) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`sw`, `s`, `func`, `dw`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> decide_tac)) >>
  strip_tac >> suspend "suffix"
QED

Resume typed_copy_forward_fields_path[suffix]:
  `LENGTH vs = LENGTH stvs` by metis_tac[typed_copy_forward_entries_lengths] >>
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `typed_copy_forward_entry _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[typed_copy_state_frame_def]) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qpat_x_assum `!stys dtvs stvs vs dst' src' doff' soff' sa' sb' s'' dw' sw' func'. _` drule >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`, `func`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> decide_tac)) >>
  strip_tac >> suspend "finish"
QED

Resume typed_copy_forward_fields_path[finish]:
  `val_in_memory dtv v (doff + w2n dw) t'.vs_memory` by
    (irule typed_copy_frame_preserves_source >>
     conj_tac >- (gvs[arithmeticTheory.ADD_COMM]) >>
     qexistsl_tac [`type_memory_size_list dtvs`,
       `doff + (type_memory_size dtv + w2n dw)`, `t.vs_memory`] >>
     qpat_assum `typed_copy_state_frame sc _ _ t t'`
       (mp_tac o cj 3 o REWRITE_RULE [typed_copy_state_frame_def]) >>
     simp[GSYM ADD_ASSOC] >> strip_tac >>
     qpat_assum `val_in_memory dtv v _ t.vs_memory`
       (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM])) >>
  `typed_copy_state_frame sa (doff + w2n dw)
     (type_memory_size dtv + type_memory_size_list dtvs) s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >>
     conj_tac
     >- (irule typed_copy_state_frame_subinterval >>
         qexistsl_tac [`w2n dw + doff`, `type_memory_size dtv`] >> simp[]) >>
     irule typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[] >>
     irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`doff + type_memory_size dtv + w2n dw`,
       `type_memory_size_list dtvs`] >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[GSYM ADD_ASSOC] >>
  qpat_assum `tuple_in_memory vs dtvs _ t'.vs_memory`
    (ACCEPT_TAC o REWRITE_RULE [GSYM ADD_ASSOC])
QED

Finalise typed_copy_forward_fields_path

Theorem typed_copy_forward_counter_init_path:
  emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
  (!x. not_fresh_at a x ==> x <> counter) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      lookup_var counter t = SOME 0w /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all place_typed_copy_assign_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
  metis_tac[]
QED

Theorem typed_copy_forward_two_ops_path:
  emit_op opc1 args1 a = (op1,b) /\ emit_op opc2 args2 b = (op2,c) /\
  opc1 <> INVOKE /\ ~is_terminator opc1 /\ opc1 <> GAS /\
  opc2 <> INVOKE /\ ~is_terminator opc2 /\ opc2 <> GAS /\
  (!out. step_inst_base (mk_inst a.cs_next_id opc1 args1 [out]) s =
         OK (update_var out w1 s)) /\
  (!t out. eval_operand op1 t = SOME w1 /\
     t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t ==>
     step_inst_base (mk_inst b.cs_next_id opc2 args2 [out]) t =
     OK (update_var out w2 t)) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand op1 t = SOME w1 /\ eval_operand op2 t = SOME w2 /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends a b /\ cs_extends b c` by gvs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func` by metis_tac[fn_has_code_split] >>
  qpat_assum `emit_op opc1 _ _ = _`
    (mp_then Any mp_tac place_typed_copy_emit_op_path) >>
  disch_then (qspecl_then [`func`, `ctx`, `s`, `w1`, `off`, `len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `emit_op opc2 _ _ = _`
    (mp_then Any mp_tac place_typed_copy_emit_op_path) >>
  disch_then (qspecl_then [`func`, `ctx`, `t`, `w2`, `off`, `len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `eval_operand op1 t' = SOME w1` by
    metis_tac[typed_copy_state_frame_operand, typed_copy_emit_op_fresh] >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `b` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_forward_header_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword (:256) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand done t = SOME (if k < N then 0w else 1w) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand lt t = SOME (bool_to_word (k < N)) /\
       eval_operand done t = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
       t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
       ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
       t.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule typed_copy_forward_two_ops_path >> simp[] >>
     qexistsl_tac [`[Var counter; length]`, `[lt]`, `b`, `LT`, `ISZERO`] >>
     simp[venomInstTheory.is_terminator_def] >> conj_tac
     >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
             eval_operand_def, w2n_n2w, LESS_MOD] >>
     rpt strip_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_pure1_def]) >>
  qexists_tac `t` >> Cases_on `k < N` >> gvs[bool_to_word_def]
QED

Theorem typed_copy_forward_counter_increment_path:
  emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  k + 1 < dimword (:256) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w (k + 1)) /\
      t.vs_memory = s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at a x /\ x <> counter ==>
           lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_inst, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b c` by gvs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func` by metis_tac[fn_has_code_split] >>
  qpat_assum `emit_op _ _ _ = _`
    (mp_then Any mp_tac place_typed_copy_emit_op_path) >>
  disch_then (qspecl_then [`func`, `ctx`, `s`, `n2w (k+1)`, `0`, `0`] mp_tac) >>
  (impl_tac >- simp[is_terminator_def, step_inst_base_def, mk_inst_def,
                       exec_pure2_def, eval_operand_def, word_add_n2w]) >> strip_tac >>
  drule_all place_typed_copy_assign_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  qpat_x_assum `typed_copy_state_frame a _ _ s t` mp_tac >>
  simp[typed_copy_state_frame_def] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem typed_copy_forward_index_offsets_path:
  emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand so t = SOME (n2w (k * ss)) /\
      eval_operand doff t = SOME (n2w (k * ds)) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >> irule typed_copy_forward_two_ops_path >> simp[] >>
  qexistsl_tac [`[Var counter; Lit (n2w ss)]`, `[Var counter; Lit (n2w ds)]`,
               `b`, `MUL`, `MUL`] >>
  simp[is_terminator_def] >> conj_tac
  >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, word_mul_n2w] >>
  rpt strip_tac >>
  `lookup_var counter t = SOME (n2w k)` by gvs[typed_copy_state_frame_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, word_mul_n2w]
QED

Theorem typed_copy_forward_index_adds_path:
  emit_op ADD [src;so] a = (sp,b) /\
  emit_op ADD [dst;doff] b = (dp,c) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. doff = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand so s = SOME sv /\ eval_operand doff s = SOME dv /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand sp t = SOME (sw + sv) /\
      eval_operand dp t = SOME (dw + dv) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >> irule typed_copy_forward_two_ops_path >> simp[] >>
  qexistsl_tac [`[src;so]`, `[dst;doff]`, `b`, `ADD`, `ADD`] >>
  simp[is_terminator_def] >> conj_tac
  >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  rpt strip_tac >>
  `eval_operand dst t = SOME dw /\ eval_operand doff t = SOME dv` by
    metis_tac[typed_copy_state_frame_operand] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def]
QED

Theorem typed_copy_forward_index_addresses_path:
  emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code a e func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand sp t = SOME (sw + n2w (k * ss)) /\
      eval_operand dp t = SOME (dw + n2w (k * ds)) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
      t.vs_inst_idx = LENGTH e.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a c /\ ci_mono c e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a c /\ cs_extends c e` by gvs[ci_mono_def] >>
  `fn_has_code a c func /\ fn_has_code c e func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_forward_index_offsets_path >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `!x. dst = Var x ==> not_fresh_at c x` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `!x. doff = Var x ==> not_fresh_at c x` by
    metis_tac[typed_copy_emit_op_fresh] >>
  drule_all typed_copy_forward_index_adds_path >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `c` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_forward_index_child_path:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  typed_copy_forward_entry cenv ctx dty sty dtv stv v /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  lookup_var counter s = SOME (n2w k) /\ k < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw + k * type_memory_size stv) s.vs_memory /\
  w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  (w2n sw + k * type_memory_size stv + type_memory_size stv <=
     w2n dw + k * type_memory_size dtv \/
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + k * type_memory_size stv) /\
  fn_has_code a z func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
      typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = z.cs_current_bb /\
      t.vs_inst_idx = LENGTH z.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono e z` by metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a e /\ cs_extends e z` by gvs[ci_mono_def] >>
  `fn_has_code a e func /\ fn_has_code e z func` by metis_tac[fn_has_code_split] >>
  `w2n (sw + n2w (k * type_memory_size stv)) = w2n sw + k * type_memory_size stv /\
   w2n (dw + n2w (k * type_memory_size dtv)) = w2n dw + k * type_memory_size dtv` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. sp = Var x ==> not_fresh_at e x) /\
   (!x. dp = Var x ==> not_fresh_at e x)` by
    metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_forward_index_addresses_path >>
  disch_then (qspecl_then [`w2n dw + k * type_memory_size dtv`,
                          `type_memory_size dtv`, `ctx`] strip_assume_tac) >>
  suspend "child"
QED

Resume typed_copy_forward_index_child_path[child]:
  drule typed_copy_forward_entry_run >> disch_then drule >>
  disch_then (qspecl_then [`sw + n2w (k * type_memory_size stv)`, `t`, `func`,
                          `dw + n2w (k * type_memory_size dtv)`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `e` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Finalise typed_copy_forward_index_child_path

Theorem typed_copy_forward_index_body_path:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!i. i < N ==> typed_copy_forward_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\ k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  fn_has_code a endst func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t /\
      ~t.vs_halted /\ t.vs_current_bb = endst.cs_current_bb /\
      t.vs_inst_idx = LENGTH endst.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z /\
   ci_mono z z1 /\ ci_mono z1 endst` by
    metis_tac[typed_copy_emit_op_mono, cj 1 ci_mono_typed_memory_family,
              ci_mono_emit_inst, pairTheory.SND] >>
  `ci_mono a z /\ ci_mono sa z /\ ci_mono z endst` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a z /\ cs_extends z endst` by gvs[ci_mono_def] >>
  `fn_has_code a z func /\ fn_has_code z endst func` by metis_tac[fn_has_code_split] >>
  `not_fresh_at z counter /\
   (!x. src = Var x ==> not_fresh_at a x) /\
   (!x. dst = Var x ==> not_fresh_at a x)` by
    (conj_tac
     >- (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     conj_tac >> metis_tac[typed_copy_operand_fresh_mono]) >>
  suspend "copy"
QED

Resume typed_copy_forward_index_body_path[copy]:
  `w2n sw <= w2n sw + k * type_memory_size stv /\
   w2n sw + k * type_memory_size stv + type_memory_size stv <=
     w2n sw + N * type_memory_size stv` by metis_tac[typed_copy_array_subinterval] >>
  `w2n dw <= w2n dw + k * type_memory_size dtv /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n dw + N * type_memory_size dtv` by metis_tac[typed_copy_array_subinterval] >>
  `lookup_var counter s = SOME (n2w k) /\
   eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
   val_in_memory stv (f k) (w2n sw + k * type_memory_size stv) s.vs_memory` by
    gvs[typed_copy_index_inv_def] >>
  `k < dimword (:256) /\ k + 1 < dimword (:256)` by decide_tac >>
  `typed_copy_forward_entry cenv ctx dty sty dtv stv (f k)` by metis_tac[] >>
  `w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256)` by decide_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
       typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
         (type_memory_size dtv) s t /\
       ~t.vs_halted /\ t.vs_current_bb = z.cs_current_bb /\
       t.vs_inst_idx = LENGTH z.cs_current_insts` by
    (irule typed_copy_forward_index_child_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     qexists_tac `sw` >> simp[] >> decide_tac) >>
  suspend "increment"
QED

Resume typed_copy_forward_index_body_path[increment]:
  `lookup_var counter t = SOME (n2w k)` by
    metis_tac[typed_copy_state_frame_counter] >>
  drule_all typed_copy_forward_counter_increment_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) t t'` by
    (simp[typed_copy_state_frame_def] >> rpt strip_tac >>
     first_x_assum irule >> gvs[ci_mono_def, not_fresh_at_def] >> decide_tac) >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) s t` by
    (irule typed_copy_state_frame_mono >> qexists_tac `a` >> simp[]) >>
  `eval_operand src t' = SOME sw /\ eval_operand dst t' = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t'` by
    (irule typed_copy_index_inv_step >> simp[ADD1] >>
     qexists_tac `s` >> simp[] >>
     irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Finalise typed_copy_forward_index_body_path

Theorem typed_copy_forward_jump_path:
  emit_inst JMP [Label target] [] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_marked_path F ctx func s 0 (OK (jump_to target s))
Proof
  strip_tac >> drule_all place_copy_emit_instruction >> strip_tac >>
  irule place_copy_jump_path >> simp[] >>
  qexists_tac `a.cs_next_id` >> simp[]
QED

Theorem typed_copy_forward_branch_path:
  emit_inst JNZ [test; Label yes; Label no] [] a = ((),b) /\
  fn_has_code a b func /\ eval_operand test s = SOME w /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (if w = 0w then no else yes) s))
Proof
  strip_tac >> drule_all place_copy_emit_instruction >> strip_tac >>
  irule place_copy_branch_path >> simp[] >>
  qexistsl_tac [`a.cs_next_id`, `test`] >> simp[]
QED

Theorem typed_copy_forward_index_header_branch_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] c = ((),d) /\
  ci_mono sa a /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
      ~t.vs_halted /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if k = N then exit else blabel)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_inst, pairTheory.SND] >>
  `cs_extends a c /\ cs_extends c d` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a c func /\ fn_has_code c d func` by
    metis_tac[fn_has_code_split] >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[typed_copy_index_inv_def] >>
  drule_all typed_copy_forward_header_path >>
  disch_then (qspecl_then [`w2n dw`, `N * type_memory_size dtv`, `ctx`]
    strip_assume_tac) >>
  `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t` by
    (irule typed_copy_index_inv_preserve >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all typed_copy_forward_branch_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `jump_to (if (if k < N then 0w else 1w) = 0w then blabel else exit) t` >>
  simp[typed_copy_index_inv_jump, jump_to_def] >>
  Cases_on `k < N` >> gvs[jump_to_def]
QED

Theorem typed_copy_forward_index_loop_path:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  ci_mono sa init /\ ci_mono sa st0 /\ ci_mono sa sth /\ ci_mono sa stb /\
  ci_mono init st0 /\ ci_mono st0 stx /\
  cs_extends sth stj /\ cs_extends stb ste /\
  ~not_fresh_at sa counter /\ not_fresh_at sth counter /\
  not_fresh_at stb counter /\
  sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_forward_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa stx func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = stx.cs_current_bb /\
      t.vs_inst_idx = LENGTH stx.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  suspend "slices"
QED

Resume typed_copy_forward_index_loop_path[slices]:
  `cs_extends st0 st1 /\ cs_extends stj st2 /\ cs_extends ste st3` by
    metis_tac[ci_mono_emit_inst, ci_mono_def, pairTheory.SND] >>
  `cs_extends st1 sth /\ cs_extends st2 stb /\ cs_extends st3 stx` by
    metis_tac[ci_mono_new_block, ci_mono_def, pairTheory.SND] >>
  `cs_extends stb stx` by metis_tac[cs_extends_trans] >>
  `cs_extends stj stx` by metis_tac[cs_extends_trans] >>
  `cs_extends sa init /\ cs_extends sa st0 /\ cs_extends sa sth /\
   cs_extends sa stb` by gvs[ci_mono_def] >>
  `fn_has_code init st0 func /\ fn_has_code st0 st1 func /\
   fn_has_code sth st2 func /\ fn_has_code stb ste func /\
   fn_has_code ste st3 func` by
    (rpt conj_tac >> irule fn_has_code_mid >>
     (conj_tac >- metis_tac[ci_mono_def, cs_extends_trans]) >>
     qexistsl_tac [`stx`, `sa`] >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  `sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
   stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
   stx.cs_current_bb = exit /\ stx.cs_current_insts = []` by
    gvs[new_block_def] >>
  suspend "init"
QED

Resume typed_copy_forward_index_loop_path[init]:
  `s.vs_current_bb = init.cs_current_bb /\
   s.vs_inst_idx = LENGTH init.cs_current_insts` by simp[] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all place_typed_copy_assign_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
    (simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
     metis_tac[]) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t` by
    simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero] >>
  drule_all typed_copy_forward_jump_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  suspend "iterate"
QED

Resume typed_copy_forward_index_loop_path[iterate]:
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `emit_inst ASSIGN [Lit 0w] _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JMP _ _ st0 = _` kall_tac >>
  qabbrev_tac `Inv = typed_copy_index_inv sa counter src dst sw dw f stv dtv N s` >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `!j q. j <= N /\ Inv j q /\ ~q.vs_halted /\
     q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\ Inv j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = N then exit else blabel)` by
    (rpt strip_tac >>
     `eval_operand length q = SOME (n2w N)` by
       (fs[Abbr `Inv`, typed_copy_index_inv_def] >>
        metis_tac[typed_copy_state_frame_operand]) >>
     simp[Abbr `Inv`] >>
     irule typed_copy_forward_index_header_branch_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
     simp[eval_operand_def]) >>
  suspend "body"

QED

Resume typed_copy_forward_index_loop_path[body]:
  `!j q. j < N /\ Inv j q /\ ~q.vs_halted /\
     q.vs_current_bb = blabel /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\ Inv (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (rpt strip_tac >>
     `q.vs_current_bb = stb.cs_current_bb /\
      q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
     `typed_copy_index_inv sa counter src dst sw dw f stv dtv N s j q` by
       gvs[Abbr `Inv`] >>
     drule_all typed_copy_forward_index_body_path >> strip_tac >>
     drule_all typed_copy_forward_jump_path >>
     disch_then (qspec_then `ctx` assume_tac) >>
     qpat_assum `gas_marked_path F ctx func q 0 (OK _)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then drule >> simp[] >> strip_tac >>
     goal_assum (drule_at Any) >>
     simp[Abbr `Inv`, typed_copy_index_inv_jump, GSYM ADD1] >>
     gvs[jump_to_def]) >>
  suspend "finish"
QED

Resume typed_copy_forward_index_loop_path[finish]:
  `Inv 0 (jump_to hdr t)` by
    simp[Abbr `Inv`, typed_copy_index_inv_jump] >>
  `?u. gas_marked_path F ctx func (jump_to hdr t) 0 (OK u) /\
       Inv N u /\ ~u.vs_halted /\ u.vs_current_bb = exit /\ u.vs_inst_idx = 0` by
    (irule place_copy_iterate_path >>
     (conj_tac >- simp[jump_to_def]) >>
     (conj_tac >- (qexistsl_tac [`hdr`, `blabel`] >> simp[jump_to_def])) >>
     (conj_tac >- simp[jump_to_def]) >>
     qexistsl_tac [`0`, `N`] >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  qpat_x_assum `Inv N u` mp_tac >>
  simp[Abbr `Inv`, typed_copy_index_inv_def, typed_copy_index_prefix_complete]
QED

Finalise typed_copy_forward_index_loop_path


Theorem typed_copy_forward_sarray_slow_path:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_forward_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  drule_all typed_copy_sarray_slow_layout >> strip_tac >>
  irule typed_copy_forward_index_loop_path >> simp[eval_operand_def] >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[eval_operand_def]
QED

Theorem typed_copy_forward_dynarray_slow_data_path:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_forward_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa stx func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = stx.cs_current_bb /\
      t.vs_inst_idx = LENGTH stx.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_dynarray_slow_layout >> strip_tac >>
  irule typed_copy_forward_index_loop_path >> simp[] >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem typed_copy_forward_sarray_path:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  (!i. i < N ==> typed_copy_forward_entry cenv ctx dty sty dtv stv
     (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  N < dimword (:256) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n sw) s.vs_memory /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- (`stv = dtv` by metis_tac[typed_copy_static_widening] >>
      qpat_x_assum `stv = dtv` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def] >> strip_tac >>
      `N * type_memory_size stv < dimword (:256)` by decide_tac >>
      `val_footprint (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) <=
       N * type_memory_size stv` by
        simp[loweringPostsTheory.val_footprint_def, type_memory_size_def] >>
      `N * type_memory_size stv <= type_memory_size (ArrayTV stv (Fixed N))` by
        simp[type_memory_size_def] >>
      drule_all place_typed_copy_fixed_path >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[type_memory_size_def]) >>
  drule_all typed_copy_sarray_representation >> strip_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       (!i. i < N ==> val_in_memory dtv
          (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
          (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
       typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (ho_match_mp_tac typed_copy_forward_sarray_slow_path >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem typed_copy_forward_void_path:
  emit_void opc args a = ((),b) /\
  opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS /\
  step_inst_base (mk_inst a.cs_next_id opc args []) s = OK r /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK (r with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  `run_inst_seq (emitted_insts a b) s = OK r` by
    (asm_rewrite_tac[run_inst_seq_def] >> simp[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts a b) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts a b)` by simp[mk_inst_def] >>
  `b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, emitted_insts_def, DROP_APPEND1] >>
  drule_all place_copy_seq_path >> simp[]
QED

Theorem typed_copy_forward_assert_path:
  emit_void ASSERT [ok] a = ((),b) /\ eval_operand ok s = SOME 1w /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> qexists_tac `s with vs_inst_idx := LENGTH b.cs_current_insts` >>
  conj_tac
  >- (irule typed_copy_forward_void_path >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
      simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs]) >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  gvs[typed_copy_state_frame_def, lookup_var_def, same_blocks_def,
      venom_state_component_equality]
QED

Theorem typed_copy_forward_mstore_path:
  emit_void MSTORE [dst; value] a = ((),b) /\
  eval_operand dst s = SOME dw /\ eval_operand value s = SOME w /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  qexists_tac `(mstore (w2n dw) w s) with vs_inst_idx := LENGTH b.cs_current_insts` >>
  conj_tac
  >- (irule typed_copy_forward_void_path >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
      simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs, exec_write2_def]) >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  simp[mstore_mem_word_at_same, typed_copy_mstore_state_frame] >>
  gvs[mstore_def, write_memory_with_expansion_def, same_blocks_def]
QED

Theorem typed_copy_forward_dyn_check_path:
  emit_op GT [length; Lit (n2w C)] a = (too_long,b) /\
  emit_op ISZERO [too_long] b = (ok,c) /\
  emit_void ASSERT [ok] c = ((),d) /\
  eval_operand length s = SOME (n2w N) /\ N <= C /\ C < dimword (:256) /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
      t.vs_inst_idx = LENGTH d.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a c /\ cs_extends c d` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a c func /\ fn_has_code c d func` by metis_tac[fn_has_code_split] >>
  `N < dimword (:256)` by decide_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand too_long t = SOME 0w /\ eval_operand ok t = SOME 1w /\
       t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
       ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
       t.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule typed_copy_forward_two_ops_path >> simp[] >>
     qexistsl_tac [`[length; Lit (n2w C)]`, `[too_long]`, `b`, `GT`, `ISZERO`] >>
     simp[is_terminator_def] >> conj_tac
     >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
             eval_operand_def, w2n_n2w, LESS_MOD, bool_to_word_def, NOT_LESS] >>
     rpt strip_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def, bool_to_word_def]) >>
  drule_all typed_copy_forward_assert_path >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `c` >>
     fs[ci_mono_def] >> decide_tac) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_forward_dyn_read_check_path:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  N <= C /\ C < dimword (:256) /\
  (!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w N) s)) /\
  fn_has_code a e func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
      t.vs_inst_idx = LENGTH e.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a b func /\ fn_has_code b e func` by metis_tac[fn_has_code_split] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
       typed_copy_state_frame a off len s t /\
       ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
       t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_typed_copy_emit_op_path >> simp[] >>
     qexistsl_tac [`[src]`, `MLOAD`] >> simp[is_terminator_def]) >>
  drule_all typed_copy_forward_dyn_check_path >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `eval_operand length t' = SOME (n2w N)` by
    metis_tac[typed_copy_state_frame_operand, typed_copy_emit_op_fresh] >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `b` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_forward_dyn_data_path:
  emit_void MSTORE [dst; length] a = ((),b) /\
  emit_op ADD [src; Lit 32w] b = (sd,c) /\
  emit_op ADD [dst; Lit 32w] c = (dd,d) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME w /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand length t = SOME w /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
      t.vs_inst_idx = LENGTH d.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b d` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a b func /\ fn_has_code b d func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_forward_mstore_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  suspend "adds"
QED

Resume typed_copy_forward_dyn_data_path[adds]:
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
       eval_operand sd u = SOME (sw + 32w) /\ eval_operand dd u = SOME (dw + 32w) /\
       u.vs_memory = t.vs_memory /\ typed_copy_state_frame b (w2n dw) 32 t u /\
       ~u.vs_halted /\ u.vs_current_bb = d.cs_current_bb /\
       u.vs_inst_idx = LENGTH d.cs_current_insts` by
    (irule typed_copy_forward_two_ops_path >> simp[] >>
     qexistsl_tac [`[src; Lit 32w]`, `[dst; Lit 32w]`, `c`, `ADD`, `ADD`] >>
     simp[is_terminator_def] >> conj_tac
     >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
     rpt strip_tac >>
     `eval_operand dst t' = SOME dw` by
       metis_tac[typed_copy_state_frame_operand, typed_copy_operand_fresh_mono] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `typed_copy_state_frame a (w2n dw) 32 s u` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `b` >> simp[]) >>
  `eval_operand length u = SOME w` by metis_tac[typed_copy_state_frame_operand] >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `u` >> simp[]
QED

Finalise typed_copy_forward_dyn_data_path

Theorem typed_copy_forward_dyn_prefix_path:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  N <= C /\ C < dimword (:256) /\
  (!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w N) s)) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w N) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_word_at (w2n dw) t.vs_memory = n2w N /\
      typed_copy_state_frame a (w2n dw) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `cs_extends a a4 /\ cs_extends a4 b` by gvs[ci_mono_def] >>
  `fn_has_code a a4 func /\ fn_has_code a4 b func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_forward_dyn_read_check_path >>
  disch_then (qspecl_then [`w2n dw`, `32`, `ctx`] strip_assume_tac) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. src = Var x ==> not_fresh_at a4 x) /\
   (!x. dst = Var x ==> not_fresh_at a4 x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_forward_dyn_data_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_state_frame a (w2n dw) 32 s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `a4` >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_forward_dynarray_path:
  compile_copy_dynarray_typed cenv dst dty C src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (dty = sty ==> dtv = stv) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (!i. i < LENGTH vs ==> typed_copy_forward_entry cenv ctx dty sty dtv stv (EL i vs)) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic C))) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dd,b)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (sd,a6)` >> disch_tac >>
  drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `ci_mono b sb` by
    (qmatch_asmsub_abbrev_tac `suffix b = ((),sb)` >>
     `ci_mono b (SND (suffix b))` suffices_by gvs[] >>
     unabbrev_all_tac >> IF_CASES_TAC >>
     rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
          rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_emit_op, ci_mono_emit_inst, ci_mono_new_block,
          ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_comp_return,
          cj 1 ci_mono_typed_memory_family,
          contextTheory.compile_copy_memory_dynamic_def, ci_mono_emit_void]) >>
  `cs_extends sa b /\ cs_extends b sb` by gvs[ci_mono_def] >>
  `fn_has_code sa b func /\ fn_has_code b sb func` by metis_tac[fn_has_code_split] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w (LENGTH vs)) s)` by
    metis_tac[typed_copy_dynarray_mload_step] >>
  drule_all typed_copy_forward_dyn_prefix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "suffix"
QED

Resume typed_copy_forward_dynarray_path[suffix]:
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) t.vs_memory` by
    (irule typed_copy_frame_preserves_source >> conj_tac >- simp[] >>
     qexistsl_tac [`32`, `w2n dw`, `s.vs_memory`] >> simp[] >> conj_tac
     >- (fs[type_memory_size_def] >> decide_tac) >>
     gvs[typed_copy_state_frame_def]) >>
  `LENGTH vs <= scap` by gvs[typed_copy_dynarray_wf] >>
  `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv /\
   LENGTH vs * type_memory_size dtv <= C * type_memory_size dtv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  `w2n (sw + 32w) + LENGTH vs * type_memory_size stv < dimword (:256) /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv < dimword (:256) /\
   (w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= w2n (dw + 32w) \/
    w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= w2n (sw + 32w))` by
    (gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
       (!i. i < LENGTH vs ==> val_in_memory dtv (EL i vs)
          (w2n (dw + 32w) + i * type_memory_size dtv) u.vs_memory) /\
       typed_copy_state_frame b (w2n (dw + 32w))
          (LENGTH vs * type_memory_size dtv) t u /\
       ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts` by suspend "data" >>
  suspend "reconstruct"
QED

Resume typed_copy_forward_dynarray_path[data]:
  markerLib.RESUME_TAC >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  qpat_x_assum `val_in_memory _ _ _ s.vs_memory` kall_tac >>
  qpat_x_assum `typed_copy_state_frame sa _ _ s t` kall_tac >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  `!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
     (w2n (sw + 32w) + i * type_memory_size stv) t.vs_memory` by
    gvs[typed_copy_dynarray_representation] >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\ dty = sty` >>
  IF (qpat_assum `type_memory_size dtv = type_memory_size stv /\ dty = sty` kall_tac)
    (suspend "bulk") (suspend "slow")
QED

Resume typed_copy_forward_dynarray_path[slow]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  `!i. i < LENGTH vs ==> typed_copy_forward_entry cenv ctx dty sty dtv stv (EL i vs) /\
        val_wf stv (EL i vs) /\ val_wf dtv (EL i vs)` by
    gvs[typed_copy_dynarray_wf] >>
  irule (BETA_RULE (Q.INST [`f` |-> `\i. EL i vs`]
    typed_copy_forward_dynarray_slow_data_path)) >>
  qpat_assum `fresh_label "typed_dyn_cond" _ = _`
    (irule_at (Pat `fresh_label "typed_dyn_cond" _ = _`)) >>
  qpat_assum `fresh_label "typed_dyn_body" _ = _`
    (irule_at (Pat `fresh_label "typed_dyn_body" _ = _`)) >>
  qpat_assum `fresh_label "typed_dyn_exit" _ = _`
    (irule_at (Pat `fresh_label "typed_dyn_exit" _ = _`)) >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> decide_tac
QED

Resume typed_copy_forward_dynarray_path[bulk]:
  markerLib.RESUME_TAC >>
  `dtv = stv` by simp[] >>
  qpat_x_assum `dtv = stv` SUBST_ALL_TAC >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  rename1 `emit_op MUL _ b = (bytes,c)` >>
  `ci_mono b c /\ ci_mono c sb` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_compile_copy_memory_dynamic, pairTheory.SND] >>
  `cs_extends b c /\ cs_extends c sb` by gvs[ci_mono_def] >>
  `fn_has_code b c func /\ fn_has_code c sb func` by metis_tac[fn_has_code_split] >>
  `?r. gas_marked_path F ctx func t 0 (OK r) /\
       eval_operand bytes r = SOME (n2w (LENGTH vs * type_memory_size stv)) /\
       r.vs_memory = t.vs_memory /\
       typed_copy_state_frame b (w2n (dw + 32w)) (LENGTH vs * type_memory_size stv) t r /\
       ~r.vs_halted /\ r.vs_current_bb = c.cs_current_bb /\
       r.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule place_typed_copy_emit_op_path >> simp[] >>
     qexistsl_tac [`[length; Lit (n2w (type_memory_size stv))]`, `MUL`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, GSYM word_mul_n2w]) >>
  `eval_operand sd r = SOME (sw + 32w) /\ eval_operand dd r = SOME (dw + 32w)` by
    metis_tac[typed_copy_state_frame_operand] >>
  suspend "mcopy"
QED

Resume typed_copy_forward_dynarray_path[reconstruct]:
  markerLib.RESUME_TAC >> (
  `typed_copy_state_frame b (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t u` by metis_tac[] >>
  qexists_tac `u` >> conj_tac
  >- (qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then drule >> simp[]) >>
  conj_tac
  >- (irule typed_copy_dynarray_reconstruct >> conj_tac
      >- (qpat_assum `!i. _ ==> val_in_memory dtv _ _ u.vs_memory` mp_tac >>
          simp_tac std_ss [AC ADD_ASSOC ADD_COMM] >> simp[]) >>
      qpat_assum `typed_copy_state_frame b (w2n dw + 32) _ t u`
        (irule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >> simp[]) >>
  simp[] >>
  `typed_copy_state_frame sa (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t u` by
    (irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ s t`)) >>
      simp[type_memory_size_def]) >>
  irule typed_copy_state_frame_subinterval >>
  goal_assum (drule_at (Pat `typed_copy_state_frame sa _ _ t _`)) >>
  simp[type_memory_size_def, Excl "LE_MULT_RCANCEL"])
QED

Resume typed_copy_forward_dynarray_path[mcopy]:
  markerLib.RESUME_TAC >> (
  `LENGTH vs * type_memory_size stv < dimword (:256)` by decide_tac >>
  `eval_operand bytes r = SOME (n2w (LENGTH vs * type_memory_size stv))` by simp[] >>
  `emit_void MCOPY [dd; sd; bytes] c = ((),sb)` by
    gvs[compile_copy_memory_dynamic_def] >>
  `same_blocks c sb` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  `gas_marked_path F ctx func r 0
     (OK ((mcopy (w2n (dw + 32w)) (w2n (sw + 32w))
          (LENGTH vs * type_memory_size stv) r)
       with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule typed_copy_forward_void_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
     simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs,
          step_inst_base_def, w2n_n2w, LESS_MOD]) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func r 0 (OK u)` >>
  `typed_copy_state_frame c (w2n (dw + 32w))
      (LENGTH vs * type_memory_size stv) r u` by
    (simp[Abbr `u`, typed_copy_state_frame_def, lookup_var_def,
          typed_copy_mcopy_state_frame, mcopy_def, write_memory_with_expansion_def]) >>
  `typed_copy_state_frame b (w2n (dw + 32w))
      (LENGTH vs * type_memory_size stv) t u` by
    (gvs[] >> irule typed_copy_state_frame_trans >> qexists_tac `r` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `c` >> simp[]) >>
  qexists_tac `u` >> conj_tac
  >- (qpat_assum `gas_marked_path F ctx func t 0 (OK r)`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then drule >> simp[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >>
      conj_tac >- gvs[typed_copy_dynarray_wf] >>
      qexistsl_tac [`w2n (sw + 32w) + i * type_memory_size stv`,
                    `type_memory_size stv`, `r.vs_memory`] >>
      simp[] >> conj_tac
      >- gvs[typed_copy_dynarray_wf, exprSimPropsTheory.val_footprint_le] >>
      `mem_bytes_at (w2n (dw + 32w)) (LENGTH vs * type_memory_size stv) u.vs_memory =
       mem_bytes_at (w2n (sw + 32w)) (LENGTH vs * type_memory_size stv) r.vs_memory` by
        simp[Abbr `u`, mcopy_mem_bytes_at_same] >>
      drule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
      disch_then (qspecl_then [`i * type_memory_size stv`, `type_memory_size stv`] mp_tac) >>
      (impl_tac >-
        (`SUC i <= LENGTH vs` by decide_tac >>
         `SUC i * type_memory_size stv <= LENGTH vs * type_memory_size stv` by
           simp[arithmeticTheory.LE_MULT_RCANCEL] >>
         qpat_x_assum `SUC i * _ <= _` mp_tac >>
         pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac)) >>
      simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  gvs[Abbr `u`, mcopy_def, write_memory_with_expansion_def, same_blocks_def])
QED

Finalise typed_copy_forward_dynarray_path

Theorem typed_copy_forward_entries_from_semantics:
  !dtys stys dtvs stvs vs.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) stys dtys /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    (!cd cs cdt cst cv. MEM cd dtys ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_forward_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs
Proof
  Induct >> Cases_on `stys` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[typed_copy_forward_entries_def, OPT_MMAP_def, AllCaseEqs(),
       vyperTypingTheory.value_has_type_def, val_in_memory_def, val_wf_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[typed_copy_memory_size]
QED

Theorem typed_copy_forward_tuple_path:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  typed_copy_forward_entries cenv ctx dtys stys dtvs stvs vs /\
  tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
  compile_store_memory_typed cenv dst (TupleT dtys) src (TupleT stys) sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory (TupleTV stvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (TupleTV stvs) < dimword (:256) /\
  w2n dw + type_memory_size (TupleTV dtvs) < dimword (:256) /\
  (w2n sw + type_memory_size (TupleTV stvs) <= w2n dw \/
   w2n dw + type_memory_size (TupleTV dtvs) <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory (TupleTV dtvs) (ArrayV (TupleV vs)) (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size (TupleTV dtvs)) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_forward_fields_path >> disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`, `func`] mp_tac) >>
  gvs[val_in_memory_def, type_memory_size_def]
QED

Theorem typed_copy_forward_struct_path:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string name) /\
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,ty,sz). sz = type_memory_bytes cenv ty) fields /\
  typed_copy_forward_entries cenv ctx
    (MAP (FST o SND) fields) (MAP (FST o SND) fields) tvs tvs vs /\
  tuple_val_wf vs tvs /\
  compile_store_memory_typed cenv dst (StructT name) src (StructT name) sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  tuple_in_memory vs tvs (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size_list tvs < dimword (:256) /\
  w2n dw + type_memory_size_list tvs < dimword (:256) /\
  (w2n sw + type_memory_size_list tvs <= w2n dw \/
   w2n dw + type_memory_size_list tvs <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      tuple_in_memory vs tvs (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size_list tvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  `compile_struct_typed_copy cenv dst src fields fields 0 0 =
   compile_typed_copy_fields cenv dst src
     (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0` by
    (qpat_assum `MAP _ fields = MAP (FST o SND) fields`
       (fn th => rewrite_tac[GSYM th]) >>
     irule typed_copy_struct_fields_producer >> simp[EVERY_MEM]) >>
  gvs[] >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_forward_fields_path >> disch_then drule >>
  disch_then (qspecl_then [`s`, `dw`, `sw`, `func`] mp_tac) >> simp[]
QED

Theorem typed_copy_forward_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_forward_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_forward_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (`!ss ds. (ss = ds \/ arg_types_fit ss ds) /\
         (?tvs. OPT_MMAP (evaluate_type tenv) ds = SOME tvs) ==>
         LIST_REL (type_widens_to tenv) ss ds` suffices_by
       (strip_tac >> drule typed_copy_tuple_widening >>
        gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
        metis_tac[]) >>
     Induct >> Cases_on `ds` >>
     simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `typed_copy_forward_entries cenv ctx dtys stys tvs' tvs l` by
    (irule typed_copy_forward_entries_from_semantics >>
     (conj_tac >- gvs[val_wf_def]) >>
     (conj_tac >- gvs[val_wf_def]) >>
     (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
     qexists_tac `tenv` >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[typedCopyDomainTheory.member_rank_lt_tuple]) >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  irule typed_copy_forward_tuple_path >> simp[] >>
  (conj_tac >- gvs[val_wf_def]) >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexists_tac `tvs` >> gvs[val_wf_def] >> decide_tac
QED

Theorem typed_copy_forward_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_forward_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_forward_entry cenv ctx (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH l ==> typed_copy_forward_entry cenv ctx de se tv' tv (EL i l)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once typedCopyDomainTheory.type_rank_def] >>
     gvs[typed_copy_dynarray_wf, all_have_type_EVERY, EVERY_EL]) >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_forward_dynarray_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`scap`, `tv`, `sw`] >>
  gvs[typed_copy_dynarray_wf] >> strip_tac >> gvs[]
QED

Theorem typed_copy_forward_sarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_forward_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_forward_entry cenv ctx (ArrayT de (Fixed cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by
    metis_tac[typed_copy_default_widening] >>
  `!i. i < cap ==> typed_copy_forward_entry cenv ctx de se tv' tv
      (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once typedCopyDomainTheory.type_rank_def] >>
     `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (irule typed_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule typed_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[default_value_well_typed,
                 cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  gvs[type_memory_size_def] >> irule typed_copy_forward_sarray_path >> simp[] >>
  (conj_tac >- gvs[value_has_type_def]) >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tv`, `sw`, `tenv`] >> gvs[type_memory_size_def, value_has_type_def]
QED

Theorem typed_copy_forward_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_forward_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_forward_entry cenv ctx (StructT name) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    suspend "values" >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by suspend "widen" >>
  `typed_copy_forward_entries cenv ctx (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) tvs tvs vs` by
    (irule typed_copy_forward_entries_from_semantics >> simp[] >>
     qexists_tac `tenv` >> gvs[evaluate_types_OPT_MMAP] >>
     (conj_tac >- metis_tac[]) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     `MEM cd (MAP (FST o SND) fields)` by metis_tac[] >>
     qpat_x_assum `MEM cd (MAP SND args)` kall_tac >>
     fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,cd,y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[compileEnvTheory.get_struct_fields_def] >>
     drule_all typedCopyDomainTheory.member_rank_lt_struct >>
     simp[typedCopyDomainTheory.type_rank_def, nsid_to_string_def]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    suspend "bytes" >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  suspend "run"
QED

Resume typed_copy_forward_struct_entry[values]:
  qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
  qpat_x_assum `struct_has_type _ l` mp_tac >>
  qpat_x_assum `fields_val_wf l _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  qid_spec_tac `l` >> qid_spec_tac `tvs` >>
  Induct_on `args` >> Cases_on `tvs` >> Cases_on `l` >>
  simp[value_has_type_def, val_wf_def] >>
  PairCases_on `h'` >> simp[value_has_type_def, val_wf_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule_all >> strip_tac >>
  qexists_tac `h'1::vs` >> simp[value_has_type_def, val_wf_def]
QED

Resume typed_copy_forward_struct_entry[widen]:
  `!ss ds. (ss = ds \/ arg_types_fit ss ds) /\
       (?tvs. OPT_MMAP (evaluate_type tenv) ds = SOME tvs) ==>
       LIST_REL (type_widens_to tenv) ss ds` suffices_by
    (strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  Induct >> Cases_on `ds` >>
  simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]
QED

Resume typed_copy_forward_struct_entry[bytes]:
  (conj_tac >- metis_tac[]) >>
  `!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  qpat_x_assum `OPT_MMAP _ (MAP (FST o SND) fields) = SOME tvs` mp_tac >>
  qpat_x_assum `EVERY _ fields` mp_tac >>
  qpat_x_assum `!ty tv. evaluate_type tenv ty = SOME tv ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  qid_spec_tac `tvs` >> Induct_on `fields` >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[OPT_MMAP_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[]
QED

Resume typed_copy_forward_struct_entry[run]:
  markerLib.RESUME_TAC >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `tvs` >>
     Induct_on `args` >> Cases_on `tvs` >> simp[type_memory_size_def]) >>
  gvs[type_memory_size_def, val_in_memory_def, typed_copy_fields_tuple_zip] >>
  irule typed_copy_forward_struct_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexists_tac `sw` >> simp[compileEnvTheory.get_struct_fields_def]
QED

Finalise typed_copy_forward_struct_entry

Theorem typed_copy_forward_rank_entry:
  !n cenv tenv ctx dty sty dtv stv v.
    type_rank cenv.ce_struct_fields dty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v ==>
    typed_copy_forward_entry cenv ctx dty sty dtv stv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- suspend "word" >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytestring" >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (irule typed_copy_forward_sarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >> rpt strip_tac >>
          qpat_x_assum `!k. k < _ ==> _`
            (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
          simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
      irule typed_copy_forward_dynarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >~ [`TupleT dtys`]
  >- (irule typed_copy_forward_tuple_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >~ [`StructT name`]
  >- (irule typed_copy_forward_struct_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  qexists_tac `s` >> simp[val_in_memory_def, type_memory_size_def,
    typed_copy_state_frame_refl, gas_marked_path_def, fragGasPathTheory.gas_path_rules]
QED

Resume typed_copy_forward_rank_entry[word]:
  drule_all typed_copy_word_widening >> strip_tac >> gvs[] >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  `type_memory_size dtv = 32` by
    (qpat_x_assum `is_word_type dty` mp_tac >>
     qpat_x_assum `evaluate_type tenv dty = SOME dtv` mp_tac >>
     Cases_on `dty` >> simp[is_word_type_def]
     >~ [`FlagT`]
     >- (rw[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
         gvs[type_memory_size_def]) >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_word_type_def, evaluate_type_def, type_memory_size_def] >>
     rpt strip_tac >> gvs[type_memory_size_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_word_type_def, evaluate_type_def, type_memory_size_def,
         AllCaseEqs()]) >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[exprSimPropsTheory.val_in_memory_word] >>
  irule place_typed_copy_word_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`sw`, `tenv`] >> simp[]
QED

Resume typed_copy_forward_rank_entry[bytestring]:
  drule_all typed_copy_bytestring_source >> strip_tac >>
  simp[typed_copy_forward_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  `!ty tv. is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
     (?cap. tv = BaseTV (BytesT (Dynamic cap))) \/
     (?cap. tv = BaseTV (StringT cap))` by
    (Cases >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >> rw[is_bytestring_type_def, evaluate_type_def]) >>
     rw[evaluate_type_def]) >>
  `(?cap. stv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. stv = BaseTV (StringT cap))` by metis_tac[] >>
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by metis_tac[] >>
  `val_footprint dtv v <= type_memory_size dtv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
  irule place_typed_copy_bytestring_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
  FIRST [rename1 `StringV str` >> qexistsl_tac [`STRLEN str`, `sw`],
         rename1 `BytesV bs` >> qexistsl_tac [`LENGTH bs`, `sw`]] >>
  gvs[val_in_memory_def, loweringPostsTheory.val_footprint_def,
      type_memory_size_def] >>
  qmatch_goalsub_abbrev_tac `word_size len <= word_size capacity` >>
  `word_size len <= word_size capacity` by
    (irule exprSimHypsTheory.word_size_monotone >> simp[Abbr `len`]) >>
  qspec_then `len` assume_tac exprSimPropsTheory.le_word_size_mul >> decide_tac
QED

Finalise typed_copy_forward_rank_entry

Theorem compile_store_memory_typed_forward_run:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `typed_copy_forward_entry cenv ctx dty sty dtv stv v` by
    (irule typed_copy_forward_rank_entry >> simp[] >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  irule typed_copy_forward_entry_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw`] >> simp[]
QED
