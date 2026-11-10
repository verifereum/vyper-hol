Theory placeMemoryArrayForward
Ancestors
  placeMemoryArrayControl placeMemoryChildForward placeMemoryTypedBase
  placeMemoryCodeLayout placeMemoryCopyEffect placeMemoryCopyFrames
  placeMemoryDynarrayForward
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  venomState venomInst venomExecSemantics freshWrites ASCIInumbers list arithmetic

Theorem typed_memory_array_addresses_fresh:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. sp = Var x ==> not_fresh_at sb x) /\
  (!x. dp = Var x ==> not_fresh_at sb x)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[not_fresh_at_def, toString_inj] >> rpt strip_tac >> decide_tac
QED

(* One semantic element step, shared by fixed and dynamic array loops. The
   small write region is retained here so the loop can frame its source and
   already completed destination elements before enlarging the effect. *)
Theorem typed_memory_array_element_forward:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  typed_memory_child_forward cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv + 64 < dimword (:256) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)
Proof
  strip_tac >>
  drule_all typed_memory_array_addresses_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule typed_memory_array_addresses_fresh >> strip_tac >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `w2n (sw + n2w (i * type_memory_size stv)) = w2n sw + i * type_memory_size stv /\
   w2n (dw + n2w (i * type_memory_size dtv)) = w2n dw + i * type_memory_size dtv` by
    (`w2n sw + i * type_memory_size stv < dimword (:256) /\
      w2n dw + i * type_memory_size dtv < dimword (:256) /\
      i * type_memory_size stv < dimword (:256) /\
      i * type_memory_size dtv < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `?t. val_in_memory dtv v (w2n (dw + n2w (i * type_memory_size dtv))) t.vs_memory /\
       typed_copy_effect ctx func b4 b5 u t
         (w2n (dw + n2w (i * type_memory_size dtv))) (type_memory_size dtv)` by
    (irule typed_memory_child_forward_apply >> simp[] >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >> decide_tac) >>
  (`typed_copy_effect ctx func sa b4 s u
      (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)` by
     (simp[typed_copy_effect_def] >>
      qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
   qexists_tac `t` >> conj_tac
   >- (qpat_x_assum `val_in_memory dtv v _ t.vs_memory` mp_tac >> simp[]) >>
   match_mp_tac (GEN_ALL placeMemoryCopyEffectTheory.typed_copy_effect_then) >>
   qexistsl_tac [`u`, `b4`, `b4`] >> gvs[] >>
   metis_tac[not_fresh_at_mono])
QED

(* The semantic loop step is independent of sparse versus dense lookup. Keep
   the complete source alive and retain every earlier destination element. *)
Theorem typed_memory_array_prefix_step:
  typed_copy_effect ctx func sa sb s t (dst + i * type_memory_size dtv)
    (type_memory_size dtv) /\
  val_in_memory dtv (elem i) (dst + i * type_memory_size dtv) t.vs_memory /\
  val_in_memory stv v src s.vs_memory /\ val_wf stv v /\
  (src + type_memory_size stv <= dst \/
   dst + N * type_memory_size dtv <= src) /\ i < N /\
  (!j. j < i ==> val_wf dtv (elem j) /\
     val_in_memory dtv (elem j) (dst + j * type_memory_size dtv) s.vs_memory) ==>
  val_in_memory stv v src t.vs_memory /\
  (!j. j < SUC i ==>
     val_in_memory dtv (elem j) (dst + j * type_memory_size dtv) t.vs_memory)
Proof
  strip_tac >> (
  `i * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
    (`SUC i <= N` by decide_tac >>
     `SUC i * type_memory_size dtv <= N * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * _ <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  conj_tac
  >- (irule val_in_memory_outside_write >> simp[] >>
      qexistsl_tac [`dst + i * type_memory_size dtv`, `s.vs_memory`, `type_memory_size dtv`] >>
      reverse conj_tac >- (simp[] >> decide_tac) >> rpt strip_tac >>
      irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[]) >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j = i` >- simp[] >>
  `j < i` by decide_tac >>
  `j * type_memory_size dtv + type_memory_size dtv <= i * type_memory_size dtv` by
    (`SUC j <= i` by decide_tac >>
     `SUC j * type_memory_size dtv <= i * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC j * _ <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  irule val_in_memory_outside_write >> simp[] >>
  qexistsl_tac [`dst + i * type_memory_size dtv`, `s.vs_memory`, `type_memory_size dtv`] >>
  reverse conj_tac >- (simp[] >> decide_tac) >> rpt strip_tac >>
  irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[])
QED

(* Semantic finite iteration. The round callback includes condition and
   backedge control, but retains the small element write window. Freshness is
   measured at the pre-counter state sa throughout, since the backedge writes
   the counter on every round. *)
Theorem typed_memory_array_iteration_forward:
  val_wf stv v /\
  (!j. j < N ==> val_wf dtv (elem j)) /\
  (src + type_memory_size stv <= dst \/
   dst + N * type_memory_size dtv <= src) /\
  val_in_memory stv v src u.vs_memory /\
  typed_copy_effect ctx func sa head s u dst (N * type_memory_size dtv) /\
  lookup_var counter u = SOME (n2w 0) /\
  (!i a. i < N /\
     val_in_memory stv v src a.vs_memory /\
     (!j. j < i ==> val_in_memory dtv (elem j)
       (dst + j * type_memory_size dtv) a.vs_memory) /\
     typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
     lookup_var counter a = SOME (n2w i) ==>
     ?b. val_in_memory dtv (elem i)
           (dst + i * type_memory_size dtv) b.vs_memory /\
         typed_copy_effect ctx func sa head a b
           (dst + i * type_memory_size dtv) (type_memory_size dtv) /\
         lookup_var counter b = SOME (n2w (SUC i))) ==>
  ?t. val_in_memory stv v src t.vs_memory /\
      (!j. j < N ==> val_in_memory dtv (elem j)
        (dst + j * type_memory_size dtv) t.vs_memory) /\
      typed_copy_effect ctx func sa head s t dst (N * type_memory_size dtv) /\
      lookup_var counter t = SOME (n2w N)
Proof
  strip_tac >> (
  `!i. i <= N ==> ?a.
     val_in_memory stv v src a.vs_memory /\
     (!j. j < i ==> val_in_memory dtv (elem j)
       (dst + j * type_memory_size dtv) a.vs_memory) /\
     typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
     lookup_var counter a = SOME (n2w i)` suffices_by metis_tac[LESS_EQ_REFL] >>
  Induct >> strip_tac
  >- (qexists_tac `u` >> simp[]) >>
  `i <= N /\ i < N` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!i a. _` drule_all >> strip_tac >>
  `val_in_memory stv v src b.vs_memory /\
   (!j. j < SUC i ==> val_in_memory dtv (elem j)
     (dst + j * type_memory_size dtv) b.vs_memory)` by
    (irule typed_memory_array_prefix_step >>
     conj_tac >- (qexists_tac `N` >> simp[]) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `i * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
    (`SUC i * type_memory_size dtv <= N * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * _ <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `typed_copy_effect ctx func sa head a b dst (N * type_memory_size dtv)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> decide_tac) >>
  qexists_tac `b` >> simp[] >>
  match_mp_tac (GEN_ALL placeMemoryCopyEffectTheory.typed_copy_effect_then) >>
  qexistsl_tac [`a`, `head`, `sa`] >> simp[])
QED

(* Rebase the element's old-variable frame to the compiler state before the
   loop counter was allocated. The increment intentionally overwrites counter,
   so a body-local frame cannot be the round's result contract. *)
Theorem typed_memory_array_backedge_effect:
  typed_copy_effect ctx func bst b5 s v d n /\
  lookup_var counter s = SOME (n2w i) /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==>
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME bb /\
  DROP (LENGTH b5.cs_current_insts) bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  SUC i < dimword (:256) /\
  head.cs_current_bb = hdr /\ head.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old head s t d n /\
      lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory
Proof
  strip_tac >>
  `lookup_var counter v = SOME (n2w i)` by
    metis_tac[typed_copy_effect_lookup] >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `gas_marked_path F ctx func v 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    (irule typed_memory_array_backedge_forward >> simp[] >>
     qexistsl_tac [`id1`, `id2`, `id3`] >> simp[]) >>
  `gas_marked_path F ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    (drule typed_copy_effect_path >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, ADD_CLAUSES]) >>
  qexists_tac `jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)` >>
  simp[jump_to_def, lookup_var_update_var] >>
  qpat_x_assum `typed_copy_effect _ _ _ _ _ _ _ _` mp_tac >>
  strip_tac >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem typed_memory_array_condition_effect:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done) /\
  next.cs_current_bb = (if i < N then blabel else exit) /\
  next.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old next s t d n /\
      lookup_var counter t = SOME (n2w i) /\ t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `gas_marked_path F ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))` by
    (irule typed_memory_array_condition_forward >> simp[eval_operand_def] >>
     qexistsl_tac [`counter`, `id1`, `id2`, `id3`, `length`] >> simp[]) >>
  qexists_tac `jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

(* Execute one real condition/element/backedge round. The semantic callback is
   just the address calculation and recursive element copy, not the loop. *)
Theorem typed_memory_array_round_effect:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME hbb /\
  hbb.bb_instructions =
    [mk_inst h1 LT [Var counter; length] [lt];
     mk_inst h2 ISZERO [Var lt] [done];
     mk_inst h3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i < N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done /\
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  bst.cs_current_bb = blabel /\ bst.cs_current_insts = [] /\
  head.cs_current_bb = s.vs_current_bb /\ head.cs_current_insts = [] /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME ebb /\
  DROP (LENGTH b5.cs_current_insts) ebb.bb_instructions =
    [mk_inst e1 ADD [Var counter; Lit 1w] [inc];
     mk_inst e2 ASSIGN [Var inc] [counter];
     mk_inst e3 JMP [Label head.cs_current_bb] []] /\
  (!a. typed_copy_effect ctx func old bst s a d n /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory ==>
       ?v. val_in_memory dtv value d v.vs_memory /\
           typed_copy_effect ctx func bst b5 a v d n) ==>
  ?t. val_in_memory dtv value d t.vs_memory /\
      typed_copy_effect ctx func old head s t d n /\
      lookup_var counter t = SOME (n2w (SUC i))
Proof
  strip_tac >>
  `?a. typed_copy_effect ctx func old bst s a d n /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory` by
    (irule typed_memory_array_condition_effect >>
     qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  qpat_x_assum `!a. _ ==> ?v. _` drule_all >> strip_tac >>
  `?t. typed_copy_effect ctx func old head a t d n /\
       lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory` by
    (irule typed_memory_array_backedge_effect >>
     qpat_assum `typed_copy_effect ctx func bst b5 a v d n` (irule_at Any) >>
     qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  qexists_tac `t` >> simp[] >>
  match_mp_tac (GEN_ALL placeMemoryCopyEffectTheory.typed_copy_effect_then) >>
  qexistsl_tac [`a`, `bst`, `old`] >> simp[]
QED

(* Compiler decomposition only; the shared lookup theorem is reused for the
   finished blocks rather than duplicated for the static label names. *)
Theorem typed_memory_sarray_slow_compile:
  compile_copy_sarray_typed cenv dst dt src st numelts sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\
    ~is_abi_dynamic cenv.ce_struct_fields dt) ==>
  ?hdr l1 blabel l2 exit l3 counter init st0 st1 u1 sth
   lt h1 done stj st2 u2 stb so b1 doff b2 sp b3 dp b4 b5 inc b6 ste st3 u3.
  fresh_label "typed_sa_cond" sa = (hdr,l1) /\
  fresh_label "typed_sa_body" l1 = (blabel,l2) /\
  fresh_label "typed_sa_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; Lit (n2w numelts)] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem typed_memory_sarray_slow_forward:
  compile_copy_sarray_typed cenv dst dt src st N sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\
    ~is_abi_dynamic cenv.ce_struct_fields dt) /\
  typed_memory_child_forward cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  value_has_type (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
    (w2n sw) s.vs_memory /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv + 64 < dimword (:256) /\
  N < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (N * type_memory_size dtv)
Proof
  strip_tac >> (
  drule_all typed_memory_sarray_slow_compile >> strip_tac >>
  drule_all typed_copy_slow_array_control_layout >> strip_tac >>
  `(do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
       doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
       sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
       return (sp,dp) od) stb = ((sp,dp),b4)` by
    simp[comp_bind_def, comp_return_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  `?u. typed_copy_effect ctx func sa sth s u (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter u = SOME (n2w 0) /\ u.vs_memory = s.vs_memory` by
    suspend "initial" >>
  `default_value stv = default_value dtv` by metis_tac[typed_memory_widening_defaults] >>
  qabbrev_tac `elem = \i. case ALOOKUP kvs i of NONE => default_value stv | SOME v => v` >>
  `!i. value_has_type stv (elem i) /\ val_wf stv (elem i) /\
       value_has_type dtv (elem i) /\ val_wf dtv (elem i)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`value_has_type (ArrayTV dtv _) _`, `value_has_type (ArrayTV stv _) _`,
        `val_wf (ArrayTV dtv _) _`, `val_wf (ArrayTV stv _) _`,
        `evaluate_type tenv dt = _`, `evaluate_type tenv st = _`,
        `default_value stv = _`] >>
     simp[Abbr `elem`, NoAsms] >> rpt (first_x_assum kall_tac) >>
     simp[valueEncodingDefsTheory.val_wf_def] >> rpt strip_tac >>
     metis_tac[typed_memory_sparse_lookup_type, typed_memory_sparse_lookup_wf]) >>
  `?z. val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
          (w2n sw) z.vs_memory /\
       (!j. j < N ==> val_in_memory dtv (elem j)
          (w2n dw + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sa sth s z (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter z = SOME (n2w N)` by
    (irule typed_memory_array_iteration_forward >>
     qpat_assum `typed_copy_effect _ _ sa sth s u _ _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     suspend "round") >>
  suspend "exit")
QED

Resume typed_memory_sarray_slow_forward[initial]:
  markerLib.RESUME_TAC >>
  `gas_marked_path F ctx func s 0
     (OK (jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1)))` by
    (irule typed_memory_array_init_forward >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  qexists_tac `jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Resume typed_memory_sarray_slow_forward[round]:
  markerLib.RESUME_TAC >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >>
  rpt strip_tac >>
  irule typed_memory_array_element_forward >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `sw` >>
  `eval_operand src a' = SOME sw /\ eval_operand dst a' = SOME dw` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[eval_operand_def] >>
     qpat_x_assum `typed_copy_effect ctx func sa sth s a _ _` mp_tac >>
     qpat_x_assum `typed_copy_effect ctx func sa stb a a' _ _` mp_tac >>
     simp[typed_copy_effect_def] >> rpt strip_tac >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  `i * type_memory_size stv + type_memory_size stv <= N * type_memory_size stv /\
   i * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
    (`SUC i <= N` by decide_tac >>
     `SUC i * type_memory_size stv <= N * type_memory_size stv /\
      SUC i * type_memory_size dtv <= N * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * type_memory_size stv <= _` mp_tac >>
     qpat_x_assum `SUC i * type_memory_size dtv <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory stv (elem i) (w2n sw + i * type_memory_size stv) a.vs_memory` by
    (simp[Abbr `elem`, NoAsms] >> irule typed_memory_sarray_element >>
     rpt (goal_assum (drule_at Any))) >>
  gvs[typed_copy_effect_def] >> decide_tac
QED

Resume typed_memory_sarray_slow_forward[exit]:
  markerLib.RESUME_TAC >> (
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `?t. typed_copy_effect ctx func sa sb z t (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter t = SOME (n2w N) /\ t.vs_memory = z.vs_memory` by
    (drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_condition_effect >>
     disch_then irule >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (irule typed_memory_sarray_intro >> simp[] >>
      qpat_x_assum `!j. j < N ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  match_mp_tac (GEN_ALL placeMemoryCopyEffectTheory.typed_copy_effect_then) >>
  qexistsl_tac [`z`, `sth`, `sa`] >> simp[])
QED

Finalise typed_memory_sarray_slow_forward

(* Separate the dynamic header setup from the same slow-loop control skeleton. *)
Theorem typed_memory_dynarray_slow_compile:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  fn_has_code sa sb func ==>
  ?length src_data dst_data sm hdr l1 blabel l2 exit l3 counter init st0 st1 u1 sth
   lt h1 done stj st2 u2 stb so b1 doff b2 sp b3 dp b4 b5 inc b6 ste st3 u3.
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sm) /\
  fresh_label "typed_dyn_cond" sm = (hdr,l1) /\
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
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))] b1 = (doff,b2) /\
  emit_op ADD [src_data;so] b2 = (sp,b3) /\
  emit_op ADD [dst_data;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,sb) /\
  same_blocks sa sm /\ isPREFIX sa.cs_current_insts sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. length = Var x ==> not_fresh_at sm x) /\
  (!x. src_data = Var x ==> not_fresh_at sm x) /\
  (!x. dst_data = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_op LT _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ISZERO [lt_op] _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_op MUL _ _ = _` kall_tac) >>
  qpat_x_assum `emit_op ADD [src_data; _] _ = _` kall_tac >>
  qpat_x_assum `emit_op ADD [dst_data; _] _ = _` kall_tac >>
  qpat_x_assum `emit_op ADD [Var counter; _] _ = _` kall_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND, not_fresh_at_def, toString_inj] >>
  rpt strip_tac >> decide_tac
QED

Theorem typed_memory_dynarray_slow_forward:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  typed_memory_child_forward cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) + 64 < dimword (:256) /\
  cap < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic cap)))
Proof
  strip_tac >> (
  drule_all typed_memory_dynarray_slow_compile >> strip_tac >>
  `fn_has_code sm sb func` by
    (qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def, same_blocks_def]) >>
  drule_all typed_copy_dynarray_slow_code_lookup >> strip_tac >>
  `isPREFIX sm.cs_current_insts st1.cs_current_insts /\
   st1.cs_current_bb = sm.cs_current_bb` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fresh_label "typed_dyn_cond" _ = _`,
        `fresh_label "typed_dyn_body" _ = _`,
        `fresh_label "typed_dyn_exit" _ = _`,
        `fresh_var _ = _`, `emit_inst ASSIGN [Lit 0w] _ _ = _`,
        `emit_inst JMP [Label hdr] _ st0 = _`] >>
     rpt (first_x_assum kall_tac) >>
     simp[fresh_label_def, fresh_var_def, emit_inst_def, fresh_id_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sm func` by
    (simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
     gvs[same_blocks_def] >>
     metis_tac[listTheory.isPREFIX_TRANS]) >>
  drule_all typed_copy_slow_array_control_layout >> strip_tac >>
  `(do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
       doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
       sp <- emit_op ADD [src_data; so]; dp <- emit_op ADD [dst_data; doff];
       return (sp,dp) od) stb = ((sp,dp),b4)` by
    simp[comp_bind_def, comp_return_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_block st1.cs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block st2.cs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block st3.cs_current_bb _ = _` kall_tac >>
  `LENGTH vs <= cap /\ LENGTH vs <= scap` by
    metis_tac[typed_memory_dynarray_length] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[valueEncodingDefsTheory.val_in_memory_def, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  drule_all typed_memory_dynarray_setup_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_effect ctx func sa sm s t (w2n dw)
     (type_memory_size (ArrayTV dtv (Dynamic cap)))` by
    (simp[typed_copy_effect_def] >> conj_tac
     >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     conj_tac
     >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     rpt strip_tac >>
     qpat_x_assum `!a len. _` (qspecl_then [`a`, `len`] mp_tac) >>
     simp[] >> gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `?u. typed_copy_effect ctx func sm sth t u (w2n dw + 32)
        (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter u = SOME 0w /\ u.vs_memory = t.vs_memory` by
    (suspend "initial") >>
  suspend "integration")
QED

Resume typed_memory_dynarray_slow_forward[initial]:
  markerLib.RESUME_TAC >> (
  `gas_marked_path F ctx func t 0
     (OK (jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)))` by
    (irule typed_memory_array_init_forward >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  qexists_tac `jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> first_x_assum drule >> simp[])
QED

Resume typed_memory_dynarray_slow_forward[integration]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `lookup_block sb.cs_current_bb _ = SOME bb` kall_tac >>
  qpat_x_assum `isPREFIX sb.cs_current_insts _` kall_tac >>
  qpat_x_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` kall_tac >>
  qpat_x_assum `st1.cs_current_bb = _` kall_tac >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
     (w2n sw) u.vs_memory` by
    (simp[] >> irule val_in_memory_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw`, `s.vs_memory`, `type_memory_size (ArrayTV dtv (Dynamic cap))`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!a len. _` (qspecl_then [`a`, `len`] mp_tac) >>
     simp[] >> gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  qabbrev_tac `elem = \i. EL i vs` >>
  `!i. i < LENGTH vs ==>
       value_has_type stv (elem i) /\ val_wf stv (elem i) /\
       value_has_type dtv (elem i) /\ val_wf dtv (elem i)` by
    (simp[Abbr `elem`, NoAsms] >>
     map_every (fn q => qpat_assum q mp_tac)
       [`value_has_type (ArrayTV dtv _) _`, `value_has_type (ArrayTV stv _) _`,
        `val_wf (ArrayTV dtv _) _`, `val_wf (ArrayTV stv _) _`] >>
     rpt (first_x_assum kall_tac) >>
     simp[ valueEncodingDefsTheory.val_wf_def, vyperTypingTheory.value_has_type_def] >>
     qid_spec_tac `vs` >> Induct >> simp[valueEncodingDefsTheory.val_wf_def,
       vyperTypingTheory.value_has_type_def] >> rpt strip_tac >>
     Cases_on `i` >> gvs[] >> metis_tac[]) >>
  `?z. val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
          (w2n sw) z.vs_memory /\
       (!j. j < LENGTH vs ==> val_in_memory dtv (elem j)
          (w2n dw + 32 + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sm sth t z (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter z = SOME (n2w (LENGTH vs))` by
    (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)
       typed_memory_array_iteration_forward >>
     disch_then irule >>
     (conj_tac >- suspend "round") >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >- simp[]) >>
     (conj_tac >- (gvs[valueEncodingTheory.type_memory_size_def] >>
       `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
       decide_tac)) >> simp[]) >>
  suspend "exit")
QED

Resume typed_memory_dynarray_slow_forward[round]:
  markerLib.RESUME_TAC >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x t` by
    (metis_tac[typed_copy_effect_lookup]) >>
  `a.vs_labels = t.vs_labels` by
    (drule_at (Pat `typed_copy_effect _ _ _ _ t a _ _`) typed_copy_effect_record >>
     disch_then (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `!oper w. eval_operand oper t = SOME w /\
      (!x. oper = Var x ==> not_fresh_at sm x) ==>
      eval_operand oper a = SOME w` by
    (qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x a = _` mp_tac >>
     qpat_x_assum `a.vs_labels = t.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> Cases_on `oper` >> gvs[eval_operand_def]) >>
  `eval_operand length a = SOME (n2w (LENGTH vs))` by metis_tac[] >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt strip_tac >>
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (`w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
       (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_add_2]) >>
  `?v. val_in_memory dtv (elem i)
        (w2n (dw + 32w) + i * type_memory_size dtv) v.vs_memory /\
       typed_copy_effect ctx func stb b5 a' v
        (w2n (dw + 32w) + i * type_memory_size dtv) (type_memory_size dtv)`
    suffices_by (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  irule typed_memory_array_element_forward >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `sw + 32w` >>
  `eval_operand src_data a' = SOME (sw + 32w) /\
   eval_operand dst_data a' = SOME (dw + 32w)` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t a _ _` mp_tac >>
     qpat_x_assum `typed_copy_effect ctx func sm stb a a' _ _` mp_tac >>
     qpat_x_assum `eval_operand src_data t = SOME (sw + 32w)` mp_tac >>
     qpat_x_assum `eval_operand dst_data t = SOME (dw + 32w)` mp_tac >>
     qpat_x_assum `!x. src_data = Var x ==> _` mp_tac >>
     qpat_x_assum `!x. dst_data = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `src_data` >> Cases_on `dst_data` >>
     simp[eval_operand_def, typed_copy_effect_def,
          venom_state_component_equality] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `i * type_memory_size stv + type_memory_size stv <= scap * type_memory_size stv /\
   i * type_memory_size dtv + type_memory_size dtv <= cap * type_memory_size dtv` by
    (`SUC i <= scap /\ SUC i <= cap` by decide_tac >>
     `SUC i * type_memory_size stv <= scap * type_memory_size stv /\
      SUC i * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * type_memory_size stv <= _` mp_tac >>
     qpat_x_assum `SUC i * type_memory_size dtv <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory stv (elem i) (w2n sw + 32 + i * type_memory_size stv) a.vs_memory` by
    (qpat_x_assum `val_in_memory (ArrayTV stv _) _ _ a.vs_memory` mp_tac >>
     simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
     drule exprSimAggregateEncodingTheory.elems_in_memory_EL >>
     disch_then (qspec_then `i` mp_tac) >>
     simp[Abbr `elem`, AC ADD_ASSOC ADD_COMM]) >>
  gvs[typed_copy_effect_def, valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

Resume typed_memory_dynarray_slow_forward[exit]:
  markerLib.RESUME_TAC >> (
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `eval_operand length z = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t z _ _` mp_tac >>
     qpat_x_assum `eval_operand length t = SOME (n2w (LENGTH vs))` mp_tac >>
     qpat_x_assum `!x. length = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `length` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `?r. typed_copy_effect ctx func sm sb z r (w2n dw + 32)
         (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter r = SOME (n2w (LENGTH vs)) /\ r.vs_memory = z.vs_memory` by
    (drule_at (Pat `hbb.bb_instructions = _`)
       (Q.INST [`N` |-> `LENGTH (vs:value list)`, `i` |-> `LENGTH (vs:value list)`]
         typed_memory_array_condition_effect) >>
     disch_then (qspec_then `vs` irule) >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  `typed_copy_effect ctx func sm sb t r (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv)` by
    (match_mp_tac (GEN_ALL typed_copy_effect_then) >>
     qexistsl_tac [`z`, `sth`, `sm`] >> simp[]) >>
  `mem_bytes_at (w2n dw) 32 r.vs_memory = mem_bytes_at (w2n dw) 32 t.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `r` >> conj_tac
  >- (simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> conj_tac
      >- (qpat_x_assum `mem_bytes_at _ _ r.vs_memory = _` mp_tac >>
          gvs[valueEncodingDefsTheory.mem_word_at_def, valueEncodingDefsTheory.mem_bytes_at_def]) >>
      irule exprSimAggregateEncodingTheory.elems_in_memory_intro >>
      qpat_x_assum `!j. j < LENGTH vs ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  match_mp_tac (GEN_ALL typed_copy_effect_then) >>
  qexistsl_tac [`t`, `sm`, `sm`] >> simp[] >> conj_tac
  >- (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >>
      simp[valueEncodingTheory.type_memory_size_def] >>
      `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
      decide_tac) >>
  metis_tac[not_fresh_at_mono])
QED

Finalise typed_memory_dynarray_slow_forward
