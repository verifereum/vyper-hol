(* Recursive typed-copy element execution with a shared checked endpoint. *)
Theory typedCopyArrayPathMem
Ancestors
  typedCopyControlPathMem placeMemoryArrayForward placeMemoryCopyEffect
  placeMemoryTypedBase placeMemoryChildForward context compileEnv emitHelperProps
  venomState venomExecSemantics freshWrites fragGasMode fragGasPathMem arithmetic

Theorem typed_memory_array_element_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  (!st dtv stv v dp sp a b u dw sw.
    type_widens_to tenv st dt /\
    evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t)) /\
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
  w2n sw + i * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
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
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  strip_tac >> (
  drule_all typed_memory_array_addresses_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule typed_memory_array_addresses_fresh >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(_ with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `w2n (sw + n2w (i * type_memory_size stv)) = w2n sw + i * type_memory_size stv /\
   w2n (dw + n2w (i * type_memory_size dtv)) = w2n dw + i * type_memory_size dtv` by
    (`w2n sw + i * type_memory_size stv < dimword (:256) /\
      w2n dw + i * type_memory_size dtv < dimword (:256) /\
      i * type_memory_size stv < dimword (:256) /\
      i * type_memory_size dtv < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD]) >>
  qpat_x_assum `!st dtv stv v dp sp a b u dw sw. _` drule >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `u` mp_tac) >> simp[] >> strip_tac >>
  `typed_copy_effect ctx func sa b4 s u
      (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)` by
    (qpat_assum `gas_path_mem ctx func s 0 (OK u)`
       (mp_then Any (qspec_then `F` assume_tac) gas_marked_path_from_mem) >>
     simp[typed_copy_effect_def] >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule typed_copy_effect_then >>
      qexistsl_tac [`b4`, `b4`, `u`] >> simp[] >>
      metis_tac[not_fresh_at_mono]) >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED

Theorem typed_memory_array_round_effect_mem:
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
           typed_copy_effect ctx func bst b5 a v d n /\
           gas_path_mem ctx func a 0 (OK v)) ==>
  ?t. val_in_memory dtv value d t.vs_memory /\
      typed_copy_effect ctx func old head s t d n /\
      gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w (SUC i))
Proof
  strip_tac >>
  `?a. typed_copy_effect ctx func old bst s a d n /\
       gas_path_mem ctx func s 0 (OK a) /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory` by
    (irule typed_memory_array_condition_effect_mem >>
     qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  qpat_x_assum `!a. _ ==> ?v. _` drule_all >> strip_tac >>
  `?t. typed_copy_effect ctx func old head a t d n /\
       gas_path_mem ctx func a 0 (OK t) /\
       lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory` by
    (irule typed_memory_array_backedge_effect_mem >>
     qpat_assum `typed_copy_effect ctx func bst b5 a v d n` (irule_at Any) >>
     qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule typed_copy_effect_then >>
      qexistsl_tac [`old`, `bst`, `a`] >> simp[]) >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
