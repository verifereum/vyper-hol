(* Recursive typed-copy element execution with a shared checked endpoint. *)
Theory typedCopyArrayPathMem
Ancestors
  typedCopyControlPathMem placeMemoryArrayForward placeMemoryCopyEffect
  placeMemoryTypedBase placeMemoryChildForward context compileEnv emitHelperProps
  venomState venomExecSemantics freshWrites fragGasMode fragGasPathMem arithmetic
  placeMemoryArrayControl placeMemoryCodeLayout exprLoweringProps emitHelper
  valueEncoding valueEncodingProps

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

Theorem typed_memory_array_iteration_forward_mem:
  val_wf stv v /\
  (!j. j < N ==> val_wf dtv (elem j)) /\
  (src + type_memory_size stv <= dst \/
   dst + N * type_memory_size dtv <= src) /\
  val_in_memory stv v src u.vs_memory /\
  typed_copy_effect ctx func sa head s u dst (N * type_memory_size dtv) /\
  gas_path_mem ctx func s 0 (OK u) /\
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
         gas_path_mem ctx func a 0 (OK b) /\
         lookup_var counter b = SOME (n2w (SUC i))) ==>
  ?t. val_in_memory stv v src t.vs_memory /\
      (!j. j < N ==> val_in_memory dtv (elem j)
        (dst + j * type_memory_size dtv) t.vs_memory) /\
      typed_copy_effect ctx func sa head s t dst (N * type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w N)
Proof
  strip_tac >> (
  `!i. i <= N ==> ?a.
     val_in_memory stv v src a.vs_memory /\
     (!j. j < i ==> val_in_memory dtv (elem j)
       (dst + j * type_memory_size dtv) a.vs_memory) /\
     typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
     gas_path_mem ctx func s 0 (OK a) /\
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
  qexists_tac `b` >> simp[] >> conj_tac
  >- (irule typed_copy_effect_then >>
      qexistsl_tac [`sa`, `head`, `a`] >> simp[]) >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED

Theorem typed_memory_sarray_slow_forward_mem:
  compile_copy_sarray_typed cenv dst dt src st N sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\
    ~is_abi_dynamic cenv.ce_struct_fields dt) /\
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
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  N < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (N * type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK t)
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
       gas_path_mem ctx func s 0 (OK u) /\
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
     simp[valueEncodingTheory.val_wf_def] >> rpt strip_tac >>
     metis_tac[typed_memory_sparse_lookup_type, typed_memory_sparse_lookup_wf]) >>
  `?z. val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
          (w2n sw) z.vs_memory /\
       (!j. j < N ==> val_in_memory dtv (elem j)
          (w2n dw + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sa sth s z (w2n dw) (N * type_memory_size dtv) /\
       gas_path_mem ctx func s 0 (OK z) /\
       lookup_var counter z = SOME (n2w N)` by
    (irule typed_memory_array_iteration_forward_mem >>
     qpat_assum `typed_copy_effect _ _ sa sth s u _ _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     suspend "round") >>
  suspend "exit")
QED

Resume typed_memory_sarray_slow_forward_mem[initial]:
  markerLib.RESUME_TAC >>
  `gas_path_mem ctx func s 0 (OK (jump_to hdr (update_var counter 0w s)))` by
    (irule typed_memory_array_init_path_mem >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  drule gas_marked_path_from_mem >> disch_then (qspec_then `F` assume_tac) >>
  qexists_tac `jump_to hdr (update_var counter 0w s)` >> simp[] >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Resume typed_memory_sarray_slow_forward_mem[round]:
  markerLib.RESUME_TAC >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect_mem >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >>
  rpt strip_tac >>
  irule typed_memory_array_element_forward_mem >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `sw` >>
  `eval_operand src a' = SOME sw /\ eval_operand dst a' = SOME dw` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`typed_copy_effect ctx func sa sth s a _ _`,
        `typed_copy_effect ctx func sa stb a a' _ _`,
        `!x. src = Var x ==> _`, `!x. dst = Var x ==> _`,
        `eval_operand src s = SOME sw`, `eval_operand dst s = SOME dw`] >>
     rpt (pop_assum kall_tac) >>
     Cases_on `src` >> Cases_on `dst` >>
     simp[typed_copy_effect_def, eval_operand_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
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
  `a'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `typed_copy_effect ctx func sa sth s a _ _`
       (mp_then Any mp_tac typed_copy_effect_record) >>
     qpat_assum `typed_copy_effect ctx func sa stb a a' _ _`
       (mp_then Any mp_tac typed_copy_effect_record) >>
     simp[venom_state_component_equality]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  simp[] >> decide_tac
QED

Resume typed_memory_sarray_slow_forward_mem[exit]:
  markerLib.RESUME_TAC >> (
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `?t. typed_copy_effect ctx func sa sb z t (w2n dw) (N * type_memory_size dtv) /\
       gas_path_mem ctx func z 0 (OK t) /\
       lookup_var counter t = SOME (n2w N) /\ t.vs_memory = z.vs_memory` by
    (drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_condition_effect_mem >>
     disch_then irule >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (irule typed_memory_sarray_intro >> simp[] >>
      qpat_x_assum `!j. j < N ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  conj_tac
  >- (irule typed_copy_effect_then >>
      qexistsl_tac [`sa`, `sth`, `z`] >> simp[]) >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED

Finalise typed_memory_sarray_slow_forward_mem
