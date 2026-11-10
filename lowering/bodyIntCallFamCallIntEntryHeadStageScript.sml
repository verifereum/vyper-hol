(* Singleton staging, retaining the completed prefix and deferred suffix. *)
Theory bodyIntCallFamCallIntEntryHeadStage
Ancestors
  bodyIntCallFamCallIntAllocatedStage bodyIntCallFamCallIntWordStage
  bodyIntCallFamCallIntStageAdapters bodyIntCallFamCallIntStageInterface
  bodyIntCallJointCallCore bodyIntCallJointContract exprLoweringProps
  exprLowering compileEnv fragExec loweringPosts
Libs
  monadsyntax

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;
val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

Theorem intcall_singleton_stage_endpoint:
  compile_stage_intcall_args ce [vv] [flag] [expr_type e] a = ([op],c) /\
  ^deferred fp ce e vv r a es t /\ post_value_type ce e = expr_type e /\
  vv_type vv = expr_type e /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  (flag ==> is_word_type (expr_type e)) /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es a t /\
  fn_has_code a c fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  start.cs_next_id <= a.cs_next_id /\
  ^deferred_list fp ce ds vs rs a es t /\
  ^completed_prefix fp.jc_cx start a tys flags values ops t /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv ==>
    val_wf tv (EL i values)) /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^deferred_list fp ce ds vs rs c es u /\
    ^completed_prefix fp.jc_cx start c (tys ++ [expr_type e]) (flags ++ [flag])
      (values ++ [v]) (ops ++ [op]) u
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `flag`
  >- suspend "word" >>
  suspend "memory"
QED

Resume intcall_singleton_stage_endpoint[word]:
  gvs[compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  drule_all exprSimAggregateChildrenTheory.vv_holds_materialise >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `expr_type e`, `tv` |-> `tv`,
    `sa` |-> `a`, `sb` |-> `c`, `s` |-> `t`]
    (SPEC_ALL (BETA_RULE intcall_word_stage_endpoint))) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `u` >> gvs[]
QED

Resume intcall_singleton_stage_endpoint[memory]:
  gvs[compile_stage_intcall_args_def, intcall_stage_write,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `unwrap_value ce vv a = (src,b)` >>
  rename1 `compile_alloc_buffer _ b = (buf,d)` >>
  rename1 `vv_at ce fp.jc_cx (expr_type e) origin a es r vv t` >>
  `cs_extends a b /\ a.cs_next_id <= b.cs_next_id /\
   a.cs_next_var <= b.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`vv`,`a`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `cs_extends b d /\ cs_extends d c` by
    (mp_tac (Q.SPECL [`MAX 32 (type_memory_size tv)`,`b`]
       ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`ce`,`src`,`buf.buf_operand`,`expr_type e`,`expr_type e`,`d`]
       ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  `fn_has_code a b fp.jc_func /\ fn_has_code b d fp.jc_func /\
   fn_has_code d c fp.jc_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  mp_tac (Q.INST [`sa` |-> `a`, `sb` |-> `b`, `s` |-> `t`, `op` |-> `src`]
    (SPEC_ALL (BETA_RULE intcall_stage_forcing_endpoint))) >>
  (impl_tac >- (simp[] >> qexists_tac `origin` >> simp[])) >>
  strip_tac >> rename1 `intcall_expr_cont fp ce env es a t es b mid` >>
  suspend "store"
QED

Resume intcall_singleton_stage_endpoint[store]:
  `type_memory_size tv + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `start.cs_next_id <= b.cs_next_id` by decide_tac >>
  `intcall_expr_res fp ce env es b mid /\ ~mid.vs_halted /\
   mid.vs_current_bb = b.cs_current_bb /\
   mid.vs_inst_idx = LENGTH b.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  drule_all (BETA_RULE intcall_allocated_store_endpoint) >> strip_tac >>
  `intcall_expr_cont fp ce env es a t es c u` by
    (irule intcall_expr_cont_trans >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  qexists_tac `u` >> gvs[]
QED

Finalise intcall_singleton_stage_endpoint
