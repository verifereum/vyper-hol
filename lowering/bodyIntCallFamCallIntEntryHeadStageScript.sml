(* Singleton staging, retaining the completed prefix and deferred suffix. *)
Theory bodyIntCallFamCallIntEntryHeadStage
Ancestors
  bodyIntCallFamCallIntAllocatedStage bodyIntCallFamCallIntWordStage
  bodyIntCallFamCallIntStageAdapters bodyIntCallFamCallIntStageInterface
  bodyIntCallJointCallCore bodyIntCallJointContract exprLoweringProps
  exprLowering compileEnv fragExec loweringPosts bodyIntCallStageOrigin
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

Theorem intcall_singleton_stage_origin_endpoint:
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
      (values ++ [v]) (ops ++ [op]) u /\
    (~flag ==> ?aid len inst w.
      eval_operand op u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,len) /\
      MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ start.cs_next_id <= aid /\ aid < c.cs_next_id /\
      type_memory_size tv <= len)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `flag`
  >- suspend "word" >>
  suspend "memory"
QED

Resume intcall_singleton_stage_origin_endpoint[word]:
  gvs[compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  drule_all exprSimAggregateChildrenTheory.vv_holds_materialise >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `expr_type e`, `tv` |-> `tv`,
    `sa` |-> `a`, `sb` |-> `c`, `s` |-> `t`]
    (SPEC_ALL (BETA_RULE intcall_word_stage_endpoint))) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `u` >> gvs[]
QED

Resume intcall_singleton_stage_origin_endpoint[memory]:
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

Resume intcall_singleton_stage_origin_endpoint[store]:
  `type_memory_size tv + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `start.cs_next_id <= b.cs_next_id` by decide_tac >>
  `intcall_expr_res fp ce env es b mid /\ ~mid.vs_halted /\
   mid.vs_current_bb = b.cs_current_bb /\
   mid.vs_inst_idx = LENGTH b.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  drule_all (BETA_RULE intcall_allocated_store_origin_endpoint) >> strip_tac >>
  `intcall_expr_cont fp ce env es a t es c u` by
    (irule intcall_expr_cont_trans >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  qexists_tac `u` >> gvs[] >>
  qexistsl_tac [`MAX 32 (type_memory_size tv)`, `inst`] >> simp[]
QED

Finalise intcall_singleton_stage_origin_endpoint

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
  strip_tac >> drule_all intcall_singleton_stage_origin_endpoint >>
  strip_tac >> qexists_tac `u` >> simp[]
QED

(* Factor one compiler step without exposing its word/memory implementation. *)
Theorem intcall_stage_cons:
  compile_stage_intcall_args ce (vv::vs) (flag::flags) (ty::tys) a =
    do first <- compile_stage_intcall_args ce [vv] [flag] [ty];
       rest <- compile_stage_intcall_args ce vs flags tys;
       return (first ++ rest) od a
Proof
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> Cases_on `v` >> simp[]
QED

Theorem intcall_indexed_triple_cons[local]:
  !P (xs:'a list) (ys:'b list) (zs:'c list) x y z.
  (LENGTH (x::xs) = LENGTH (y::ys) /\
   LENGTH (x::xs) = LENGTH (z::zs) /\
   (!i. i < LENGTH (x::xs) ==>
     P (EL i (x::xs)) (EL i (y::ys)) (EL i (z::zs)))) <=>
  P x y z /\ LENGTH xs = LENGTH ys /\ LENGTH xs = LENGTH zs /\
    (!i. i < LENGTH xs ==> P (EL i xs) (EL i ys) (EL i zs))
Proof
  rpt gen_tac >> simp[Once arithmeticTheory.FORALL_NUM] >> metis_tac[]
QED

val allocation_origin = ``\func start current op tv s.
  ?aid len inst w. eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ start.cs_next_id <= aid /\ aid < current.cs_next_id /\
    type_memory_size tv <= len``;

Theorem intcall_allocation_origin_frame:
  ^allocation_origin fp.jc_func start a op tv s /\
  (!x. op = Var x ==> not_fresh_at a x) /\
  intcall_expr_cont fp ce env es a s ee b u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) /\
  a.cs_next_id <= b.cs_next_id ==>
  ^allocation_origin fp.jc_func start b op tv u
Proof
  BETA_TAC >> strip_tac >>
  `eval_operand op u = SOME w` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_saved_operand >>
     qexists_tac `a` >>
     qexistsl_tac [`fp.jc_ctx`, `fp.jc_func`, `F`, `n`, `s`] >>
     fs[intcall_expr_cont_def]) >>
  qexistsl_tac [`aid`, `len`, `inst`, `w`] >>
  fs[intcall_expr_cont_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem intcall_list_stage_origin_endpoint:
  !ds vs rs values flags a c out start tys pflags pvalues pops t.
  compile_stage_intcall_args ce vs flags (MAP expr_type ds) a = (out,c) /\
  LENGTH vs = LENGTH ds /\ LENGTH rs = LENGTH ds /\
  LENGTH values = LENGTH ds /\ LENGTH flags = LENGTH ds /\
  ^deferred_list fp ce (ds ++ tail_ds) (vs ++ tail_vs) (rs ++ tail_rs) a es t /\
  ^completed_prefix fp.jc_cx start a tys pflags pvalues pops t /\
  (!i tv. i < LENGTH tys /\ ~EL i pflags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv ==>
    val_wf tv (EL i pvalues)) /\
  (!i. i < LENGTH ds ==>
    post_value_type ce (EL i ds) = expr_type (EL i ds) /\
    vv_type (EL i vs) = expr_type (EL i ds) /\
    read_result fp.jc_cx (EL i rs) es = (INL (EL i values),es) /\
    (EL i flags ==> is_word_type (expr_type (EL i ds))) /\
    ?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv /\
      type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv (EL i values) /\
      (~EL i flags ==> val_wf tv (EL i values))) /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es a t /\
  fn_has_code a c fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  start.cs_next_id <= a.cs_next_id /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  LENGTH out = LENGTH ds /\
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^deferred_list fp ce tail_ds tail_vs tail_rs c es u /\
    ^completed_prefix fp.jc_cx start c (tys ++ MAP expr_type ds)
      (pflags ++ flags) (pvalues ++ values) (pops ++ out) u /\
    (!i tv. i < LENGTH ds /\ ~EL i flags /\
      evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv ==>
      ^allocation_origin fp.jc_func start c (EL i out) tv u)
Proof
  Induct_on `ds`
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      gvs[compile_stage_intcall_args_def, comp_return_def] >> qexists_tac `t` >>
      simp[fragGasModeTheory.gas_marked_path_def, intcall_expr_cont_def,
           locals_kept_def] >> metis_tac[fragGasPathTheory.gas_path_rules]) >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `vs` ["", "vv vs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `rs` ["", "r rs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `values` ["", "v values"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `flags` ["", "flag flags"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  suspend "head"
QED

Resume intcall_list_stage_origin_endpoint[head]:
  qpat_assum `!i. i < LENGTH (h::ds) ==> _`
    (qspec_then `0` mp_tac) >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `compile_stage_intcall_args ce (vv::vs) _ _ a = _` mp_tac >>
  simp[NoAsms, Once intcall_stage_cons, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pop_assum (fn th => assume_tac th >> pure_rewrite_tac [th]) >>
  simp[NoAsms] >>
  pairarg_tac >> pop_assum (fn th => assume_tac th >> pure_rewrite_tac [th]) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `_ = c` SUBST_ALL_TAC >>
  rename1 `compile_stage_intcall_args ce [vv] [flag] [expr_type h] a = (first,b)` >>
  `LENGTH first = 1` by
    (qpat_assum `compile_stage_intcall_args ce [vv] _ _ a = _`
       (mp_then (Pat `compile_stage_intcall_args _ _ _ _ _ = _`) mp_tac
          bodyIntCallStageOriginTheory.stage_intcall_args_length) >>
     simp[NoAsms]) >>
  namedCases_on `first` ["", "op more"]
  >- (qpat_x_assum `LENGTH [] = 1` mp_tac >> simp[NoAsms]) >>
  `more = []` by (qpat_x_assum `LENGTH (op::more) = 1` mp_tac >> simp[NoAsms]) >>
  pop_assum SUBST_ALL_TAC >>
  `ci_mono a b` by
    (qpat_assum `compile_stage_intcall_args ce [vv] _ _ a = _`
      (fn eq => mp_tac (Q.SPECL [`ce`,`[vv]`,`[flag]`,`[expr_type h]`,`a`]
        ci_mono_compile_stage_intcall_args) >> simp[NoAsms,eq])) >>
  `ci_mono b c` by
    (qpat_assum `compile_stage_intcall_args ce vs' _ _ b = _`
      (fn eq => mp_tac (Q.SPECL [`ce`,`vs'`,`flags'`,`MAP expr_type ds`,`b`]
        ci_mono_compile_stage_intcall_args) >> simp[NoAsms,eq])) >>
  `fn_has_code a b fp.jc_func /\ fn_has_code b c fp.jc_func` by
    (qpat_x_assum `!vs rs values flags a c out start tys pflags pvalues pops t. _` kall_tac >>
     fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `^deferred fp ce h vv r a es t /\
   ^deferred_list fp ce (ds ++ tail_ds) (vs' ++ tail_vs) (rs' ++ tail_rs) a es t` by
    (qpat_x_assum `!vs rs values flags a c out start tys pflags pvalues pops t. _` kall_tac >>
     qpat_x_assum `(^deferred_list) _ _ _ _ _ _ _ _` mp_tac >>
     BETA_TAC >> pure_rewrite_tac [listTheory.APPEND] >>
     CONV_TAC (LAND_CONV (HO_REWR_CONV intcall_indexed_triple_cons)) >>
     simp[NoAsms]) >>
  suspend "singleton"
QED

Resume intcall_list_stage_origin_endpoint[singleton]:
  `type_memory_size tv < 2**64` by
    (qpat_x_assum `!vs rs values flags a c out start tys pflags pvalues pops t. _` kall_tac >> simp[]) >>
  drule_all intcall_singleton_stage_origin_endpoint >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es a t es b mid` >>
  suspend "tail"
QED

Resume intcall_list_stage_origin_endpoint[tail]:
  `LENGTH vs' = LENGTH ds /\ LENGTH rs' = LENGTH ds /\
   LENGTH values' = LENGTH ds /\ LENGTH flags' = LENGTH ds` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`LENGTH (vv::vs') = _`, `LENGTH (r::rs') = _`,
       `LENGTH (v::values') = _`, `LENGTH (flag::flags') = _`] >>
     simp[NoAsms]) >>
  `(!i. i < LENGTH ds ==>
    post_value_type ce (EL i ds) = expr_type (EL i ds) /\
    vv_type (EL i vs') = expr_type (EL i ds) /\
    read_result fp.jc_cx (EL i rs') es = (INL (EL i values'),es) /\
    (EL i flags' ==> is_word_type (expr_type (EL i ds))) /\
    ?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv /\
      type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv (EL i values') /\
      (~EL i flags' ==> val_wf tv (EL i values')))` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH (h::ds) ==> _` (qspec_then `SUC i` mp_tac) >>
     simp[NoAsms, listTheory.EL, listTheory.LENGTH] >>
     disch_then irule >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  suspend "prefix"
QED

Resume intcall_list_stage_origin_endpoint[prefix]:
  `(!i tv'. i < LENGTH (tys ++ [expr_type h]) /\
    ~EL i (pflags ++ [flag]) /\
    evaluate_type (get_tenv fp.jc_cx) (EL i (tys ++ [expr_type h])) = SOME tv' ==>
    val_wf tv' (EL i (pvalues ++ [v])))` by
    (qpat_x_assum `!vs rs values flags a c out start tys pflags pvalues pops t. _` kall_tac >>
     `LENGTH pflags = LENGTH tys /\ LENGTH pvalues = LENGTH tys` by
       (qpat_x_assum `(^completed_prefix) _ _ a _ _ _ _ _` mp_tac >>
        BETA_TAC >> simp[NoAsms] >> metis_tac[]) >>
     rpt gen_tac >>
     Cases_on `i < LENGTH tys`
     >- (simp[NoAsms, listTheory.EL_APPEND_EQN] >>
         rpt strip_tac >> metis_tac[]) >>
     simp[NoAsms, listTheory.LENGTH_APPEND, listTheory.LENGTH] >>
     strip_tac >> `i = LENGTH tys` by decide_tac >>
     pop_assum SUBST_ALL_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`~EL (LENGTH tys) (pflags ++ [flag])`,
        `evaluate_type _ (EL (LENGTH tys) (tys ++ [expr_type h])) = _`,
        `LENGTH pflags = LENGTH tys`, `LENGTH pvalues = LENGTH tys`] >>
     simp[NoAsms, listTheory.EL_APPEND_EQN] >> rpt strip_tac >>
     `tv' = tv` by metis_tac[optionTheory.SOME_11] >>
     pop_assum SUBST_ALL_TAC >>
     qpat_x_assum `~flag ==> val_wf tv v` irule >> first_assum ACCEPT_TAC) >>
  `intcall_expr_res fp ce env es b mid /\ ~mid.vs_halted /\
   mid.vs_current_bb = b.cs_current_bb /\
   mid.vs_inst_idx = LENGTH b.cs_current_insts` by
    (qpat_assum `intcall_expr_cont fp ce env es a t es b mid` mp_tac >>
     simp[NoAsms, intcall_expr_cont_def] >> metis_tac[]) >>
  `start.cs_next_id <= b.cs_next_id` by
    (qpat_assum `ci_mono a b` mp_tac >> simp[NoAsms, ci_mono_def] >>
     rpt strip_tac >> decide_tac) >>
  qpat_assum `compile_stage_intcall_args ce vs' _ _ b = _`
    (fn eq => qpat_x_assum `!vs rs values flags a c out start tys pflags pvalues pops t. _`
      (fn ih => mp_then (Pat `compile_stage_intcall_args _ _ _ _ _ = _`) mp_tac ih eq)) >>
  disch_then drule_all >> strip_tac >>
  suspend "compose"
QED

Resume intcall_list_stage_origin_endpoint[compose]:
  `a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var` by
    (qpat_assum `ci_mono a b` mp_tac >> simp[NoAsms, ci_mono_def]) >>
  `intcall_expr_cont fp ce env es a t es c u` by
    (irule intcall_expr_cont_trans >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[NoAsms]) >>
  `b.cs_next_id <= c.cs_next_id` by
    (qpat_assum `ci_mono b c` mp_tac >> simp[NoAsms, ci_mono_def]) >>
  `!x. op = Var x ==> not_fresh_at b x` by
    (qpat_assum `(^completed_prefix) _ _ b _ _ _ _ mid` mp_tac >>
     BETA_TAC >> strip_tac >>
     `LENGTH pops = LENGTH tys` by
       (qpat_assum `LENGTH (pops ++ [op]) = _` mp_tac >> simp[NoAsms]) >>
     qpat_x_assum `!i. i < LENGTH (tys ++ [expr_type h]) ==> _`
       (qspec_then `LENGTH tys` mp_tac) >>
     simp[listTheory.EL_APPEND_EQN] >> metis_tac[]) >>
  `~flag ==> ^allocation_origin fp.jc_func start c op tv u` by
    (strip_tac >>
     `^allocation_origin fp.jc_func start b op tv mid` by
       (BETA_TAC >> first_x_assum irule >> simp[]) >>
     drule_all intcall_allocation_origin_frame >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `[op] ++ rest = out` (SUBST1_TAC o SYM) >>
      qpat_assum `LENGTH rest = LENGTH ds` mp_tac >> simp[NoAsms]) >>
  qexists_tac `u` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `[op] ++ rest = out` (SUBST1_TAC o SYM) >>
  qpat_x_assum `(^deferred_list) _ _ tail_ds tail_vs tail_rs c es u` mp_tac >>
  qpat_x_assum `(^completed_prefix) _ _ c _ _ _ _ u` mp_tac >>
  BETA_TAC >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND,
    listTheory.MAP, listTheory.LENGTH_APPEND, listTheory.LENGTH_MAP,
    listTheory.LENGTH, arithmeticTheory.ADD1] >>
  simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> ntac 3 (pop_assum mp_tac) >>
  qpat_assum `evaluate_type _ (expr_type h) = SOME tv` mp_tac >>
  qpat_assum `~flag ==> (^allocation_origin) _ _ c op tv u` mp_tac >>
  qpat_assum `!i tv. i < LENGTH ds /\ ~EL i flags' /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `i` >>
  gvs[] >> metis_tac[]
QED

Finalise intcall_list_stage_origin_endpoint

Theorem intcall_list_stage_endpoint:
  !ds vs rs values flags a c out start tys pflags pvalues pops t.
  compile_stage_intcall_args ce vs flags (MAP expr_type ds) a = (out,c) /\
  LENGTH vs = LENGTH ds /\ LENGTH rs = LENGTH ds /\
  LENGTH values = LENGTH ds /\ LENGTH flags = LENGTH ds /\
  ^deferred_list fp ce (ds ++ tail_ds) (vs ++ tail_vs) (rs ++ tail_rs) a es t /\
  ^completed_prefix fp.jc_cx start a tys pflags pvalues pops t /\
  (!i tv. i < LENGTH tys /\ ~EL i pflags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv ==>
    val_wf tv (EL i pvalues)) /\
  (!i. i < LENGTH ds ==>
    post_value_type ce (EL i ds) = expr_type (EL i ds) /\
    vv_type (EL i vs) = expr_type (EL i ds) /\
    read_result fp.jc_cx (EL i rs) es = (INL (EL i values),es) /\
    (EL i flags ==> is_word_type (expr_type (EL i ds))) /\
    ?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv /\
      type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv (EL i values) /\
      (~EL i flags ==> val_wf tv (EL i values))) /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es a t /\
  fn_has_code a c fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  start.cs_next_id <= a.cs_next_id /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  LENGTH out = LENGTH ds /\
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^deferred_list fp ce tail_ds tail_vs tail_rs c es u /\
    ^completed_prefix fp.jc_cx start c (tys ++ MAP expr_type ds)
      (pflags ++ flags) (pvalues ++ values) (pops ++ out) u
Proof
  rpt gen_tac >> strip_tac >> drule_all intcall_list_stage_origin_endpoint >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `u` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
