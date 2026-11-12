(* Same-run void-mode staging, before INVOKE. *)
Theory bodyIntCallFamCallIntEntryVoidEndpoint
Ancestors
  bodyIntCallFamCallIntEntryHeadStage bodyIntCallFamCallIntEntryModes
  bodyIntCallJointContract exprLoweringProps

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\ w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\ !i. i < LENGTH tys ==>
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
val staged_regions = ``\cx ds flags ops s.
  !i j ti tj w z. i < j /\ j < LENGTH ds /\ ~EL i flags /\ ~EL j flags /\
    evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME ti /\
    evaluate_type (get_tenv cx) (expr_type (EL j ds)) = SOME tj /\
    eval_operand (EL i ops) s = SOME w /\ eval_operand (EL j ops) s = SOME z ==>
    regions_disjoint (w2n w) (type_memory_size ti) (w2n z) (type_memory_size tj)``;
val allocation_origin = ``\func start bound op tv s.
  ?aid len inst w. eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ start.cs_next_id <= aid /\ aid < bound.cs_next_id /\
    type_memory_size tv <= len``;

Theorem intcall_void_staged_endpoint:
  compile_call compile_expr ce ret_ty ty (IntCall fid) ds dflt sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,flags) /\
  ce.ce_func_return_type (nsid_to_string fid) = NoneT /\
  compile_multi_vvs compile_expr ce ds sa = (vs,a) /\
  LENGTH vs = LENGTH ds /\ LENGTH rs = LENGTH ds /\
  LENGTH values = LENGTH ds /\ LENGTH flags = LENGTH ds /\
  ^deferred_list fp ce ds vs rs a es t /\
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
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u ops c x argv.
    compile_stage_intcall_args ce vs flags (MAP expr_type ds) a = (ops,c) /\
    emit_void INVOKE
      (Label (internal_fn_label (ce.ce_func_ids (nsid_to_string fid))
        (nsid_to_string fid) (ce.ce_func_param_types (nsid_to_string fid))
        ce.ce_is_ctor) :: ops) c = (x,sb) /\
    vv = StackValue NoneT (Lit 0w) /\
    fn_has_code sa a fp.jc_func /\ fn_has_code a c fp.jc_func /\
    fn_has_code c sb fp.jc_func /\
    gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^staged_regions fp.jc_cx ds flags ops u /\
    ^completed_prefix fp.jc_cx sa c (MAP expr_type ds) flags values ops u /\
    (!i tv. i < LENGTH ds /\ ~EL i flags /\
      evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv ==>
      ^allocation_origin fp.jc_func sa sb (EL i ops) tv u) /\
    eval_operands ops u = SOME argv /\ LENGTH argv = LENGTH ds /\
    (!i w. i < LENGTH ds /\ eval_operand (EL i ops) u = SOME w ==>
      EL i argv = w)
Proof
  strip_tac >> drule_all intcall_void_mode_code >> strip_tac >> gvs[] >>
  `ci_mono sa a` by
    (`a = SND (compile_multi_vvs compile_expr ce ds sa)` by simp[] >>
     pop_assum SUBST1_TAC >> irule ci_mono_compile_multi_vvs >>
     simp[compile_expr_ci_mono]) >>
  `sa.cs_next_id <= a.cs_next_id` by fs[ci_mono_def] >>
  mp_tac (Q.INST [`tail_ds` |-> `[]`, `tail_vs` |-> `[]`,
    `tail_rs` |-> `[]`, `start` |-> `sa`, `tys` |-> `[]`,
    `pflags` |-> `[]`, `pvalues` |-> `[]`, `pops` |-> `[]`, `out` |-> `ops`]
    (SPEC_ALL intcall_list_stage_fresh_origin_endpoint)) >>
  simp[] >> strip_tac >>
  `^completed_prefix fp.jc_cx sa c (MAP expr_type ds) flags values ops u`
    by simp[] >>
  drule intcall_completed_operands >> strip_tac >>
  qexistsl_tac [`u`,`argv`] >> simp[] >>
  conj_tac >- (qpat_assum `!i j ti tj w z. _` ACCEPT_TAC) >>
  `c.cs_next_id <= sb.cs_next_id` by
    (qmatch_asmsub_abbrev_tac `emit_void INVOKE iops c` >>
     mp_tac (Q.SPECL [`INVOKE`,`iops`,`c`] ci_mono_emit_void) >>
     simp[ci_mono_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!i tv. _` drule_all >> strip_tac >>
  qexistsl_tac [`len`,`inst`,`w`] >> simp[]
QED
