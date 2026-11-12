(* Argument relations for an arbitrary targeted package, independent of mode. *)
Theory bodyIntCallFamCallIntEntryPackageArgs
Ancestors
  bodyIntCallFamCallIntEntryIntroduce bodyIntCallFamCallIntEntryHeadStage
  bodyIntCallFamCallIntEntryPackage

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
val staged_regions = ``\cx ds flags ops s.
  !i j ti tj w z. i < j /\ j < LENGTH ds /\ ~EL i flags /\ ~EL j flags /\
    evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME ti /\
    evaluate_type (get_tenv cx) (expr_type (EL j ds)) = SOME tj /\
    eval_operand (EL i ops) s = SOME w /\ eval_operand (EL j ops) s = SOME z ==>
    regions_disjoint (w2n w) (type_memory_size ti) (w2n z) (type_memory_size tj)``;
val allocation_origin = ``\func start bound op tv s.
  ?aid len inst w.
    eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ start.cs_next_id <= aid /\ aid < bound.cs_next_id /\
    type_memory_size tv <= len``;

Theorem intcall_targeted_staged_arguments:
  set_internal_package_target target
    (package_internal_fn tops tr keys ctor imm
      (mut,F,rr,name,args,([]:expr list),ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,nkey,use_tr,is_view,is_ctor,ilen,ss',rt) /\
  ALL_DISTINCT (MAP FST args) /\ MAP expr_type ds = MAP SND args /\
  params = ZIP (MAP FST args,flags) /\
  bind_arguments (get_tenv cx) args values = SOME penv /\
  ^completed_prefix cx start current (MAP expr_type ds) flags values out u /\
  ^staged_regions cx ds flags out u /\
  (if has_rb then 1 else 0) + LENGTH args <= LENGTH (argv:bytes32 list) /\
  LENGTH argv < dimword (:256) /\
  (!i w. i < LENGTH ds /\ eval_operand (EL i out) u = SOME w ==>
    EL ((if has_rb then 1 else 0)+i) argv = w) /\
  (!i tv. i < LENGTH args /\
    evaluate_type (get_tenv cx) (SND (EL i args)) = SOME tv ==>
    type_memory_bytes ce (SND (EL i args)) = type_memory_size tv) /\
  (!i tv. i < LENGTH ds /\ ~EL i flags /\
    evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME tv ==>
    ^allocation_origin func start current (EL i out) tv u) ==>
  internal_args_rel ce params penv (if has_rb then 1 else 0) argv
    u.vs_alloca_next u.vs_memory /\
  (!i po psz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    ?aid off len. FLOOKUP u.vs_allocas aid = SOME (off,len) /\
      (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid) /\
      start.cs_next_id <= aid /\ aid < current.cs_next_id /\
      off <= w2n (EL ((if has_rb then 1 else 0)+i) argv) /\
      w2n (EL ((if has_rb then 1 else 0)+i) argv) + psz <= off+len)
Proof
  strip_tac >> drule_all intcall_targeted_parameter_metadata >> strip_tac >>
  `!i tv. i < LENGTH args /\
    evaluate_type (get_tenv cx) (SND (EL i args)) = SOME tv ==>
    ?off. FLOOKUP ce.ce_vars (FST (EL i args)) =
      SOME (MemLoc off (type_memory_size tv))` by
    (rpt strip_tac >>
     qpat_assum `EVERY _ args`
       (mp_tac o REWRITE_RULE [listTheory.EVERY_EL]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `params = ZIP (MAP FST args,flags)` SUBST1_TAC >>
      irule (BETA_RULE intcall_staged_bound_arguments) >>
      simp[] >> qexistsl_tac [`current`,`cx`,`ds`,`out`,`start`,`values`] >>
      fs[arithmeticTheory.ADD_COMM] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH ds = LENGTH args` by
    (qpat_assum `MAP expr_type ds = MAP SND args`
      (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `!i tv. i < LENGTH ds /\ ~EL i flags /\
    evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME tv ==>
    type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
    ^allocation_origin func start current (EL i out) tv u` by
    (rpt strip_tac >>
     `expr_type (EL i ds) = SND (EL i args)` by
       (qpat_assum `MAP expr_type ds = MAP SND args`
         (mp_tac o Q.AP_TERM `EL i`) >> simp[listTheory.EL_MAP]) >>
     gvs[]) >>
  rpt gen_tac >> strip_tac >>
  irule intcall_staged_parameter_provenance >>
  qexistsl_tac [`args`,`ce`,`cx`,`ds`,`flags`,`out`,`params`,`po`,`values`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_parameter_immutable_separation:
  immutable_alloca_sep func ce cx es u /\
  (!i po psz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    ?aid off len. FLOOKUP u.vs_allocas aid = SOME (off,len) /\
      (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid) /\
      off <= w2n (EL ((argbase:num)+i) (argv:bytes32 list)) /\
      w2n (EL ((argbase:num)+i) (argv:bytes32 list)) + psz <= off+len) ==>
  (ce.ce_is_ctor ==> !i po psz nm tv iv io.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms) nm =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n (EL ((argbase:num)+i) (argv:bytes32 list))) psz)
Proof
  strip_tac >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`,`po`,`psz`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[] >> irule intcall_alloca_subregion_immutable_sep >>
  simp[] >> goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
  simp[] >> qexistsl_tac [`nm`,`iv`] >> simp[]
QED

Theorem intcall_parameter_buffer_separation:
  alloca_inv u /\ FLOOKUP u.vs_allocas bid = SOME (b,sz) /\
  b <= w2n rb /\ w2n rb + n <= b+sz /\
  (!i po psz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    ?aid off len. FLOOKUP u.vs_allocas aid = SOME (off,len) /\
      bid < aid /\ off <= w2n (EL ((argbase:num)+i) (argv:bytes32 list)) /\
      w2n (EL ((argbase:num)+i) (argv:bytes32 list)) + psz <= off+len) ==>
  !i po psz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    regions_disjoint (w2n rb) n (w2n (EL ((argbase:num)+i) (argv:bytes32 list))) psz
Proof
  strip_tac >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`,`po`,`psz`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule intcall_alloca_subregions_disjoint >>
  qexistsl_tac [`b`,`bid`,`len`,`aid`,`off`,`u`,`sz`] >> simp[]
QED
