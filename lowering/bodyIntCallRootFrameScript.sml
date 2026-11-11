(* Root-frame boundaries: staging means the exact parameter span, not
   its containing caller allocation (which could also contain the buffer). *)
Theory bodyIntCallRootFrame
Ancestors
  bodyIntCallJointContract bodySim bodyIntCallPrologueInit bodyIntCallParameterGeometry
  bodyIntCallSemanticEntry bodyIntCallResourceSpans

Theorem internal_parameter_windows_protected:
  (!b z. staged b z <=>
    ?i po. i < LENGTH params /\ ~SND (EL i params) /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
      b = w2n (EL ((argbase:num) + i) (argv:bytes32 list))) /\
  (!i po z. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) ==>
    ?aid off asz. FLOOKUP caller.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m /\ off <= w2n (EL ((argbase:num) + i) (argv:bytes32 list)) /\
      w2n (EL ((argbase:num) + i) (argv:bytes32 list)) + z <= off + asz) /\
  (!a k aid off asz. P a k /\
    FLOOKUP caller.vs_allocas aid = SOME (off,asz) /\
    n <= aid /\ aid < m ==> regions_disjoint a k off asz) ==>
  !b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b z. staged b z <=> _` (fn th => fs[th]) >>
  qpat_x_assum `!i po z. _ ==> ?aid off asz. _` drule_all >>
  strip_tac >> rpt strip_tac >>
  irule protected_span_subregion >>
  qexistsl_tac [`P`,`off`,`asz`] >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem internal_parameter_windows_buffer:
  (!b z. staged b z <=>
    ?i po. i < LENGTH params /\ ~SND (EL i params) /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
      b = w2n (EL ((argbase:num) + i) (argv:bytes32 list))) /\
  (!i po z. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) ==>
    regions_disjoint rb cap (w2n (EL ((argbase:num) + i) (argv:bytes32 list))) z) ==>
  !b z. staged b z ==> regions_disjoint rb cap b z
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b z. staged b z <=> _` (fn th => fs[th]) >>
  metis_tac[]
QED

Theorem internal_prologue_module_pins:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  cenv_module_pins tops ce ==>
  cenv_module_pins tops (ce2 with ce_alloca_locals := T)
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compileEnvTheory.compile_env_component_equality] >> strip_tac >>
  fs[cenv_module_pins_def]
QED

Theorem internal_prologue_return_pc:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) ==>
  ce2.ce_return_pc = SOME (PtrVar rpc 0)
Proof
  strip_tac >> drule intCallCalleeTheory.internal_prologue_stages >>
  strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >>
  strip_tac >> gvs[]
QED

Theorem internal_prologue_no_return_buffer:
  compile_internal_prologue ce params F rt st0 = ((ce2,rpc),st1) ==>
  ce2.ce_return_buf = ce.ce_return_buf
Proof
  strip_tac >> drule intCallCalleeTheory.internal_prologue_stages >>
  strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >>
  strip_tac >> gvs[compileEnvTheory.comp_return_def]
QED

(* Choose only operands actually defined by the prologue.  In the current
   internal-function compiler ce_imm_alloca is NONE, also in deploy mode. *)
Theorem internal_root_reserved_operands:
  (?x. rpc = Var x /\ not_fresh_at st x /\
       lookup_var x landing = SOME pc) /\
  (has_rb ==> ?x sz w.
    ce.ce_return_buf = SOME (PtrVar (Var x) sz) /\
    not_fresh_at st x /\ lookup_var x landing = SOME w) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\ ce.ce_imm_alloca = NONE ==>
  ?reserved.
    (!op. reserved op <=> op = rpc \/
      ?sz. ce.ce_return_buf = SOME (PtrVar op sz)) /\
    reserved rpc /\
    (!op sz. ce.ce_return_buf = SOME (PtrVar op sz) ==> reserved op) /\
    (!op. ce.ce_imm_alloca = SOME op ==> reserved op) /\
    (!op. reserved op ==>
      ?x w. op = Var x /\ lookup_var x landing = SOME w) /\
    (!op x. reserved op /\ op = Var x ==> not_fresh_at st x)
Proof
  strip_tac >>
  qexists_tac `\op. op = rpc \/ ?sz. ce.ce_return_buf = SOME (PtrVar op sz)` >>
  simp[] >> Cases_on `has_rb` >> gvs[] >> metis_tac[]
QED

Theorem internal_root_frame_exists:
  supported_program tops /\
  cxf.stk = owner::ancestors /\
  call_stack_follows (call_edge_rel edges) cxf.stk /\
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cxf /\
  evaluate_type (get_tenv cxf) ret = SOME rtv /\
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  cenv_module_pins tops ce /\ ce.ce_imm_alloca = NONE /\
  ce.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) ret /\
  (has_rb <=> ce.ce_returns_count = 0 /\ ret <> NoneT) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  (has_rb ==> ?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
  (?x. rpc = Var x /\ not_fresh_at st1 x /\ lookup_var x u = SOME pc) /\
  (has_rb ==> ?x. not_fresh_at st1 x /\ lookup_var x u = SOME (HD argv) /\
    !off sz. ce.ce_return_buf = SOME (MemLoc off sz) ==>
      ce2.ce_return_buf = SOME (PtrVar (Var x) sz)) /\
  (!i po z. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) ==>
    ?aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m /\
      off <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
      w2n (EL ((if has_rb then 1 else 0) + i) argv) + z <= off + asz) /\
  (has_rb ==>
    w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next /\
    ?aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m /\ off <= w2n (HD argv) /\
      w2n (HD argv) + type_memory_size rtv <= off + asz) /\
  (has_rb ==> !i po z.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) ==>
    regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
      (w2n (EL (1 + i) argv)) z) ==>
  ?fp. intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = cxf /\ fp.jc_owner = owner /\ fp.jc_ancestors = ancestors /\
    fp.jc_edges = edges /\ fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = t.vs_alloca_next /\ fp.jc_morig = t /\ fp.jc_oorig = u /\
    fp.jc_root_ce = (ce2 with ce_alloca_locals := T) /\
    fp.jc_rpc = rpc /\ fp.jc_pc = pc /\
    fp.jc_rb = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
    fp.jc_prot = (\a k. a + k <= t.vs_alloca_next /\
      !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
        n <= aid /\ aid < m ==> regions_disjoint a k off asz) /\
    fp.jc_staged = (\b z. ?i po.
      i < LENGTH params /\ ~SND (EL i params) /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
      b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) /\
    fp.jc_reserved = (\op. op = rpc \/
      ?sz. ce2.ce_return_buf = SOME (PtrVar op sz)) /\
    (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at st1 x)
Proof
  strip_tac >>
  drule compile_internal_prologue_fields >>
  simp[compileEnvTheory.compile_env_component_equality] >> strip_tac >>
  drule_all internal_prologue_module_pins >> strip_tac >>
  drule internal_prologue_return_pc >> strip_tac >>
  `~has_rb ==> ce2.ce_return_buf = NONE` by
    (strip_tac >> gvs[] >> drule internal_prologue_no_return_buffer >> simp[]) >>
  `has_rb ==> ?x sz w. ce2.ce_return_buf = SOME (PtrVar (Var x) sz) /\
    not_fresh_at st1 x /\ lookup_var x u = SOME w` by metis_tac[] >>
  mp_tac (Q.INST [`ce` |-> `ce2`, `st` |-> `st1`, `landing` |-> `u`]
    (SPEC_ALL internal_root_reserved_operands)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexists_tac `<| jc_tops := tops; jc_ctx := ctx; jc_func := callee;
    jc_cx := cxf; jc_edges := edges; jc_owner := owner;
    jc_ancestors := ancestors; jc_lo := t.vs_alloca_next;
    jc_staged := (\b z. ?i po. i < LENGTH params /\ ~SND (EL i params) /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
      b = w2n (EL ((if has_rb then 1 else 0) + i) argv));
    jc_prot := (\a k. a + k <= t.vs_alloca_next /\
      !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
        n <= aid /\ aid < m ==> regions_disjoint a k off asz);
    jc_morig := t; jc_oorig := u;
    jc_root_ce := ce2 with ce_alloca_locals := T;
    jc_ret_ty := ret; jc_ret_tv := rtv; jc_rpc := rpc; jc_pc := pc;
    jc_rb := (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE);
    jc_reserved := reserved |>` >>
  `reserved = (\op. op = rpc \/ ?sz. ce2.ce_return_buf = SOME (PtrVar op sz))`
    by simp[FUN_EQ_THM] >>
  simp[IgnAsm `has_rb <=> _`] >>
  simp[intcall_frame_ok_def, IgnAsm `has_rb <=> _`] >> suspend "frame"
QED

Resume internal_root_frame_exists[frame]:
  rpt conj_tac
  >~ [`call_stack_follows _ (owner::ancestors)`]
  >- (qpat_assum `cxf.stk = _` (fn th => rewrite_tac[GSYM th]) >> simp[])
  >~ [`eval_operand _ _ = _`] >- simp[venomStateTheory.eval_operand_def]
  >~ [`!id. supported_struct_fields tops id <> SOME []`]
  >- metis_tac[supported_program_struct_fields_nonempty]
  >- (Cases_on `has_rb` >> fs[] >> rpt strip_tac >>
      qpat_x_assum `!i po z. _ ==> ?aid off asz. _` drule_all >>
      strip_tac >> qpat_x_assum `!aid off asz. _` drule_all >>
      gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
  >> simp[] >> Cases_on `has_rb` >> gvs[] >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!i po z. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
QED

Finalise internal_root_frame_exists
