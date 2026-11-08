(* Root-frame boundaries: staging means the exact parameter span, not
   its containing caller allocation (which could also contain the buffer). *)
Theory bodyIntCallRootFrame
Ancestors
  bodyIntCallJointContract bodyIntCallPrologueInit bodyIntCallParameterGeometry
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
