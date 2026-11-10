(* TEMPORARY OWNER-SPLIT STATEMENT: parse-checked only, not proved.
   Historical obligation C1.5.3.2. This is the complete universal package
   conjunct of intcall_entry (not an alternate definition of that relation).
   Inputs are single-endpoint staging descriptors, their separation, the
   source binding, and a preceding return ALLOCA. Module pins are explicit
   equalities to avoid an ancestor cycle through bodyIntCallSeams.
   No resource conclusion is assumed: the unit-charge leaves must supply it. *)
Theory bodyIntCallPackageEntryInterface
Ancestors
  bodyIntCallUnitCharge bodyIntCallStageEntryMemory bodyIntCallStagePackage
  bodyIntCallPackageGlobals bodyIntCallPackageLayout bodyIntCallMetadata
  bodySim exprSimHypsDefs exprSimHyps exprLoweringProps intCallCallee
  compileVyper compileEnv context vyperInterpreter vyperState vyperAST
  venomExecSemantics venomState venomInst list words finite_map

Theorem intcall_package_entry:
  !tops ctx func caller cx tenv name args ret ss mut rr es1 prev penv rtv
   sa sb st2 st3 D vals ws argv rbw rc rbs pvs lbl t.
    body_inv tops ctx caller cx /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    caller.ce_module = NONE /\
    caller.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    caller.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    lbl = internal_fn_label (caller.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (caller.ce_func_param_types (nsid_to_string (NONE,name))) caller.ce_is_ctor /\
    fn_directly_calls ctx func.fn_name lbl /\
    stmt_state_rel ctx func caller cx (es1 with scopes := prev) t /\
    expr_sim_inv caller cx tenv (es1 with scopes := prev) /\
    bind_arguments (get_tenv cx) args vals = SOME penv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    EVERY (staged_arg caller func (es1 with scopes := prev) st2 st3 t) D /\
    MAP (\(ty,tv,v,flag,op). ty) D = MAP SND args /\
    MAP (\(ty,tv,v,flag,op). v) D = vals /\
    MAP (\(ty,tv,v,flag,op). flag) D = pvs /\
    EVERY (\(ty,tv,v,flag,op).
      evaluate_type (get_tenv cx) ty = SOME tv /\
      (flag ==> is_word_type ty)) D /\
    eval_operands (MAP (\(ty,tv,v,flag,op). op) D) t = SOME ws /\
    (!i j. i < LENGTH D /\ j < LENGTH D /\ i <> j ==>
      (\(ty,tv,v,flag,op) (ty',tv',v',flag',op').
        ~flag /\ ~flag' ==>
        !w w'. eval_operand op t = SOME w /\ eval_operand op' t = SOME w' ==>
        regions_disjoint (w2n w) (type_memory_size tv)
          (w2n w') (type_memory_size tv')) (EL i D) (EL j D)) /\
    argv = (if rc = 0 /\ ret <> NoneT then [rbw] else []) ++ ws /\
    LENGTH argv < dimword (:256) /\
    sa.cs_next_id <= st2.cs_next_id /\ st3.cs_next_id <= sb.cs_next_id /\
    (rc = 0 /\ ret <> NoneT ==>
      ?rid off cap inst.
        FLOOKUP t.vs_allocas rid = SOME (off,cap) /\
        rid < st2.cs_next_id /\ rbw = n2w off /\ off < dimword (:256) /\
        type_memory_size rtv <= cap /\
        MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = rid) ==>
    !callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key
     trans view ctor imm_len' ss' rt.
      lookup_function lbl ctx.ctx_functions = SOME callee /\
      setup_callee callee argv t = SOME setup /\
      set_internal_package_target caller.ce_target
        (package_internal_fn tops use_trans (nkeys : string -> num)
          caller.ce_is_ctor imm_len
          (mut,F,rr,name,args,([] : expr list),ret,ss)) =
        (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
      lbl' = lbl /\
      (has_rb <=>
        rc = 0 /\ caller.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT) /\
      (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
      state_rel func ce cx (es1 with scopes := []) t /\
      internal_immutable_regions ce cx es1 t.vs_alloca_next /\
      internal_args_rel ce params penv (if has_rb then 1 else 0) argv
        t.vs_alloca_next t.vs_memory /\
      (!i po psz.
        i < LENGTH params /\ ~SND (EL i params) /\
        FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
        ?aid off asz.
          FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
          (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
            inst.inst_id = aid) /\
          sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          off <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
          w2n (EL ((if has_rb then 1 else 0) + i) argv) + psz <= off + asz) /\
      (has_rb ==> !i po psz.
        i < LENGTH params /\ ~SND (EL i params) /\
        FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
        regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
          (w2n (EL (1 + i) argv)) psz) /\
      (ce.ce_is_ctor ==> !i po psz nm tv iv io.
        i < LENGTH params /\ ~SND (EL i params) /\
        FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
        FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
        FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
          NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) nm = SOME (tv,iv) ==>
        regions_disjoint io (type_memory_size tv)
          (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz) /\
      (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
        FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
        FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
          NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) nm = SOME (tv,iv) ==>
        regions_disjoint io (type_memory_size tv)
          (w2n (HD argv)) (type_memory_size rtv)) /\
      t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
      alloca_room ctx callee setup /\ fmp_room ctx callee setup
Proof
  cheat
QED
