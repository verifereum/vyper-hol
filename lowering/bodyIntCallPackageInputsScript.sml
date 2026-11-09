(* Synchronized package resources, without compiler branch witnesses. *)
Theory bodyIntCallPackageInputs
Ancestors
  bodyIntCallSeamDefs bodyIntCallEntryInputs bodyIntCallInvokeEntry

Theorem intcall_entry_package_inputs:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys : string -> num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([] : expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) ==>
  label = lbl /\
  (has_rb <=> nret = 0 /\
    cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT) /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
  state_rel func ce cx (es1 with scopes := []) t /\
  internal_immutable_regions ce cx es1 t.vs_alloca_next /\
  internal_args_rel ce params penv (if has_rb then 1 else 0) argv
    t.vs_alloca_next t.vs_memory /\
  t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  alloca_room ctx callee setup /\ fmp_room ctx callee setup
Proof
  pure_rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_x_assum `_ /\ _ ==> st2 = _ /\ _` kall_tac >>
  qpat_x_assum `_ \/ _ ==> ?rbuf aid off. _` kall_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key trans view ctor imm_len' ss' rt. _`
    (mk_asm "package") >>
  gvs[] >> asm_x "package" drule >> disch_then drule >>
  disch_then assume_tac >> first_x_assum drule >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_entry_package_separation:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys : string -> num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([] : expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) ==>
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
              | SOME imms => get_source_immutables ce.ce_module imms) nm =
       SOME (tv,iv) ==>
     regions_disjoint io (type_memory_size tv)
       (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz) /\
  (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables ce.ce_module imms) nm =
       SOME (tv,iv) ==>
     regions_disjoint io (type_memory_size tv)
       (w2n (HD argv)) (type_memory_size rtv))
Proof
  pure_rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_x_assum `_ /\ _ ==> st2 = _ /\ _` kall_tac >>
  qpat_x_assum `_ \/ _ ==> ?rbuf aid off. _` kall_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key trans view ctor imm_len' ss' rt. _`
    (mk_asm "package") >>
  gvs[] >> asm_x "package" drule >> disch_then drule >>
  disch_then assume_tac >> first_x_assum drule >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_entry_caller_protection:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  (!aid off sz.
     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) ==>
     mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept cenv es0 s0 t /\
  (!n lo sz aid off asz.
     local_region cenv prev t n lo sz /\
     FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
     sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
     regions_disjoint lo sz off asz)
Proof
  pure_rewrite_tac[intcall_entry_def] >> strip_tac >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
