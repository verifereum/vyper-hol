(* Allocation charge available at an internal-call boundary. *)
Theory bodyPtrIntCallMargin
Ancestors exprLoweringProps relation finite_map pred_set list arithmetic words
  bodySim exprSimHyps compileEnv compileVyper loweringShapeProps bodyIntCallSeams

Theorem alloca_room_call_margin:
  !ctx func s finish margin callee.
    alloca_room ctx func s /\
    fn_directly_calls ctx func.fn_name callee /\
    finish <= s.vs_alloca_next /\ margin <= unit_alloca_frame ctx ==>
    finish + margin < dimword (:256)
Proof
  rpt strip_tac >> fs[alloca_room_def] >>
  `TC (fn_directly_calls ctx) func.fn_name callee` by
    metis_tac[TC_SUBSET] >>
  `0 < CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` by
    (spose_not_then assume_tac >>
     `CARD {g | TC (fn_directly_calls ctx) func.fn_name g} = 0` by decide_tac >>
     ` {g | TC (fn_directly_calls ctx) func.fn_name g} = {}` by
       metis_tac[CARD_EQ_0] >>
     fs[EXTENSION]) >>
  `unit_alloca_frame ctx <=
   CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
     unit_alloca_frame ctx` by
    (Cases_on `CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` >>
     fs[MULT_CLAUSES]) >>
  decide_tac
QED

(* Both runtime and deploy compilation check every internal declaration. *)
Theorem body_inv_internal_allocs_ok:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,ss)
Proof
  rpt strip_tac >>
  `MEM (mut,nr,rr,name,args,dflts,ret,ss)
     (FST (SND (classify_functions tops)))` by
    simp[MEM_classify_internal] >>
  gvs[body_inv_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
  Cases_on `cx.in_deploy` >> gvs[] >>
  metis_tac[lower_vyper_runtime_unit_allocs_ok,
            lower_vyper_deploy_unit_allocs_ok]
QED

(* The caller's coherent type metadata suffices; no callee ghost is needed
   to establish the size bound before invoking the body induction. *)
Theorem body_inv_internal_return_size:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  evaluate_type (get_tenv cx) ret = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  drule_all body_inv_internal_allocs_ok >>
  simp[fn_allocs_ok_def] >> strip_tac >>
  `type_memory_bytes cenv ret = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `cenv.ce_struct_fields =
   (build_compile_env tops Internal mut name args ret ss F).ce_struct_fields` by
    gvs[body_inv_def, build_compile_env_ce_struct_fields] >>
  drule type_memory_bytes_frame >> strip_tac >>
  gvs[] >> fs[dimword_def]
QED

(* Actual INVOKE arguments identify the entry's memory-return buffer.
   Capacity is the semantic return size, not the larger ALLOCA size. *)
Theorem intcall_entry_return_bounds:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (0,rbs,pvs) /\
  0 < rbs /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv ==>
  w2n (HD argv) + type_memory_size rtv < dimword (:256) /\
  type_memory_size rtv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  fs[intcall_entry_def] >>
  `type_memory_size rtv + 64 < dimword (:256)` by
    metis_tac[body_inv_internal_return_size] >>
  `t.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  gvs[] >> decide_tac
QED

(* Boundary producer inventory for the pointer-call composition:

   - In the has-return-buffer branch use
       SOME (HD argv, type_memory_size rtv)
     for d.  Its capacity equality is reflexive; intcall_entry_return_bounds
     supplies the two independent strict inequalities.  The has_rb test
     and the association of argv with the actual INVOKE are supplied by
     intcall_entry_def.  No equality with rbuf.buf_size is required.

   - No-DALLOCA is already a caller premise of expr_sim_ptr_def and
     expr_vv_sim_ptr_def, and is a property of the unchanged ctx, not a
     property to infer from intret_ptr_q.

   - bodySimEntry's body_inv_build_internal_env transfers the caller's
     body_inv to the rebuilt internal environment;
     compile_internal_prologue_body_inv transfers it through parameter
     materialization.  The callee context's stack update leaves body_inv
     unchanged (its cx observations are get_module_code NONE, in_deploy,
     and get_tenv).  The actual-entry proof must also produce expr_sim_inv,
     typing, and ghost_inv; these are not consequences of the size lemma.

   - internal_args_rel_def supplies pairwise separation of memory
     parameters and their ends below the caller frontier.  It does NOT
     supply their separation from caller locals/old sites, or their ghost
     provenance.  Those are concrete staging obligations: the F branch of
     compile_stage_intcall_args_def always copies to compile_alloc_buffer
     (MAX 32 mem_size).  alloca_step_live_local_separated_ptr and
     emit_alloca_endpoint_ptr (assignTuplePtrAllocEndpoint) provide the
     local-separation interface, including reused sites.  intcall_entry_def
     also identifies the fresh return-buffer site and its ALLOCA id.
     The staging proof must retain the fresh site witnesses and old-site
     separation for the confinement proof; S1's intcall_entry alone is
     not a pointer-entry contract.

   - The confinement proof must preserve BOTH memory and t_mem membership
     on protected caller bytes.  Neither internal_args_rel nor RetQ
     promises that frame; intret_ptr_q only gives the return's semantic
     and storage-taint facts.  Concrete staging and confinement therefore
     remain separate obligations, not assumptions discharged here.
*)
