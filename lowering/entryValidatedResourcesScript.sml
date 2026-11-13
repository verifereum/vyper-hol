(* Initial allocation resources from the runtime validator. *)
Theory entryValidatedResources
Ancestors
  entryInitialResources vyperLoweringCorrect allocaHistory fcgPostorder
  fcgCorrectnessProof venomMemProofs vyperCompiler venomWf venomInst
  fcgDefs list exprLoweringProps

Theorem validated_entry_alloca_room:
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME func /\
  s.vs_alloca_next = 0 ==>
  alloca_room ctx func s
Proof
  strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  `ctx_wf ctx` by
    (simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, MEM_MAP] >>
     metis_tac[lookup_function_MEM, lookup_function_result_name]) >>
  `func.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `fcg_is_reachable (fcg_analyze ctx) name` by
    (irule fcg_analyze_reachable_complete_proof >>
     simp[fcg_path_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_mem]) >>
  irule initial_alloca_room >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable (fcg_analyze ctx) g` by
        metis_tac[reachable_fcg_acyclic_tc_rank] >>
      metis_tac[reachable_fcg_acyclic_no_reachable_cycle]) >>
  metis_tac[lowering_context_ok_alloca_budget]
QED

Theorem runtime_initial_entry_resources:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func ==>
  let s = vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                    vs_inst_idx := 0 |> in
    alloca_room unit.cu_context func s /\ alloca_inv s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\
    (!cenv cx es. ~cenv.ce_is_ctor ==>
      immutable_alloca_sep func cenv cx es s) /\
    (!inst n base sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n)
Proof
  strip_tac >> simp_tac std_ss [LET_THM] >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >> gvs[] >>
  `vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0 /\ ~vs.vs_halted` by
    gvs[initial_venom_state_rel_def] >>
  conj_tac
  >- (irule validated_entry_alloca_room >> simp[] >> metis_tac[]) >>
  simp[alloca_inv_empty_proof, alloca_history_empty, immutable_alloca_sep_def,
       immutable_decl_sep_def]
QED
