(* Finite safe runs obtained from whole-registration ownership and an actual STOP. *)
Theory entryRegistrationObserver
Ancestors
  calldataRegistrationExec calldataRegistrationLocals entryDecoderObserver
  entryStopObserverConstruction abiEncoderObserver memSafeRun

Theorem registration_observer_owned_stop:
  compile_register_positional_args ce (build_positional_args ce args) off st = (cef,final) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) (ty',tv).
    ty = ty' /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tys /\
  fn_has_code st final observer /\
  alloca_inv initial /\ alloca_frontier_inv ctx observer site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts observer)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!id. st.cs_next_id <= id /\ id < final.cs_next_id ==>
    FLOOKUP initial.vs_allocas id = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb observer.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  observer = entry_stop_function final.cs_current_bb (LENGTH final.cs_current_insts) iid fn /\
  lookup_block final.cs_current_bb fn.fn_blocks = SOME bb /\
  LENGTH final.cs_current_insts <= LENGTH bb.bb_instructions ==>
  (?fuel z. run_from fuel ctx observer initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx observer initial) \/
  ?v outputs fp fuel.
    ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\
    LIST_REL (\((name,ty),tv) (x,dst,p,id).
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
      FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      eval_operand dst v = SOME (n2w p) /\
      abi_decoder_operand_live final.cs_next_var dst /\
      st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
      p+type_memory_size tv < dimword (:256) /\
      (?vname ins. dst = Var vname /\ MEM ins (fn_insts observer) /\
        ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
        ins.inst_id = id)) (ZIP (args,MAP SND tys)) outputs /\
    alloca_inv v /\ alloca_frontier_inv ctx observer site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame fp initial v /\
    (!q k. MEM (q,k) fp ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!tenv. LIST_REL (\(name,ty) (ty',tv). evaluate_type tenv ty = SOME tv) args tys ==>
      ?scope. bind_arguments tenv args (MAP (\(x,dst,p,id). x) outputs) = SOME scope) /\
    run_from fuel ctx observer initial = Halt (stop_view v) /\
    mem_safe_run fuel ctx observer initial
Proof
  strip_tac >> drule_all registration_positional_owned_provenance >>
  strip_tac >- metis_tac[] >>
  `lookup_block v.vs_current_bb observer.fn_blocks =
      SOME (entry_stop_block (LENGTH final.cs_current_insts) iid bb) /\
    get_instruction (entry_stop_block (LENGTH final.cs_current_insts) iid bb)
      v.vs_inst_idx = SOME (mk_inst iid STOP [] [])` by
    metis_tac[entry_stop_function_cut] >>
  `run_from 0 ctx observer v = Halt (stop_view v)` by
    metis_tac[run_from_stop_view] >>
  `mem_safe_run 0 ctx observer v` by
    metis_tac[decoder_observer_stop_safe] >>
  qpat_x_assum `!fuel r. _` (qspecl_then [`0`, `Halt (stop_view v)`] mp_tac) >>
  simp[] >> strip_tac >> disj2_tac >>
  qexistsl_tac [`v`, `outputs`, `fp`, `fuel'`] >> gvs[] >> conj_tac
  >- (qpat_x_assum `!id. _ \/ _ ==> _` MATCH_ACCEPT_TAC) >>
  rpt strip_tac >>
  `LIST_REL (\((name,ty),tv) (x,dst,p,id). value_has_type tv x)
     (ZIP (args,MAP SND tys)) outputs` by
    (irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
     simp[pairTheory.FORALL_PROD]) >>
  drule_all decoded_arguments_bind_typed >> simp[]
QED
