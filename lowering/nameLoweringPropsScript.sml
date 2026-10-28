(* TOP-LEVEL: compile_name_correct covers typed word and aggregate names.
   The compiler's MemLoc and allocation-backed PtrVar bindings supply memory
   representations. Name loads preserve payload memory and earlier operands. *)
Theory nameLoweringProps
Ancestors
  exprLoweringProps exprLowering context compileEnv valueLoadProps
  valueEncodingProps eventTopicProps eventTopicExecProps localPtrsProps
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperTyping
  venomState venomExecSemantics

Theorem unwrap_memory_value_eq:
  !cenv ann ptr cs.
    unwrap_value cenv (LocatedValue ann (mk_ptr ptr LocMemory)) cs =
    if is_word_type ann then emit_op MLOAD [ptr] cs else (ptr,cs)
Proof
  rpt gen_tac >> Cases_on `is_word_type ann` >>
  simp[unwrap_value_def, mk_ptr_def, compile_ptr_load_def, comp_return_def]
QED

Theorem unwrap_memory_value_correct:
  !tenv cenv ann tv v ptr cs op cs' ss addr.
    evaluate_type tenv ann = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n addr) ss.vs_memory /\
    eval_operand ptr ss = SOME addr /\ fresh_vars_wrt cs ss /\
    unwrap_value cenv (LocatedValue ann (mk_ptr ptr LocMemory)) cs = (op,cs') ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      lowered_value_rel ann tv v op out /\ same_blocks cs cs' /\
      fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ann`
  >- (fs[unwrap_memory_value_eq] >>
      `mload (w2n addr) ss = typed_val_to_w256 tv v` by
        (rewrite_tac[GSYM mem_word_at_eq_mload] >>
         irule memory_value_rel_word >> simp[] >>
         qexistsl_tac [`tenv`, `ann`] >> simp[]) >>
      drule_all emit_op_MLOAD_frame >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
      qexists_tac `final` >> simp[lowered_value_rel_def]) >>
  gvs[unwrap_memory_value_eq] >> qexists_tac `ss` >>
  simp[emitted_insts_def, run_inst_seq_def, same_blocks_def, lowered_value_rel_def]
QED

Theorem local_ptrs_rel_value:
  !func cenv scopes ss id entry p region_size.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes id scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) ==>
    ?w. eval_operand (Var p) ss = SOME w /\
      memory_value_rel entry.type entry.value (w2n w) ss.vs_memory /\
      local_backed func p ss (w2n w) region_size /\
      w2n w + region_size <= ss.vs_alloca_next /\
      type_memory_size entry.type <= region_size /\ val_wf entry.type entry.value
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`id`, `entry`, `p`, `region_size`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >> goal_assum drule >> simp[]
QED

Theorem lower_value_name_memloc_correct:
  !tenv cenv scopes ty ann id entry offset region_size ss cs op cs'.
    vars_rel cenv scopes ss /\ lookup_scopes id scopes = SOME entry /\
    evaluate_type tenv ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (MemLoc offset region_size) /\
    offset < dimword(:256) /\ fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      lowered_value_rel ann entry.type entry.value op out /\ same_blocks cs cs' /\
      fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  `memory_value_rel entry.type entry.value offset ss.vs_memory` by
    (drule_all vars_rel_memloc_value >> simp[]) >>
  `unwrap_value cenv (LocatedValue ann (mk_ptr (Lit (n2w offset)) LocMemory)) cs =
      (op,cs')` by
    (mp_tac (Q.SPECL [`cenv`, `id`, `offset`, `region_size`, `ty`, `ann`, `cs`]
       lower_value_name_memloc) >> simp[] >> strip_tac >>
     gvs[unwrap_memory_value_eq]) >>
  qspecl_then [`tenv`, `cenv`, `ann`, `entry.type`, `entry.value`,
    `Lit (n2w offset)`, `cs`, `op`, `cs'`, `ss`, `n2w offset`]
    mp_tac unwrap_memory_value_correct >>
  simp[eval_operand_def]
QED

Theorem lower_value_name_ptrvar_correct:
  !tenv func cenv scopes ty ann id entry p region_size ss cs op cs'.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes id scopes = SOME entry /\
    evaluate_type tenv ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
    fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      lowered_value_rel ann entry.type entry.value op out /\ same_blocks cs cs' /\
      fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all local_ptrs_rel_value >> strip_tac >>
  rename1 `eval_operand (Var p) ss = SOME addr` >>
  `unwrap_value cenv (LocatedValue ann (mk_ptr (Var p) LocMemory)) cs = (op,cs')`
    by (mp_tac (Q.SPECL [`cenv`, `id`, `Var p`, `region_size`, `ty`, `ann`, `cs`]
         lower_value_name_ptrvar) >> simp[] >> strip_tac >>
        gvs[unwrap_memory_value_eq]) >>
  qspecl_then [`tenv`, `cenv`, `ann`, `entry.type`, `entry.value`,
    `Var p`, `cs`, `op`, `cs'`, `ss`, `addr`]
    mp_tac unwrap_memory_value_correct >> simp[]
QED

Theorem compile_name_correct:
  !env cenv cx func ty ann id es ss cs op cs'.
    well_typed_expr env (Name ann id) /\ env_consistent env cx es /\
    state_well_typed es /\ fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') /\
    ((?offset region_size. FLOOKUP cenv.ce_vars id = SOME (MemLoc offset region_size) /\
        offset < dimword(:256) /\ vars_rel cenv es.scopes ss) \/
     (?p region_size. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
        local_ptrs_rel func cenv es.scopes ss)) ==>
    ?v tv out.
      eval_expr cx (Name ann id) es = (INL (Value v),es) /\
      evaluate_type env.type_defs ann = SOME tv /\
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      lowered_value_rel ann tv v op out /\ same_blocks cs cs' /\
      fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all well_typed_Name_lookup >> strip_tac >> gvs[] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  `eval_expr cx (Name ann id) es = (INL (Value entry.value),es)` by
    (irule eval_name_lookup_scopes >> simp[]) >>
  FIRST [drule_all lower_value_name_memloc_correct,
         drule_all lower_value_name_ptrvar_correct] >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
  qexistsl_tac [`entry.value`, `final`] >> simp[]
QED

Theorem state_rel_vs_vars:
  !cenv cx es ss vars.
    state_rel cenv cx es (ss with vs_vars := vars) = state_rel cenv cx es ss
Proof
  simp[state_rel_def, vars_rel_def, storage_rel_def, transient_rel_def,
    immutables_rel_def, logs_rel_def, call_ctx_rel_def,
    contract_storage_def, contract_transient_def]
QED

Theorem state_rel_assignment_frame:
  !cenv cx es ss out.
    state_rel cenv cx es ss /\ out with vs_vars := ss.vs_vars = ss ==>
    state_rel cenv cx es out
Proof
  rpt strip_tac >>
  `state_rel cenv cx es (out with vs_vars := ss.vs_vars)` by simp[] >>
  fs[state_rel_vs_vars]
QED

Theorem local_ptrs_rel_assignment_frame:
  !func cenv scopes ss out.
    local_ptrs_rel func cenv scopes ss /\ out with vs_vars := ss.vs_vars = ss /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) ==>
    local_ptrs_rel func cenv scopes out
Proof
  rpt gen_tac >> strip_tac >>
  `out.vs_allocas = ss.vs_allocas /\
   out.vs_alloca_next = ss.vs_alloca_next /\ out.vs_memory = ss.vs_memory` by
    (qpat_x_assum `out with vs_vars := ss.vs_vars = ss`
       (mp_tac o AP_TERM ``\s. (s.vs_allocas,s.vs_alloca_next,s.vs_memory)``) >>
     simp[]) >>
  irule local_ptrs_rel_frame >> qexists_tac `ss` >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all local_ptrs_rel_value >> strip_tac >>
      rename1 `eval_operand (Var p) ss = SOME addr` >>
      qpat_x_assum `!old w. eval_operand old ss = SOME w ==> _`
        (qspecl_then [`Var p`, `addr`] mp_tac) >>
      gvs[eval_operand_def]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

Theorem lowered_value_rel_assignment_frame:
  !ty tv v op ss out.
    lowered_value_rel ty tv v op ss /\ out with vs_vars := ss.vs_vars = ss /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) ==>
    lowered_value_rel ty tv v op out
Proof
  rpt gen_tac >> strip_tac >>
  `out.vs_memory = ss.vs_memory` by
    (irule assignment_frame_memory >> simp[]) >>
  fs[lowered_value_rel_def] >>
  rename1 `eval_operand op ss = SOME value_word` >>
  qexists_tac `value_word` >> simp[]
QED

(* A checked name load is compositional in the existing source/memory
   invariant, including locals held through pointer variables. *)
Theorem compile_name_preserves_state:
  !env cenv cx func ty ann id es ss cs op cs'.
    well_typed_expr env (Name ann id) /\ env_consistent env cx es /\
    state_well_typed es /\ fresh_vars_wrt cs ss /\
    state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') /\
    ((?offset region_size. FLOOKUP cenv.ce_vars id = SOME (MemLoc offset region_size) /\
        offset < dimword(:256)) \/
     (?p region_size. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size))) ==>
    ?v tv out.
      eval_expr cx (Name ann id) es = (INL (Value v),es) /\
      evaluate_type env.type_defs ann = SOME tv /\
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      lowered_value_rel ann tv v op out /\ same_blocks cs cs' /\
      fresh_vars_wrt cs' out /\ state_rel cenv cx es out /\
      local_ptrs_rel func cenv es.scopes out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `vars_rel cenv es.scopes ss` by fs[state_rel_def] >>
  qsuff_tac `well_typed_expr env (Name ann id) /\ env_consistent env cx es /\
    state_well_typed es /\ fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') /\
    ((?offset region_size. FLOOKUP cenv.ce_vars id = SOME (MemLoc offset region_size) /\
        offset < dimword(:256) /\ vars_rel cenv es.scopes ss) \/
     (?p region_size. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
        local_ptrs_rel func cenv es.scopes ss))`
  >- (disch_then (mp_tac o MATCH_MP (Q.SPECL [`env`, `cenv`, `cx`, `func`, `ty`,
        `ann`, `id`, `es`, `ss`, `cs`, `op`, `cs'`] compile_name_correct)) >>
      strip_tac >> rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
      rename1 `lowered_value_rel ann value_ty value op final` >>
      qexistsl_tac [`value`, `value_ty`, `final`] >> simp[] >> conj_tac >>
      FIRST [irule state_rel_assignment_frame >> qexists_tac `ss` >> simp[],
             irule local_ptrs_rel_assignment_frame >> qexists_tac `ss` >> simp[]]) >>
  simp[] >> metis_tac[]
QED

(* Source name evaluation through the actual word-topic compiler. In
   particular, a bytes20 load remains left-aligned and an address does not. *)
Theorem compile_name_word_topic_correct:
  !env cenv cx func ty ann id es ss cs op cs'.
    well_typed_expr env (Name ann id) /\ env_consistent env cx es /\
    state_well_typed es /\ fresh_vars_wrt cs ss /\ is_word_type ann /\
    state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') /\
    ((?offset region_size. FLOOKUP cenv.ce_vars id = SOME (MemLoc offset region_size) /\
        offset < dimword(:256)) \/
     (?p region_size. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size))) ==>
    ?v tv out.
      eval_expr cx (Name ann id) es = (INL (Value v),es) /\
      evaluate_type env.type_defs ann = SOME tv /\
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      compile_encode_log_topic op (is_bytestring_type ann) cs' = (op,cs') /\
      eval_operand op out = encode_event_topic ann v /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      state_rel cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  mp_tac (Q.SPECL [`env`, `cenv`, `cx`, `func`, `ty`, `ann`, `id`,
    `es`, `ss`, `cs`, `op`, `cs'`] compile_name_preserves_state) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
  rename1 `lowered_value_rel ann value_ty value op final` >>
  `eval_operand op final = SOME (typed_val_to_w256 value_ty value)`
    by (fs[lowered_value_rel_def] >> gvs[]) >>
  drule_all compile_word_topic_correct >> strip_tac >>
  qexistsl_tac [`value`, `value_ty`, `final`] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed name lowering theorem: " ^ name)
  end)
  (DB.thms "nameLoweringProps")
