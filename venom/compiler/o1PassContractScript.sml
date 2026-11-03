(*
 * The per-pass contract of the O1 pipeline.
 *
 * The pipeline runs its passes function by function, callee first, and a
 * function's passes observe a unit in which its callees are finished and
 * its callers are still raw.  Such a unit has no meaning of its own:
 * FmpLowering gives a finished callee a hidden FMP parameter that a raw
 * caller does not pass.  So the contract is not stated on the units the
 * walk builds but on STAGE CONTEXTS: for the k-th pass of the schedule,
 * the context in which every function has been through the passes before
 * it.  The walk's intermediate functions are exactly these contexts'
 * functions (o1FnScheduleDecomp, o1ScheduleDecomp), so one contract
 * theorem per pass tag, stated between consecutive stage contexts,
 * composes to the pipeline stage theorems S4 and S6 (o1PipelineCorrect).
 *
 * A pass run is a fn_pass_step: the dispatched pass applied to one
 * function on the unit it observed, with the checks the schedule runner
 * makes.  ctx_pass_stage relates two contexts function by function through
 * such steps; the VIEW says what the observed unit's callees are relative
 * to the output context (FmpLowering reads callee signatures,
 * ConcretizeMemLoc reads callee layouts): a callee is observed in its
 * final form, reached from its stage form by the later passes.
 *
 * The contract of a pass tag has two parts.  The step part is structural
 * and per run: it keeps the shape facts S6 needs, draws fresh names from
 * the supply, and (SimplifyCFG) maps only its own merged labels; these
 * make the walk's label-map applications the identity on code.  The stage
 * part is semantic: a forward simulation of terminating runs between
 * consecutive stage contexts from one initial state, equal up to a set D
 * of dead bytes (dead_result_rel D), with the shared memory invariant
 * (unitMemInv) transported.  D is the bytes nothing reads, such as the
 * unwritten capacity of a buffer the lowering stores whole: ConcretizeMemLoc
 * moves buffers, so those bytes differ after it.  Every contract holds for
 * any D; a pass that keeps every byte proves the exact unit_result_rel and
 * lifts it (unit_result_rel_dead_result_rel), and the stages compose when
 * D is well formed (dead_wf, dead_result_rel_trans).  GAS reads the call context's gas, which the planned gas
 * oracle will supply, so a pass that reorders or drops GAS reads (DFT)
 * gets the forall-out exists-in form o1_stage_contract_gas: every initial
 * state of the output has a gas variant from which the input's terminating
 * runs are matched; gas_variant is the hook the oracle instantiates,
 * equality until then.
 *
 * The eleven contract theorems, one planned admission per pass run, are in
 * o1ContractTheorems.
 *)
Theory o1PassContract
Ancestors
  unitTransformDefs unitShapeDefs unitMemInv venomPipelineDriver
  venomPassSchedule venomFnScheduleRunner venomPassDispatcher venomWf
  venomExecSemantics venomInst irSupply contextCodegenRel stackPlanGen
  staticLayoutDefs venomState stateEquiv passSimulationDefs vfmState extCallOracle
  finite_map cfgWf dretDesugarDefs list

(* ===== Equivalence up to dead bytes ===== *)

(* The bytes nothing reads, as functions of where they are: each
   account's storage and transient storage, the immutables, and the
   return data.  A stage may change them (ConcretizeMemLoc: the unwritten
   capacity of a stored buffer).  The end-to-end theorem takes them from
   the source program's layout (storage_dead), at the running contract
   only. *)
Datatype:
  dead = <| d_stor : address -> storage -> (bytes32 # num) set;
            d_trans : address -> storage -> (bytes32 # num) set;
            d_imm : (num |-> bytes32) -> (num # num) set;
            d_ret : word8 list -> num set |>
End

(* The bytes of a storage word at key in a set of (key, byte) pairs.
   Bytes are numbered as word_to_bytes w T numbers them: byte 0 is the most
   significant. *)
Definition key_taint_def:
  key_taint X key = {k:num | k < 32 /\ (key,k) IN X}
End

Definition word_agree_except_def:
  word_agree_except m (w1:bytes32) w2 <=>
    !b. b < 32 /\ b NOTIN m ==>
        EL b (word_to_bytes w1 T) = EL b (word_to_bytes w2 T)
End

Definition storage_agree_except_def:
  storage_agree_except X (st1:storage) st2 <=>
    !k. word_agree_except (key_taint X k) (st1 k) (st2 k)
End

(* Accounts equal but for their storage, which agrees outside the dead
   bytes of the first. *)
Definition accounts_agree_except_def:
  accounts_agree_except D (a1:evm_accounts) a2 <=>
    !a. (a1 a with storage := (a2 a).storage) = a2 a /\
        storage_agree_except (D.d_stor a (a1 a).storage)
          (a1 a).storage (a2 a).storage
End

Definition transient_agree_except_def:
  transient_agree_except D (t1:transient_storage) t2 <=>
    !a. storage_agree_except (D.d_trans a (t1 a)) (t1 a) (t2 a)
End

Definition imms_agree_except_def:
  imms_agree_except D (i1:num |-> bytes32) i2 <=>
    FDOM i1 = FDOM i2 /\
    !k. k IN FDOM i1 ==>
        word_agree_except {b | (k,b) IN D.d_imm i1} (i1 ' k) (i2 ' k)
End

Definition request_agree_except_def:
  request_agree_except D (r1:call_request) r2 <=>
    r1 with <| cr_accounts := r2.cr_accounts;
               cr_tStorage := r2.cr_tStorage |> = r2 /\
    accounts_agree_except D r1.cr_accounts r2.cr_accounts /\
    transient_agree_except D r1.cr_tStorage r2.cr_tStorage
End

(* unit_result_rel, but at a halt the runs may differ at the dead bytes of
   the first run's state: in storage and transient storage (at the end and
   in each request's snapshot), the immutables and the return data. *)
Definition dead_result_rel_def:
  dead_result_rel D res res' <=>
    case (res, res') of
      (Halt s, Halt s') =>
        accounts_agree_except D s.vs_accounts s'.vs_accounts /\
        transient_agree_except D s.vs_transient s'.vs_transient /\
        imms_agree_except D s.vs_immutables s'.vs_immutables /\
        LENGTH s.vs_returndata = LENGTH s'.vs_returndata /\
        (!i. i < LENGTH s.vs_returndata /\ i NOTIN D.d_ret s.vs_returndata ==>
             EL i s.vs_returndata = EL i s'.vs_returndata) /\
        s.vs_halted = s'.vs_halted /\ s.vs_logs = s'.vs_logs /\
        s.vs_pending_deletions = s'.vs_pending_deletions /\
        LIST_REL (request_agree_except D) s.vs_requests s'.vs_requests
    | (Abort a s, Abort a' s') => (a = Revert_abort ==> a' = Revert_abort)
    | _ => F
End

(* The dead bytes are fixed by the bytes that aren't: two states that agree
   outside the first's dead bytes have the same dead bytes.  It makes
   dead_result_rel transitive (dead_result_rel_trans). *)
Definition dead_wf_def:
  dead_wf D <=>
    (!a st1 st2. storage_agree_except (D.d_stor a st1) st1 st2 ==>
                 D.d_stor a st2 = D.d_stor a st1) /\
    (!a st1 st2. storage_agree_except (D.d_trans a st1) st1 st2 ==>
                 D.d_trans a st2 = D.d_trans a st1) /\
    (!i1 i2. imms_agree_except D i1 i2 ==> D.d_imm i2 = D.d_imm i1) /\
    (!r1 r2. LENGTH r1 = LENGTH r2 /\
             (!i. i < LENGTH r1 /\ i NOTIN D.d_ret r1 ==> EL i r1 = EL i r2) ==>
             D.d_ret r2 = D.d_ret r1)
End

(* An exact match is a match up to any dead bytes. *)
Theorem unit_result_rel_dead_result_rel:
  unit_result_rel r r' ==> dead_result_rel D r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[unit_result_rel_def, dead_result_rel_def, observable_equiv_def] >>
  rw[accounts_agree_except_def, transient_agree_except_def,
     imms_agree_except_def, storage_agree_except_def,
     word_agree_except_def, vfmStateTheory.account_state_component_equality] >>
  irule EVERY2_refl >>
  simp[request_agree_except_def, accounts_agree_except_def,
       transient_agree_except_def, storage_agree_except_def,
       word_agree_except_def, vfmStateTheory.account_state_component_equality,
       extCallOracleTheory.call_request_component_equality]
QED

Theorem dead_result_rel_terminates:
  dead_result_rel D res res' ==> terminates res /\ terminates res'
Proof
  Cases_on `res` >> Cases_on `res'` >>
  simp[dead_result_rel_def, terminates_def]
QED

Theorem storage_agree_except_trans:
  storage_agree_except X st1 st2 /\ storage_agree_except X st2 st3 ==>
  storage_agree_except X st1 st3
Proof
  rw[storage_agree_except_def, word_agree_except_def] >> metis_tac[]
QED

Theorem accounts_agree_except_trans:
  dead_wf D /\ accounts_agree_except D a1 a2 /\
  accounts_agree_except D a2 a3 ==>
  accounts_agree_except D a1 a3
Proof
  rw[accounts_agree_except_def, dead_wf_def] >>
  first_x_assum (qspec_then `a` strip_assume_tac) >>
  first_x_assum (qspec_then `a` strip_assume_tac) >>
  gvs[vfmStateTheory.account_state_component_equality] >>
  metis_tac[storage_agree_except_trans]
QED

Theorem transient_agree_except_trans:
  dead_wf D /\ transient_agree_except D t1 t2 /\
  transient_agree_except D t2 t3 ==>
  transient_agree_except D t1 t3
Proof
  rw[transient_agree_except_def, dead_wf_def] >>
  metis_tac[storage_agree_except_trans]
QED

Theorem imms_agree_except_trans:
  dead_wf D /\ imms_agree_except D i1 i2 /\ imms_agree_except D i2 i3 ==>
  imms_agree_except D i1 i3
Proof
  rw[dead_wf_def] >>
  `D.d_imm i2 = D.d_imm i1` by metis_tac[] >>
  gvs[imms_agree_except_def, word_agree_except_def] >> metis_tac[]
QED

Theorem request_agree_except_trans:
  dead_wf D /\ request_agree_except D r1 r2 /\
  request_agree_except D r2 r3 ==>
  request_agree_except D r1 r3
Proof
  rw[request_agree_except_def]
  >- gvs[extCallOracleTheory.call_request_component_equality]
  >- metis_tac[accounts_agree_except_trans]
  >> metis_tac[transient_agree_except_trans]
QED

Theorem dead_result_rel_trans:
  dead_wf D /\ dead_result_rel D r1 r2 /\ dead_result_rel D r2 r3 ==>
  dead_result_rel D r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[dead_result_rel_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[accounts_agree_except_trans]
  >- metis_tac[transient_agree_except_trans]
  >- metis_tac[imms_agree_except_trans]
  >- (`D.d_ret v'.vs_returndata = D.d_ret v.vs_returndata` by
        metis_tac[dead_wf_def] >> metis_tac[])
  >> irule LIST_REL_trans >> qexists_tac `v'.vs_requests` >>
     metis_tac[request_agree_except_trans]
QED

(* ===== Simulation between two initial states ===== *)

Definition ctx_sim_def:
  ctx_sim D ctx ctx' s s' <=>
    !fuel. terminates (run_context fuel ctx s) ==>
      ?fuel'. dead_result_rel D (run_context fuel ctx s)
                                (run_context fuel' ctx' s')
End

Theorem ctx_transform_correct_ctx_sim:
  ctx_transform_correct ctx ctx' s ==> ctx_sim D ctx ctx' s s
Proof
  rw[ctx_transform_correct_def, ctx_sim_def] >>
  metis_tac[unit_result_rel_dead_result_rel]
QED

(* The gas-oracle hook: two initial states that may differ only in the
   oracle list of GAS readings.  Equality until the oracle lands. *)
Definition gas_variant_def:
  gas_variant (s : venom_state) s' <=> s' = s
End

(* ===== One pass run ===== *)

(* What run_configured_fn_pass_fold does for one pass on one function:
   the pass sees the observed unit with the function current, from a
   supply that covers it (so its fresh names are fresh), and the result
   passes the runner's checks. *)
Definition fn_pass_step_def:
  fn_pass_step rpolicy pass observed s fn out <=>
    lookup_unique_function fn.fn_name observed.cu_context.ctx_functions =
      SOME fn /\
    execute_configured_fn_pass rpolicy pass observed s fn = SOME out /\
    out.fpo_function.fn_name = fn.fn_name /\
    fn_pass_effects_hold (fn_pass_tag pass) fn out /\
    introduces_no_invoke_edges fn out.fpo_function /\
    ir_supply_covers_unit s observed /\
    ir_supply_extends s out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply observed
End

(* A function taken through a list of passes by such steps. *)
Definition fn_steps_def:
  (fn_steps rpolicy [] fn fn' <=> fn' = fn) /\
  (fn_steps rpolicy (pass::passes) fn fn' <=>
    ?observed s out.
      fn_pass_step rpolicy pass observed s fn out /\
      fn_steps rpolicy passes out.fpo_function fn')
End

(* ===== Stage contexts ===== *)

(* The observed unit's callees of fn are finished: each is reached from
   its form in the output context C' by the passes still to come. *)
Definition walk_view_def:
  walk_view rpolicy later C' fn observed <=>
    !name g'.
      MEM name (fn_invoke_targets fn) /\
      lookup_function name C'.ctx_functions = SOME g' ==>
      ?g. lookup_function name observed.cu_context.ctx_functions = SOME g /\
          fn_steps rpolicy later g' g
End

(* C' is C with every function taken through pass by one step, each on an
   observed unit with C's entry, reservations and function names, related
   to C' by view. *)
Definition ctx_pass_stage_def:
  ctx_pass_stage rpolicy pass view C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    C'.ctx_global_reserved = C.ctx_global_reserved /\
    LIST_REL
      (\fn fn'. ?observed s out.
         fn_pass_step rpolicy pass observed s fn out /\
         out.fpo_function = fn' /\
         observed.cu_context.ctx_entry = C.ctx_entry /\
         observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
         ctx_fn_names observed.cu_context = ctx_fn_names C /\
         view C' fn observed)
      C.ctx_functions C'.ctx_functions
End

(* ===== Shape facts carried through every stage ===== *)

(* The entry function ends the unit's run itself: no return of any kind
   (RET, or the RETFMP and DRET the later passes and the desugaring use),
   which run_context would report as IntRet; and no parameter
   instruction anywhere, so that no pass can move one into its first
   block. *)
Definition entry_fn_no_return_def:
  entry_fn_no_return fn <=>
    EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts fn)
End

Definition entry_fn_no_params_def:
  entry_fn_no_params fn <=>
    EVERY (\inst. ~is_param_opcode inst.inst_opcode) (fn_insts fn)
End

Theorem fn_insts_blocks_MEM:
  !bbs. MEM inst (fn_insts_blocks bbs) <=>
        ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem entry_fn_no_return_no_ret:
  entry_fn_no_return fn ==> entry_fn_no_ret fn
Proof
  simp[entry_fn_no_return_def, entry_fn_no_ret_def, EVERY_MEM, fn_insts_def,
       fn_insts_blocks_MEM] >>
  metis_tac[]
QED

Theorem get_params_no_param:
  EVERY (\inst. ~is_param_opcode inst.inst_opcode) insts ==>
  get_params insts = []
Proof
  Cases_on `insts` >> simp[get_params_def]
QED

Theorem entry_fn_no_params_get_params:
  entry_fn_no_params fn /\ fn.fn_blocks <> [] ==>
  get_params (HD fn.fn_blocks).bb_instructions = []
Proof
  Cases_on `fn.fn_blocks` >>
  gvs[entry_fn_no_params_def, fn_insts_def, fn_insts_blocks_def,
      get_params_no_param]
QED

(* Every INVOKE names a function of the context in its first operand. *)
Definition fn_invoke_ok_def:
  fn_invoke_ok names fn <=>
    !inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE ==>
      ?lbl rest. inst.inst_operands = Label lbl :: rest /\ MEM lbl names
End

(* Every other label operand names a block of its own function or a
   reserved label: INVOKE targets are the only cross-function references,
   so one function's label map never touches another function's code. *)
Definition fn_label_refs_ok_def:
  fn_label_refs_ok fn <=>
    !inst l. MEM inst (fn_insts fn) /\ MEM (Label l) inst.inst_operands /\
             inst.inst_opcode <> INVOKE ==>
      MEM l (fn_labels fn) \/ reserved_label l
End

Definition unit_label_refs_ok_def:
  unit_label_refs_ok unit <=>
    EVERY fn_label_refs_ok unit.cu_context.ctx_functions
End

(* No PHI in the first block: it has no predecessors (first_block_no_preds),
   so a PHI there is dead, and a pass that inserts a prologue there
   (FmpLowering's INITIAL_FMP, DretDesugar after the PARAMs) would put it
   before a PHI, which bb_well_formed forbids. *)
Definition first_block_no_phi_def:
  first_block_no_phi fn <=>
    EVERY (\inst. inst.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions
End

Definition unit_first_block_no_phi_def:
  unit_first_block_no_phi unit <=>
    EVERY first_block_no_phi unit.cu_context.ctx_functions
End

(* Definite assignment of the source: every variable a use reads is
   written on every path to it.  SimplifyCFG's pre-walk needs it, and S3
   owes it (S2b). *)
Definition unit_defs_reach_uses_def:
  unit_defs_reach_uses unit <=>
    EVERY fn_defs_reach_uses unit.cu_context.ctx_functions
End

(* The unit's entry function has no parameter instruction (the lowering's
   entry function reads calldata, never PARAMs). *)
Definition unit_entry_no_params_def:
  unit_entry_no_params unit <=>
    !fn. MEM fn unit.cu_context.ctx_functions /\
         unit.cu_context.ctx_entry = SOME fn.fn_name ==>
         entry_fn_no_params fn
End

(* The per-function shape facts of o1_source_unit_ok that every pass keeps,
   with the well-formedness every pass keeps.  Of the raw-opcode
   restriction only no DRET is kept, which no pass introduces (the source
   never has one, so DretDesugar is the identity); the passes introduce
   the other opcodes it excludes. *)
Definition o1_fn_shape_def:
  o1_fn_shape ctx fn <=>
    wf_function fn /\ fn_inst_wf fn /\
    fn_shape_ok fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
    fn_invoke_ok (ctx_fn_names ctx) fn /\ fn_label_refs_ok fn /\
    no_dret fn /\
    (ctx.ctx_entry = SOME fn.fn_name ==>
       entry_fn_no_return fn /\ entry_fn_no_params fn) /\
    (ctx.ctx_entry <> SOME fn.fn_name ==>
       EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn))
End

(* venom_wf without global instruction-id distinctness, which is the IR
   supply's concern and not a pass's. *)
Definition o1_ctx_shape_def:
  o1_ctx_shape ctx <=>
    ctx_wf ctx /\ EVERY (o1_fn_shape ctx) ctx.ctx_functions
End

(* ===== Step contract: structural, per run ===== *)

(* New block labels and instruction ids come from the supply, so they are
   unused anywhere in the observed unit. *)
Definition fresh_names_ok_def:
  fresh_names_ok s fn fn' <=>
    (!l. MEM l (fn_labels fn') ==>
         MEM l (fn_labels fn) \/ ~MEM l s.irs_used_labels) /\
    (!id. MEM id (fn_ir_inst_ids fn') ==>
          MEM id (fn_ir_inst_ids fn) \/ ~MEM id s.irs_used_inst_ids)
End

(* A label map renames only block labels of the input that the output no
   longer has, never the entry label (the function's name). *)
Definition label_map_sources_ok_def:
  label_map_sources_ok fn fn' label_map <=>
    EVERY (\e. MEM (FST e) (fn_labels fn) /\ FST e <> fn.fn_name /\
               ~MEM (FST e) (fn_labels fn')) label_map
End

(* The supply's used instruction ids are below its next one
   (ir_supply_inst_ok): true of the initial supply, and what makes a fresh
   id fresh; every run keeps it. *)
Definition o1_step_contract_def:
  o1_step_contract rpolicy pass <=>
    !observed s fn out.
      fn_pass_step rpolicy pass observed s fn out /\
      o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s ==>
      o1_fn_shape observed.cu_context out.fpo_function /\
      fresh_names_ok s fn out.fpo_function /\
      label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
      ir_supply_inst_ok out.fpo_supply
End

(* The per-function stage rows: what a run may assume of the function it
   is given and must establish of the one it returns, where the stage
   table o1_inv below cannot reach, since the walk runs each pass on one
   function at a time in a mixed context.  Row k holds of a function that
   has been through the first k walk passes; from row 3 on (after
   ConcretizeMemLoc) the function has no ALLOCA, which SingleUseExpansion
   needs, since it would expand the literal operand of one. *)
Definition o1_fn_row_def:
  o1_fn_row (k : num) fn <=>
    3 <= k ==> EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn)
End

(* The step contract of the k-th walk run: the step contract, with row k
   of the function rows assumed of the input and row k+1 owed of the
   output. *)
Definition o1_step_contract_at_def:
  o1_step_contract_at k rpolicy pass <=>
    !observed s fn out.
      fn_pass_step rpolicy pass observed s fn out /\
      o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
      o1_fn_row k fn ==>
      o1_fn_shape observed.cu_context out.fpo_function /\
      fresh_names_ok s fn out.fpo_function /\
      label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
      ir_supply_inst_ok out.fpo_supply /\
      o1_fn_row (SUC k) out.fpo_function
End

(* The step contracts of a pass list whose first pass is the k-th run. *)
Definition o1_step_contracts_from_def:
  (o1_step_contracts_from rpolicy k [] <=> T) /\
  (o1_step_contracts_from rpolicy k (pass::passes) <=>
     o1_step_contract_at k rpolicy pass /\
     o1_step_contracts_from rpolicy (SUC k) passes)
End

(* Before row 3 the rows say nothing, so the step contract is the plain
   one. *)
Theorem o1_step_contract_at_plain:
  k < 2 ==>
  (o1_step_contract_at k rpolicy pass <=> o1_step_contract rpolicy pass)
Proof
  simp[o1_step_contract_at_def, o1_step_contract_def, o1_fn_row_def]
QED

(* A pass with the plain step contract that takes row k to row k+1 has
   the k-th step contract. *)
Theorem o1_step_contract_at_preserve:
  o1_step_contract rpolicy pass /\
  (!observed s fn out.
     fn_pass_step rpolicy pass observed s fn out /\
     o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
     o1_fn_row k fn ==>
     o1_fn_row (SUC k) out.fpo_function) ==>
  o1_step_contract_at k rpolicy pass
Proof
  simp[o1_step_contract_at_def, o1_step_contract_def] >> metis_tac[]
QED

(* ===== Stage contract: semantic, between stage contexts ===== *)

(* The initial state of a stage run: the pipeline's initial state, with
   the dynamic-memory pointer at the run's initial free-memory pointer,
   as the entry state has it (FmpLowering seeds its pointer variable from
   vs_initial_fmp). *)
Definition o1_run_state_ok_def:
  o1_run_state_ok vs <=>
    o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp
End

(* The memory facts of unitMemInv depend on a state only through the
   alloca frame and, range by range, the instruction's access ranges; so a
   pass that splits or copies an access, or adds one without ranges,
   keeps them. *)
Definition rangewise_mem_fact_def:
  rangewise_mem_fact M <=>
    ?Q R. !ctx fn inst s.
      M ctx fn inst s <=>
      Q s.vs_alloca_next s.vs_allocas s.vs_initial_fmp /\
      EVERY (\r. R r s.vs_alloca_next s.vs_allocas s.vs_initial_fmp)
        (inst_mem_ranges inst s)
End

(* The lowered-phase fact with the frame pointer read off the state: the
   semantics never writes vs_initial_fmp, so this is lowered_mem_ok at the
   initial state's fmp along every run. *)
Definition lowered_mem_fact_def:
  lowered_mem_fact eom ctx fn inst s <=>
    lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s
End

(* The stage contract of one pass run, between consecutive stage contexts
   C and C' and one initial state: every terminating run of C is matched
   by a run of C' up to the dead bytes D, and the stage invariant I of C
   becomes I' of C'.  pre
   relates the input to the output (an ordering the pass keeps, say); a
   fact about the input alone belongs in I. *)
Definition o1_stage_contract_def:
  o1_stage_contract rpolicy D pass view pre I I' <=>
    !C C' vs.
      ctx_pass_stage rpolicy pass view C C' /\ pre C C' /\
      o1_ctx_shape C /\ o1_run_state_ok vs /\ I C vs ==>
      ctx_sim D C C' vs vs /\ I' C' vs
End

(* Every initial state vs' of the output has a gas variant vs from which
   the input's terminating runs are matched by the output's runs from vs'. *)
Definition o1_stage_contract_gas_def:
  o1_stage_contract_gas rpolicy D pass view pre I I' <=>
    !C C' vs'.
      ctx_pass_stage rpolicy pass view C C' /\ pre C C' /\
      o1_ctx_shape C /\ o1_run_state_ok vs' /\ I C vs' ==>
      ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\ I' C' vs'
End

Definition any_view_def:
  any_view (C' : venom_context) (fn : ir_function)
           (observed : compilation_unit) <=> T
End

Definition no_pre_def:
  no_pre (C : venom_context) (C' : venom_context) <=> T
End

(* ===== The stage invariants ===== *)

(* Before ConcretizeMemLoc: the raw phase of the shared memory invariant,
   S3's conclusion, and well-formed global reservations, which
   max_live_eom (row 3 on) requires and the walk never changes; the
   lowering reserves nothing in the runtime unit and one interval in the
   deploy unit. *)
Definition o1_src_inv_def:
  o1_src_inv C vs <=>
    reserved_intervals_wf C.ctx_global_reserved /\ mem_inv raw_mem_ok C vs
End

(* The pre-walk's input, the lowering's output: no PHI, and every variable
   a use reads is written on every path to it (S3 owes the latter; the
   source shape gives the former).  SimplifyCFG needs both: they make its
   PHI fix-up and its dropped JNZ conditions invisible. *)
Definition o1_pre_walk_inv_def:
  o1_pre_walk_inv C vs <=>
    o1_src_inv C vs /\
    EVERY (\fn. fn_defs_reach_uses fn /\
                EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn))
      C.ctx_functions
End

(* The walk's input (row 0), SimplifyCFG's pre-walk output: every block
   reachable, definite assignment, and no PHI reading a variable written
   twice (vacuous here, with no PHI yet), which MakeSSA needs. *)
Definition o1_walk_src_inv_def:
  o1_walk_src_inv C vs <=>
    o1_src_inv C vs /\
    EVERY (\fn. all_reachable fn /\ fn_defs_reach_uses fn /\
                fn_phi_operands_single_def fn /\ fn_phis_cover_preds fn)
      C.ctx_functions
End

(* After ConcretizeMemLoc: every access below the context's layout end,
   max_live_eom (the largest function layout end and global reserved end),
   where codegen's spill regions start.  The bound is the context's, not
   existential over any upper bound, so it is not satisfiable by a large
   eom. *)
Definition o1_static_inv_def:
  o1_static_inv C vs <=>
    ?eom. max_live_eom C = SOME eom /\ mem_inv (static_mem_ok eom) C vs
End

(* After FmpLowering: static, or dynamic at or above the initial fmp. *)
Definition o1_lowered_inv_def:
  o1_lowered_inv C vs <=>
    ?eom. max_live_eom C = SOME eom /\ mem_inv (lowered_mem_fact eom) C vs
End

(* Rows 5 and 6 (SimplifyCFG's input, SUE's input) add wf_ssa: MakeSSA's
   second run establishes it and SimplifyCFG keeps it. *)
Definition o1_ssa_inv_def:
  o1_ssa_inv C vs <=> o1_lowered_inv C vs /\ EVERY wf_ssa C.ctx_functions
End

(* The invariant of the k-th stage context of the walk (k = 0 its input,
   k = 9 its output).  A pass run's contract takes row k to row k+1; a
   fact a run needs of its input is a conjunct of its row, put there by
   the run that establishes it, and a conjunct of row 0 is a premise of
   S4 that the lowering stage owes.  A row may speak of the dead bytes D
   the runs are matched up to. *)
Definition o1_inv_def:
  o1_inv (D : dead) (k : num) =
    if k = 0 then o1_walk_src_inv
    else if k <= 2 then o1_src_inv
    else if k = 3 then o1_static_inv
    else if k = 5 \/ k = 6 then o1_ssa_inv
    else o1_lowered_inv
End

(* What the k-th run's contract may assume of its stage contexts besides
   the rows of o1_inv: the function rows, row k of the input's functions
   and row k+1 of the output's, which the step contracts establish along
   the walk. *)
Definition o1_pre_def:
  o1_pre k (C : venom_context) (C' : venom_context) <=>
    EVERY (o1_fn_row k) C.ctx_functions /\
    EVERY (o1_fn_row (SUC k)) C'.ctx_functions
End

(* ===== The schedule ===== *)

(* The view of the k-th walk pass: callees are observed after the passes
   that follow it. *)
Definition o1_walk_view_def:
  o1_walk_view rpolicy k = walk_view rpolicy (DROP (SUC k) o1_fn_passes)
End

(* The stage contract of the k-th run of the walk. *)
Definition o1_run_contract_def:
  o1_run_contract rpolicy D k <=>
    o1_stage_contract rpolicy D (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (o1_pre k) (o1_inv D k) (o1_inv D (SUC k))
End

Definition o1_run_contract_gas_def:
  o1_run_contract_gas rpolicy D k <=>
    o1_stage_contract_gas rpolicy D (EL k o1_fn_passes)
      (o1_walk_view rpolicy k) (o1_pre k) (o1_inv D k) (o1_inv D (SUC k))
End
