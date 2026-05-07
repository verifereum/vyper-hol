(*
 * Counterexamples for earlier lowering memory-safety theorem statements.
 *
 * The first counterexample shows that alloca_inv alone is not enough to
 * connect a lowered function's ALLOCA sizes to the runtime vs_allocas table.
 * A lowered function allocates 32 bytes and stores through the alloca output,
 * while the adversarial state gives that allocation only one byte.
 *
 * The second counterexample keeps the ALLOCA size consistent but assigns the
 * output variable an out-of-region address, showing that size agreement alone
 * does not constrain runtime pointer values.
 *)

Theory loweringAllocaSafeAccessCounterexample
Ancestors
  compileVyper vyperCompiler loweringMemSafetyDefs
  allocaRemapDefs pointerConfinedDefs
  venomState venomMemDefs venomInst memLocDefs
  basePtrDefs compileEnv
  pred_set finite_map list option While sum arithmetic words

(* Compile environment: single MemLoc variable "buf" at offset 0, size 64.
   ce_var_type = K NONE so cenv_matches_fn and well_typed_lowering
   hold vacuously (no ALLOCA instruction whose output has a type). *)
Definition ce6_cenv_def:
  ce6_cenv : compile_env = <|
    ce_vars := FEMPTY |+ ("buf", MemLoc 0 64);
    ce_storage_layout := FEMPTY; ce_module := NONE;
    ce_struct_fields := FEMPTY; ce_dynarray_capacity := K 0;
    ce_method_id := K 42; ce_flag_member_id := (λ_ _. 0);
    ce_flag_n_members := K 0; ce_var_type := K NONE;
    ce_is_hashmap := K F; ce_event_info := (λ_ . (0, [], []));
    ce_returns_count := 1; ce_return_buf := NONE;
    ce_is_external := T;
    ce_ret_enc_info := AbiPrimWord;
    ce_ret_dec_info := DecPrimWord NoClamp;
    ce_max_return_size := 32; ce_is_ctor := F;
    ce_func_info := (λ_ . (0, 0, []));
    ce_nonreentrant := (F, 0, F, F); ce_raw_return := F
  |>
End

(* External function with a DecDynArray argument.
   This triggers compile_abi_decode_to_buf → compile_alloc_buffer → ALLOCA + MSTORE[Var].
   Specifically: ALLOCA [Lit 32w] -> "%21", MSTORE [Var "%21"; Lit 0w] *)
Definition ce6_ext_fn_def:
  ce6_ext_fn =
    ("test_fn", ce6_cenv,
     [("buf", F, T, 32, DecDynArray (DecBytestring 32) 32 32 T 1)],
     36, F, F, 0, F, F, [Pass], SOME (BaseT (UintT 256)))
End

Definition ce6_run_result_def:
  ce6_run_result =
    FST (run_lowering [] [ce6_ext_fn] [] NONE Sparse 0 0 [] (K ("",0,F)) "entry")
End

Definition ce6_fn_def:
  ce6_fn = HD ce6_run_result.ctx_functions
End

(* Extract the "test_fn" block — contains the ALLOCA and MSTORE instructions *)
Definition ce6_bb_def:
  ce6_bb = HD (FILTER (λbb. bb.bb_label = "test_fn") ce6_fn.fn_blocks)
End

(* Adversarial state: single alloca aid=0 at (offset=0, size=1) — only 1 byte.
   The fn's ALLOCA instruction allocates 32 bytes, but vs_allocas can freely differ.
   Variable "%21" = 0w (within the [0,1) alloca region). *)
Definition ce6_state_def:
  ce6_state : venom_state = (init_venom_state "entry") with <|
    vs_vars := FEMPTY |+ ("%21", 0w);
    vs_memory := GENLIST (K (0w:word8)) 64;
    vs_allocas := FEMPTY |+ (0, (0, 1));
    vs_alloca_next := 1
  |>
End

(* ===== Hypotheses of the earlier arbitrary-state statement — all TRUE ===== *)

Theorem ce6_fn_in_run_lowering:
  MEM ce6_fn (FST (run_lowering [] [ce6_ext_fn] [] NONE Sparse 0 0 [] (K ("",0,F)) "entry")).ctx_functions
Proof
  simp[ce6_fn_def, ce6_run_result_def] >> EVAL_TAC
QED

Theorem ce6_cenv_matches_fn:
  cenv_matches_fn ce6_cenv ce6_fn
Proof
  simp[cenv_matches_fn_def] >> rpt strip_tac >>
  (* ce6_cenv.ce_var_type = K NONE, so antecedent is always false *)
  fs[ce6_cenv_def]
QED

Theorem ce6_alloca_inv:
  alloca_inv ce6_state
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       ce6_state_def] >>
  conj_tac >- (
    rpt strip_tac >> fs[FLOOKUP_UPDATE] >> metis_tac[]
  ) >>
  rpt strip_tac >> fs[FLOOKUP_UPDATE] >> decide_tac
QED

Theorem ce6_well_typed_lowering:
  well_typed_lowering ce6_cenv
Proof
  simp[well_typed_lowering_def] >> conj_tac >- (
    simp[well_formed_cenv_def, ce6_cenv_def] >> conj_tac >- (
      rpt strip_tac >> fs[FLOOKUP_UPDATE] >> metis_tac[]
    ) >>
    rpt strip_tac >> fs[FLOOKUP_UPDATE] >> decide_tac
  ) >>
  simp[ce6_cenv_def] >> rpt gen_tac >> strip_tac >> fs[]
QED

Theorem ce6_memory_bound:
  ∀aid off asz.
    FLOOKUP ce6_state.vs_allocas aid = SOME (off, asz) ⇒
    off + asz ≤ LENGTH ce6_state.vs_memory
Proof
  simp[ce6_state_def] >> Cases >> rpt strip_tac >> fs[FLOOKUP_UPDATE] >> decide_tac
QED

(* ===== Key facts about the fn from run_lowering ===== *)

Theorem ce6_fn_has_alloca:
  ∃inst. MEM inst (fn_insts ce6_fn) ∧
    inst.inst_opcode = ALLOCA ∧ inst.inst_operands = [Lit 32w] ∧
    inst.inst_outputs = ["%21"]
Proof
  qexists `<|inst_id := 28; inst_opcode := ALLOCA; inst_operands := [Lit 32w]; inst_outputs := ["%21"]|>` >>
  simp[ce6_fn_def, ce6_run_result_def, fn_insts_def] >> EVAL_TAC
QED

Theorem ce6_fn_has_mstore:
  ∃inst. MEM inst (fn_insts ce6_fn) ∧
    inst.inst_opcode = MSTORE ∧ inst.inst_operands = [Var "%21"; Lit 0w]
Proof
  qexists `<|inst_id := 29; inst_opcode := MSTORE; inst_operands := [Var "%21"; Lit 0w]; inst_outputs := []|>` >>
  simp[ce6_fn_def, ce6_run_result_def, fn_insts_def] >> EVAL_TAC
QED

Theorem ce6_fn_has_mstore_write_ops:
  ∃inst ops. MEM inst ce6_bb.bb_instructions ∧
    inst.inst_opcode = MSTORE ∧ inst.inst_operands = [Var "%21"; Lit 0w] ∧
    mem_write_ops inst = SOME ops ∧
    ops.iao_ofst = Var "%21" ∧ ops.iao_max_size = SOME (Lit 32w)
Proof
  qexistsl [
    `<|inst_id := 29; inst_opcode := MSTORE; inst_operands := [Var "%21"; Lit 0w]; inst_outputs := []|>`,
    `<|iao_ofst := Var "%21"; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`
  ] >>
  simp[mem_write_ops_def, ce6_bb_def, ce6_fn_def, ce6_run_result_def] >> EVAL_TAC
QED

Theorem ce6_bb_in_fn_blocks:
  MEM ce6_bb ce6_fn.fn_blocks
Proof
  simp[ce6_bb_def, ce6_fn_def, ce6_run_result_def] >>
  EVAL_TAC
QED

(* ===== alloca_roots + pointer_derived_vars ===== *)

(* First: compute the FILTER of ALLOCA instructions from fn_insts ce6_fn.
   This gives a singleton list containing just the ALLOCA instruction with output "%21".
   We extract the concrete instruction via HD for later use. *)

Theorem ce6_alloca_filter:
  FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts ce6_fn) =
    [<|inst_id := 28; inst_opcode := ALLOCA;
       inst_operands := [Lit 32w]; inst_outputs := ["%21"]|>]
Proof
  simp[ce6_fn_def, ce6_run_result_def, fn_insts_def, fn_insts_blocks_def] >>
  EVAL_TAC
QED

Theorem ce6_alloca_inst:
  ∀inst. MEM inst (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts ce6_fn)) ⇒
    inst = <|inst_id := 28; inst_opcode := ALLOCA;
             inst_operands := [Lit 32w]; inst_outputs := ["%21"]|>
Proof
  rpt strip_tac >> fs[ce6_alloca_filter]
QED

(* ALLOCA instruction of ce6_fn for convenience. *)
Definition ce6_alloca_inst_def:
  ce6_alloca_inst : instruction =
    <|inst_id := 28; inst_opcode := ALLOCA;
      inst_operands := [Lit 32w]; inst_outputs := ["%21"]|>
End

Theorem ce6_alloca_inst_correct:
  MEM ce6_alloca_inst (fn_insts ce6_fn) ∧
  ce6_alloca_inst.inst_opcode = ALLOCA ∧
  inst_output ce6_alloca_inst = SOME "%21"
Proof
  simp[ce6_alloca_inst_def, inst_output_def, ce6_fn_def, ce6_run_result_def,
       fn_insts_def, fn_insts_blocks_def] >>
  EVAL_TAC
QED

Theorem ce6_alloca_roots_fwd:
  ∀out. (∃inst. MEM inst (fn_insts ce6_fn) ∧
         inst.inst_opcode = ALLOCA ∧ inst_output inst = SOME out) ⇒ out = "%21"
Proof
  rpt strip_tac >>
  `MEM inst (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts ce6_fn))` by
    simp[MEM_FILTER] >>
  drule_all ce6_alloca_inst >> strip_tac >>
  fs[inst_output_def, ce6_alloca_inst_def]
QED

Theorem ce6_alloca_roots_bwd:
  ∃inst. MEM inst (fn_insts ce6_fn) ∧
    inst.inst_opcode = ALLOCA ∧ inst_output inst = SOME "%21"
Proof
  qexists `ce6_alloca_inst` >>
  metis_tac[ce6_alloca_inst_correct]
QED

Theorem ce6_alloca_roots:
  alloca_roots ce6_fn = {"%21"}
Proof
  simp[alloca_roots_def, EXTENSION] >>
  gen_tac >> eq_tac
  >- metis_tac[ce6_alloca_roots_fwd]
  >- metis_tac[ce6_alloca_roots_bwd]
QED

Theorem ce6_pointer_use_step:
  pointer_use_step ce6_fn ["%21"] = []
Proof
  simp[ce6_fn_def, ce6_run_result_def, pointer_use_step_def] >> EVAL_TAC
QED

Theorem ce6_pointer_use_step_step:
  pointer_use_step_step ce6_fn ["%21"] = NONE
Proof
  simp[ce6_fn_def, ce6_run_result_def, pointer_use_step_step_def, ce6_pointer_use_step] >>
  once_rewrite_tac[OWHILE_THM] >> simp[ISL, ce6_pointer_use_step] >>
  once_rewrite_tac[OWHILE_THM] >> simp[ISL]
QED

Theorem ce6_pointer_use_vars:
  pointer_use_vars ce6_fn ["%21"] = ["%21"]
Proof
  simp[pointer_use_vars_def, ce6_pointer_use_step_step] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL, OUTL, ce6_pointer_use_step_step] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL, OUTL, ce6_pointer_use_step_step]
QED

Theorem ce6_pointer_derived_vars:
  pointer_derived_vars ce6_fn (alloca_roots ce6_fn) = {"%21"}
Proof
  simp[pointer_derived_vars_def, ce6_alloca_roots, SET_TO_LIST_SING,
       ce6_pointer_use_vars, LIST_TO_SET]
QED

Theorem ce6_pointer_derived_contains:
  "%21" ∈ pointer_derived_vars ce6_fn (alloca_roots ce6_fn)
Proof
  simp[ce6_pointer_derived_vars]
QED

(* ===== State facts ===== *)

Theorem ce6_lookup_var:
  lookup_var "%21" ce6_state = SOME 0w
Proof
  simp[ce6_state_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ce6_eval_operand_32:
  eval_operand (Lit 32w) ce6_state = SOME 32w
Proof
  simp[eval_operand_def, ce6_state_def]
QED

Theorem ce6_w2n_0:
  w2n (0w:256 word) = 0
Proof
  simp[w2n_n2w, LESS_MOD]
QED

Theorem ce6_w2n_32:
  w2n (32w:256 word) = 32
Proof
  simp[w2n_n2w, LESS_MOD] >>
  simp[dimword_def, fcpLib.DIMINDEX (Arbnum.fromInt 256)] >>
  decide_tac
QED

(* ===== THE COUNTEREXAMPLE: alloca_safe_access FAILS ===== *)
(* The MSTORE witness writes 32 bytes into an allocation with size 1. *)

Theorem ce6_not_alloca_safe_access:
  ¬alloca_safe_access ce6_fn (alloca_roots ce6_fn) ce6_state
Proof
  simp[alloca_safe_access_def, ce6_pointer_derived_vars, LET_DEF] >>
  simp[NOT_FORALL_THM, NOT_IMP, GSYM CONJ_ASSOC] >>
  qexistsl [
    `ce6_bb`,
    `<|inst_id := 29; inst_opcode := MSTORE; inst_operands := [Var "%21"; Lit 0w]; inst_outputs := []|>`,
    `<|iao_ofst := Var "%21"; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`,
    `0w:256 word`, `Lit 32w`, `32w:256 word`,
    `0:num`, `0:num`, `1:num`
  ] >>
  (* All antecedent conjuncts are ground; EVAL handles them.
     ¬(w2n 0w + w2n 32w ≤ 0 + 1) = ¬(0 + 32 ≤ 1) = T *)
  simp[mem_write_ops_def, ce6_bb_in_fn_blocks, ce6_state_def,
       FLOOKUP_UPDATE, lookup_var_def, eval_operand_def,
       ce6_w2n_0, ce6_w2n_32, ce6_bb_def, ce6_fn_def, ce6_run_result_def] >>
  EVAL_TAC >> decide_tac
QED

(* Earlier lowering_alloca_safe_access statement is false. *)
Theorem lowering_alloca_safe_access_IS_FALSE:
  ∃selectors ext_fns int_fns fb_fn (dispatch:dispatch_strategy)
             bucket_count fn_meta_bytes
             dense_buckets entry_info entry_label fn cenv s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                  dispatch bucket_count fn_meta_bytes
                  dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s ∧
    well_typed_lowering cenv ∧
    (∀aid off asz.
       FLOOKUP s.vs_allocas aid = SOME (off, asz) ⇒
       off + asz ≤ LENGTH s.vs_memory) ∧
    ¬alloca_safe_access fn (alloca_roots fn) s
Proof
  map_every qexists
    [`[]:(num # string # bool) list`, `[ce6_ext_fn]`,
     `[]:(string # compile_env # (string # bool) list # bool # bool # num # bool # bool # bool # num # stmt list # type option) list`,
     `NONE:(compile_env # bool # bool # num # bool # bool # stmt list # type option) option`,
     `(Sparse:dispatch_strategy)`,
     `0:num`, `0:num`, `[]:dense_bucket list`,
     `(K ("",0,F)):num -> string # num # bool`, `"entry"`,
     `ce6_fn`, `ce6_cenv`, `ce6_state`] >>
  (* After qexists + strip, each conjunct becomes a separate goal.
     simp handles most; ce6_memory_bound proves off+asz but goal has asz+off
     so decide_tac handles the arithmetic. *)
  rpt strip_tac >-
    metis_tac[ce6_fn_in_run_lowering] >-
    metis_tac[ce6_cenv_matches_fn] >-
    metis_tac[ce6_alloca_inv] >-
    metis_tac[ce6_well_typed_lowering] >-
    (rpt strip_tac >> metis_tac[ce6_memory_bound, ADD_COMM]) >>
  metis_tac[ce6_not_alloca_safe_access]
QED


(* ========================================================================= *
 * CE7: size agreement without pointer-value agreement is insufficient.
 *
 * ce6_fn has ALLOCA [Lit 32w] -> "%21" (inst_id=28).  ce7_state has a
 * matching allocation entry for inst_id 28, but vs_vars maps "%21" to an
 * out-of-region address, so ptrs_in_alloca_bounds fails.
 * ========================================================================= *)

Definition ce7_state_def:
  ce7_state : venom_state = (init_venom_state "entry") with <|
    vs_vars := FEMPTY |+ ("%21", 99999w);
    vs_memory := GENLIST (K (0w:word8)) 64;
    vs_allocas := FEMPTY |+ (28, (0, 32));
    vs_alloca_next := 32
  |>
End

(* ===== Hypotheses of the earlier size-only statement — all TRUE ===== *)

Theorem ce7_alloca_inv:
  alloca_inv ce7_state
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       ce7_state_def] >>
  conj_tac >- (
    rpt strip_tac >> fs[FLOOKUP_UPDATE] >> metis_tac[]
  ) >>
  rpt strip_tac >> fs[FLOOKUP_UPDATE] >> decide_tac
QED

Theorem ce7_alloca_sizes_match:
  alloca_sizes_match ce6_fn ce7_state
Proof
  simp[alloca_sizes_match_def] >> rpt strip_tac >>
  `MEM inst (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts ce6_fn))`
    by simp[MEM_FILTER] >>
  drule_all ce6_alloca_inst >> strip_tac >>
  fs[ce6_alloca_inst_def] >>
  simp[ce7_state_def, FLOOKUP_UPDATE, w2n_n2w] >>
  simp[dimword_def, fcpLib.DIMINDEX (Arbnum.fromInt 256)] >>
  qexists `0` >> decide_tac
QED

Theorem ce7_memory_bound:
  ∀aid off asz.
    FLOOKUP ce7_state.vs_allocas aid = SOME (off, asz) ⇒
    off + asz ≤ LENGTH ce7_state.vs_memory ∧ off + asz < dimword (:256)
Proof
  simp[ce7_state_def] >> Cases >> rpt strip_tac >>
  fs[FLOOKUP_UPDATE] >>
  simp[dimword_def, fcpLib.DIMINDEX (Arbnum.fromInt 256)] >>
  decide_tac
QED

(* ===== THE COUNTEREXAMPLE: ptrs_in_alloca_bounds FAILS ===== *)

Theorem ce7_not_ptrs_in_alloca_bounds:
  ¬ptrs_in_alloca_bounds ce6_fn (alloca_roots ce6_fn) ce7_state
Proof
  simp[ptrs_in_alloca_bounds_def, ce6_pointer_derived_vars, LET_DEF] >>
  simp[NOT_FORALL_THM, NOT_IMP] >>
  qexists `99999w:256 word` >>
  conj_tac >- simp[ce7_state_def, FLOOKUP_UPDATE, lookup_var_def] >>
  (* Goal: ¬in_alloca_region ce7_state (w2n 99999w) *)
  simp[w2n_n2w, dimword_def, fcpLib.DIMINDEX (Arbnum.fromInt 256)] >>
  (* Goal: ¬in_alloca_region ce7_state 99999 *)
  simp[in_alloca_region_def, NOT_EXISTS_THM] >>
  rpt gen_tac >>
  (* Goal: ¬(FLOOKUP ce7_state.vs_allocas aid = SOME (off,sz) ∧ off ≤ 99999 ∧ 99999 < off + sz) *)
  Cases_on `aid = 28:num` >-
    simp[ce7_state_def, FLOOKUP_UPDATE] >>
  simp[ce7_state_def, FLOOKUP_UPDATE]
QED

(* ===== TOP-LEVEL: lowering_memory_safe IS FALSE ===== *)
(* Earlier lowering_memory_safe statement is false even with alloca_sizes_match. *)

Theorem lowering_memory_safe_IS_FALSE:
  ∃selectors ext_fns int_fns fb_fn (dispatch:dispatch_strategy)
             bucket_count fn_meta_bytes
             dense_buckets entry_info entry_label fn cenv s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                  dispatch bucket_count fn_meta_bytes
                  dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s ∧
    alloca_sizes_match fn s ∧
    well_typed_lowering cenv ∧
    (∀aid off asz.
       FLOOKUP s.vs_allocas aid = SOME (off, asz) ⇒
       off + asz ≤ LENGTH s.vs_memory ∧ off + asz < dimword (:256)) ∧
    ¬ptrs_in_alloca_bounds fn (alloca_roots fn) s
Proof
  map_every qexists
    [`[]:(num # string # bool) list`, `[ce6_ext_fn]`,
     `[]:(string # compile_env # (string # bool) list # bool # bool # num # bool # bool # bool # num # stmt list # type option) list`,
     `NONE:(compile_env # bool # bool # num # bool # bool # stmt list # type option) option`,
     `(Sparse:dispatch_strategy)`,
     `0:num`, `0:num`, `[]:dense_bucket list`,
     `(K ("",0,F)):num -> string # num # bool`, `"entry"`,
     `ce6_fn`, `ce6_cenv`, `ce7_state`] >>
  rpt strip_tac >-
    metis_tac[ce6_fn_in_run_lowering] >-
    metis_tac[ce6_cenv_matches_fn] >-
    metis_tac[ce7_alloca_inv] >-
    metis_tac[ce7_alloca_sizes_match] >-
    metis_tac[ce6_well_typed_lowering] >-
    metis_tac[ce7_memory_bound, ADD_COMM] >-
    metis_tac[ce7_memory_bound, ADD_COMM] >>
  metis_tac[ce7_not_ptrs_in_alloca_bounds]
QED
