(*
 * FCG Analysis Definitions
 *
 * Semantic definitions and bridge lemmas for FCG correctness.
 *
 * TOP-LEVEL definitions:
 *   ctx_fn_names          - convenience: function names in context
 *   wf_fn_names           - well-formedness: distinct names, entry valid
 *   wf_invoke_targets     - well-formedness: INVOKE targets are valid
 *   fn_directly_calls     - semantic direct-call relation
 *   fcg_path              - reachability via RTC of direct calls
 *
 * TOP-LEVEL theorems:
 *   fn_directly_calls_scan               - bridge to get_invoke_targets
 *   mem_get_invoke_targets_pair          - pair membership => inst properties
 *   mem_scan_function_pair              - scan pair => inst properties
 *   mem_get_invoke_targets              - MEM in MAP FST characterization
 *)

Theory fcgAnalysisDefs
Ancestors
  fcgAnalysis relation venomInst

(* ===== Convenience Helper ===== *)

Definition ctx_fn_names_def:
  ctx_fn_names ctx = MAP (\f. f.fn_name) ctx.ctx_functions
End

(* ===== Well-Formedness Predicates ===== *)

Definition wf_fn_names_def:
  wf_fn_names ctx <=>
    ALL_DISTINCT (ctx_fn_names ctx) /\
    (!entry_name. ctx.ctx_entry = SOME entry_name ==>
       MEM entry_name (ctx_fn_names ctx))
End

Definition wf_invoke_targets_def:
  wf_invoke_targets ctx <=>
    (!func inst.
       MEM func ctx.ctx_functions /\
       MEM inst (fn_insts func) /\
       inst.inst_opcode = INVOKE ==>
       ?lbl rest. inst.inst_operands = Label lbl :: rest /\
                  MEM lbl (ctx_fn_names ctx))
End

(* ===== Semantic Relation via RTC ===== *)

(* Direct call edge: fn_a has an INVOKE instruction targeting fn_b.
   Defined purely from instruction structure -- no analysis functions. *)
Definition fn_directly_calls_def:
  fn_directly_calls ctx fn_a fn_b <=>
    ?func inst rest.
      lookup_function fn_a ctx.ctx_functions = SOME func /\
      MEM inst (fn_insts func) /\
      inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label fn_b :: rest
End

(* Reachability = reflexive-transitive closure of direct calls *)
Definition fcg_path_def:
  fcg_path ctx = RTC (fn_directly_calls ctx)
End

(* ===== Bridge Lemmas ===== *)

(* Helper: MEM pair in get_invoke_targets => instruction properties *)
Theorem mem_get_invoke_targets_pair:
  !insts callee inst.
    MEM (callee, inst) (get_invoke_targets insts) ==>
    MEM inst insts /\ inst.inst_opcode = INVOKE /\
    ?rest. inst.inst_operands = Label callee :: rest
Proof
  Induct >> simp[get_invoke_targets_def]
  >> rpt gen_tac >> strip_tac
  >> qpat_x_assum `MEM _ _` mp_tac
  >> simp[Once get_invoke_targets_def]
  >> Cases_on `h.inst_opcode` >> simp[]
  >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
  >> Cases_on `h.inst_operands` >> simp[]
  >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
  >> rename1 `op :: ops`
  >> Cases_on `op` >> simp[]
  >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
  >> strip_tac >> gvs[]
  >> TRY (res_tac >> simp[])
  >> metis_tac[]
QED

(* Corollary: MEM pair in fcg_scan_function => instruction properties *)
Theorem mem_scan_function_pair:
  MEM (callee, inst) (fcg_scan_function func) ==>
  MEM inst (fn_insts func) /\ inst.inst_opcode = INVOKE /\
  ?rest. inst.inst_operands = Label callee :: rest
Proof
  simp[fcg_scan_function_def] >>
  metis_tac[mem_get_invoke_targets_pair]
QED

(* Helper: non-INVOKE instructions are skipped *)
Theorem get_invoke_targets_skip:
  h.inst_opcode <> INVOKE ==>
  get_invoke_targets (h::rest) = get_invoke_targets rest
Proof
  strip_tac >> simp[Once get_invoke_targets_def] >>
  Cases_on `h.inst_opcode` >> gvs[]
QED

(* Helper: tail results are a subset of cons results *)
Theorem get_invoke_targets_mono:
  MEM pair (get_invoke_targets insts) ==>
  MEM pair (get_invoke_targets (h :: insts))
Proof
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[Once get_invoke_targets_def] >>
      Cases_on `h.inst_operands`
      >- simp[]
      >> rename1 `op :: ops` >> Cases_on `op` >> simp[])
  >> simp[get_invoke_targets_skip]
QED

(* Helper: reverse of mem_get_invoke_targets_pair *)
Theorem get_invoke_targets_intro:
  !insts callee inst rest.
    MEM inst insts /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee :: rest ==>
    MEM (callee, inst) (get_invoke_targets insts)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
  >- (simp[Once get_invoke_targets_def] >> simp[])
  >> irule get_invoke_targets_mono >> res_tac
QED

(* Helper: characterizes MEM in MAP FST of get_invoke_targets *)
Theorem mem_get_invoke_targets:
  MEM name (MAP FST (get_invoke_targets insts)) <=>
  ?inst rest. MEM inst insts /\
              inst.inst_opcode = INVOKE /\
              inst.inst_operands = Label name :: rest
Proof
  Induct_on `insts`
  >- simp[get_invoke_targets_def]
  >> rpt gen_tac
  >> reverse (Cases_on `h.inst_opcode = INVOKE`)
  >- (simp[get_invoke_targets_skip] >> metis_tac[])
  >> simp[Once get_invoke_targets_def]
  >> Cases_on `h.inst_operands`
  >- (simp[] >> eq_tac >> strip_tac >> gvs[] >> metis_tac[])
  >> rename1 `op :: ops`
  >> Cases_on `op` >> simp[]
  >> eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Key equivalence: the raw-instruction definition of fn_directly_calls
   is equivalent to the analysis's fcg_scan_function / get_invoke_targets.
   This is the only place that bridges semantics to implementation. *)
Theorem fn_directly_calls_scan:
  fn_directly_calls ctx fn_a fn_b <=>
  ?func. lookup_function fn_a ctx.ctx_functions = SOME func /\
         MEM fn_b (MAP FST (fcg_scan_function func))
Proof
  simp[fn_directly_calls_def, fcg_scan_function_def,
       mem_get_invoke_targets] >>
  metis_tac[]
QED

val _ = export_theory();
