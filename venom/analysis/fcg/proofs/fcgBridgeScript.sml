(*
 * FCG Bridge Lemmas
 *
 * Bridge lemmas connecting raw instruction structure to analysis functions.
 * These bridge the semantic fn_directly_calls relation to get_invoke_targets
 * and fcg_scan_function.
 *
 * TOP-LEVEL theorems:
 *   mem_get_invoke_targets_pair   - pair membership => inst properties
 *   mem_scan_function_pair        - scan pair => inst properties
 *   get_invoke_targets_skip       - non-INVOKE instructions are skipped
 *   get_invoke_targets_mono       - tail results are subset of cons results
 *   get_invoke_targets_intro      - reverse of mem_get_invoke_targets_pair
 *   mem_get_invoke_targets        - MEM in MAP FST characterization
 *   fn_directly_calls_scan        - bridge to get_invoke_targets
 *)

Theory fcgBridge
Ancestors
  fcgDefs

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
  >> Cases_on `h.inst_opcode = INVOKE` >> simp[]
  >- (Cases_on `h.inst_operands` >> simp[]
      >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
      >> rename1 `op :: ops`
      >> Cases_on `op` >> simp[]
      >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
      >> strip_tac >> gvs[]
      >> res_tac >> simp[])
  >> strip_tac >> res_tac >> simp[]
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
  simp[Once get_invoke_targets_def]
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
