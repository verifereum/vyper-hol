(* TOP-LEVEL: the generated static-element array loop executes exactly the
   runtime length's number of iterations. FUNPOW describes the established
   memory postcondition; execution is witnessed by paths in the real function.
   Helpers compose SSA snapshots and the per-iteration invariant. *)
Theory abiStaticLoopRun
Ancestors
  abiStaticLoopCode abiStaticLoopIteration abiStaticLoopBody
  fragBlockPath fragExec compileEnv exprLoweringProps
  venomExecSemantics venomState venomInst list rich_list words arithmetic
Libs wordsLib

Definition abi_static_loop_effect_def:
  abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels ss =
    jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
        (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss))
End

Definition abi_static_loop_run_inv_def:
  abi_static_loop_run_inv var_base labels dst_addr src_addr info abi_sz mem_sz
      counter_addr initial i current_state <=>
    current_state.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\
    current_state.vs_inst_idx = 0 /\ ~current_state.vs_halted /\
    mload (w2n counter_addr) current_state = n2w i /\
    current_state with vs_vars := initial.vs_vars =
      FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels)
        i initial /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (abi_static_loop_iteration_names var_base info) ==>
      eval_operand arg_op current_state = eval_operand arg_op initial)
End

Theorem abi_static_loop_effect_reset_vars:
  !info dst_addr src_addr abi_sz mem_sz counter_addr labels vars ss.
    abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels
      (ss with vs_vars := vars) =
    (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels ss)
      with vs_vars := vars
Proof
  simp[abi_static_loop_effect_def, abi_static_loop_body_memory_reset_vars,
    jump_to_reset_vars_eq]
QED

Theorem abi_static_loop_snapshot_step:
  !info dst_addr src_addr abi_sz mem_sz counter_addr labels initial current_state out i.
    current_state with vs_vars := initial.vs_vars =
      FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels)
        i initial /\
    out with vs_vars := current_state.vs_vars =
      abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels
        current_state ==>
    out with vs_vars := initial.vs_vars =
      FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels)
        (SUC i) initial
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `out with vs_vars := _ = _`
    (mp_tac o AP_TERM ``\s:venom_state. s with vs_vars := initial.vs_vars``) >>
  simp[GSYM abi_static_loop_effect_reset_vars, FUNPOW_SUC]
QED

Theorem abi_static_loop_run_inv_initial:
  !var_base labels dst_addr src_addr info abi_sz mem_sz counter_addr ss.
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\ mload (w2n counter_addr) ss = 0w ==>
    abi_static_loop_run_inv var_base labels dst_addr src_addr info abi_sz mem_sz
      counter_addr ss 0 ss
Proof
  simp[abi_static_loop_run_inv_def]
QED

Theorem abi_static_loop_run_step:
  !ctx func id var_base labels dst src info abi_sz mem_sz len_op initial
      dst_addr src_addr counter_addr n header_bb body_bb i current_state.
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_static_loop_header id var_base labels len_op /\
    lookup_block (fresh_label_output "enc_dyn_body" (labels + 1)) func.fn_blocks = SOME body_bb /\
    body_bb.bb_instructions = abi_static_loop_body id var_base labels dst src info abi_sz mem_sz /\
    eval_operand dst initial = SOME dst_addr /\ eval_operand src initial = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) initial = SOME counter_addr /\
    eval_operand len_op initial = SOME (n2w n) /\ n < dimword(:256) /\ i < n /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_iteration_names var_base info) /\
    abi_static_loop_run_inv var_base labels dst_addr src_addr info abi_sz mem_sz
      counter_addr initial i current_state ==>
    ?out. fragment_path ctx func current_state out /\
      abi_static_loop_run_inv var_base labels dst_addr src_addr info abi_sz mem_sz
        counter_addr initial (SUC i) out
Proof
  rpt gen_tac >> strip_tac >>
  `i < dimword(:256)` by decide_tac >>
  `EVERY (\name. src <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. dst <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. len_op <> Var name) (abi_static_loop_iteration_names var_base info)` by
    fs[EVERY_CONJ] >>
  fs[abi_static_loop_run_inv_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `dst`, `src`, `info`,
    `abi_sz`, `mem_sz`, `current_state`, `dst_addr`, `src_addr`, `counter_addr`,
    `len_op`, `n2w n:bytes32`, `header_bb`, `body_bb`] abi_static_loop_iteration_path) >>
  impl_tac >- simp[w2n_n2w] >> strip_tac >>
  rename1 `fragment_path ctx func current_state next_state` >>
  `next_state with vs_vars := current_state.vs_vars =
    abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels
      current_state` by simp[abi_static_loop_effect_def] >>
  drule_all abi_static_loop_snapshot_step >> DISCH_TAC >>
  qexists_tac `next_state` >> simp[word_add_n2w, ADD1]
QED

Theorem abi_static_loop_run:
  !ctx func id var_base labels dst src info abi_sz mem_sz len_op ss
      dst_addr src_addr counter_addr n header_bb body_bb.
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_static_loop_header id var_base labels len_op /\
    lookup_block (fresh_label_output "enc_dyn_body" (labels + 1)) func.fn_blocks = SOME body_bb /\
    body_bb.bb_instructions = abi_static_loop_body id var_base labels dst src info abi_sz mem_sz /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\ ss.vs_inst_idx = 0 /\
    ~ss.vs_halted /\ mload (w2n counter_addr) ss = 0w /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME (n2w n) /\ n < dimword(:256) /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_iteration_names var_base info) ==>
    ?out. fragment_path ctx func ss out /\
      abi_static_loop_run_inv var_base labels dst_addr src_addr info abi_sz mem_sz
        counter_addr ss n out
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`n`, `ctx`, `func`,
    `abi_static_loop_run_inv var_base labels dst_addr src_addr info abi_sz mem_sz
       counter_addr ss`, `ss`] fragment_path_loop) >>
  impl_tac
  >- (conj_tac >- (irule abi_static_loop_run_inv_initial >> simp[]) >>
      MAP_EVERY qx_gen_tac [`i`, `current_state`] >> strip_tac >>
      mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `dst`, `src`, `info`,
        `abi_sz`, `mem_sz`, `len_op`, `ss`, `dst_addr`, `src_addr`, `counter_addr`,
        `n`, `header_bb`, `body_bb`, `i`, `current_state`] abi_static_loop_run_step) >> simp[]) >>
  simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop run theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopRun")
