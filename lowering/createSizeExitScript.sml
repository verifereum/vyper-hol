Theory createSizeExit
Ancestors
  venomExecSemantics venomInst venomState vfmConstants
  vyperInterpreter vyperState words
  venomExecProps[qualified] venomFnInstsProofs[qualified]

(* The abort retains the instruction cursor and its size operand. *)
Definition oversized_create_abort_def:
  oversized_create_abort ctx r <=>
    ?s fn bb inst v off sz salt sz_w.
      r = Abort ExHalt_abort s /\ ~s.vs_call_ctx.cc_static /\
      MEM fn ctx.ctx_functions /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      ((inst.inst_opcode = CREATE /\ inst.inst_operands = [v;off;sz]) \/
       (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v;off;sz;salt])) /\
      eval_operand sz s = SOME sz_w /\ 2 * max_code_size < w2n sz_w
End

Definition create_size_exit_ok_def:
  create_size_exit_ok ctx res r <=>
    (ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) /\
     oversized_create_abort ctx r ==>
     res = INR (Error (RuntimeError "create initcode too large")))
End

Theorem oversized_create_abort_at_state[local]:
  ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) /\
  MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  oversized_create_abort ctx (Abort ExHalt_abort s) ==>
  ?v off sz salt sz_w.
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [v;off;sz]) \/
     (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v;off;sz;salt])) /\
    eval_operand sz s = SOME sz_w /\ 2 * max_code_size < w2n sz_w
Proof
  simp[oversized_create_abort_def] >>
  rpt strip_tac >>
  rename1 `MEM candidate ctx.ctx_functions` >>
  `!f b. lookup_block s.vs_current_bb f.fn_blocks = SOME b ==>
     MEM s.vs_current_bb (fn_labels f)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label]) >>
  `candidate = fn` by
    metis_tac[venomFnInstsProofsTheory.all_distinct_flat_map_unique] >>
  gvs[] >> qexists_tac `sz_w` >> simp[]
QED

Theorem eval_operand_halt_returndata[local]:
  eval_operand op (halt_state (set_returndata [] s)) = eval_operand op s
Proof
  Cases_on `op` >> simp[halt_state_def, set_returndata_def, eval_operand_def, lookup_var_def]
QED

Theorem oversized_create_abort_at_cursor:
  ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) /\
  MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  oversized_create_abort ctx (Abort ExHalt_abort (halt_state (set_returndata [] s))) ==>
  ?v off sz salt sz_w.
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [v;off;sz]) \/
     (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v;off;sz;salt])) /\
    eval_operand sz s = SOME sz_w /\ 2 * max_code_size < w2n sz_w
Proof
  strip_tac >>
  mp_tac (Q.INST [`s` |-> `halt_state (set_returndata [] s)`]
    (SPEC_ALL oversized_create_abort_at_state)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                simp[halt_state_def, set_returndata_def])) >>
  simp[eval_operand_halt_returndata]
QED

Theorem oversized_create_abort_non_create_cursor:
  ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) /\
  MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2 ==>
  ~oversized_create_abort ctx (Abort a s)
Proof
  strip_tac >> Cases_on `a` >>
  TRY (simp[oversized_create_abort_def] >> NO_TAC) >>
  strip_tac >> drule_all oversized_create_abort_at_state >> simp[]
QED

Theorem oversized_create_abort_non_exhalt[simp]:
  ~oversized_create_abort ctx (Abort Revert_abort s) /\
  ~oversized_create_abort ctx (Halt s) /\
  ~oversized_create_abort ctx (IntRet vs s)
Proof
  simp[oversized_create_abort_def]
QED

Theorem oversized_create_abort_static[simp]:
  s.vs_call_ctx.cc_static ==> ~oversized_create_abort ctx (Abort ExHalt_abort s)
Proof
  simp[oversized_create_abort_def]
QED

Theorem create_size_exit_ok_inr[simp]:
  create_size_exit_ok ctx (INR exc) r <=>
    (ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) /\
     oversized_create_abort ctx r ==>
     exc = Error (RuntimeError "create initcode too large"))
Proof
  simp[create_size_exit_ok_def]
QED

Theorem create_size_exit_ok_non_exhalt[simp]:
  create_size_exit_ok ctx res (Abort Revert_abort s) /\
  create_size_exit_ok ctx res (Halt s) /\
  create_size_exit_ok ctx res (IntRet vs s)
Proof
  simp[create_size_exit_ok_def]
QED

Theorem create_size_exit_ok_static[simp]:
  s.vs_call_ctx.cc_static ==>
  create_size_exit_ok ctx res (Abort ExHalt_abort s)
Proof
  simp[create_size_exit_ok_def]
QED

Theorem create_size_exit_ok_map:
  (!exc. f (INR exc) = INR exc) /\ create_size_exit_ok ctx res r ==>
  create_size_exit_ok ctx (f res) r
Proof
  simp[create_size_exit_ok_def] >> metis_tac[]
QED
