(* A target prefix can stop inside a callee without completing INVOKE.
   Completed segments carry their chosen execution/safety mode; entering a call retains its
   actual decode, setup and first-block PHI evaluation. *)
Theory fragGasFocus
Ancestors
  fragGasMode fragGasPathMem gasCount gasOracleReplay fragExec
  venomExecSemantics venomState list arithmetic

Definition gas_invoke_entry_def:
  gas_invoke_entry (ctx, func) s callee entered <=>
    ~s.vs_halted /\
    ?bb inst name arg_ops args setup first phi_state.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      inst.inst_opcode = INVOKE /\
      decode_invoke inst = SOME (name, arg_ops) /\
      lookup_function name ctx.ctx_functions = SOME callee /\
      eval_operands arg_ops s = SOME args /\
      setup_callee callee args s = SOME setup /\
      lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
      eval_phis setup first.bb_instructions = OK phi_state /\
      ~phi_state.vs_halted /\
      entered = phi_state with vs_inst_idx :=
        phi_prefix_length first.bb_instructions
End

Theorem gas_invoke_entry_readings:
  gas_invoke_entry (ctx, func) s callee entered ==>
  entered.vs_gas_readings = s.vs_gas_readings
Proof
  rw[gas_invoke_entry_def] >>
  drule gas_setup_callee_readings >>
  drule gas_count_phis_ok >> simp[]
QED

Inductive gas_focus_path:
  (!memory ctx func s n t.
     gas_marked_path memory ctx func s n (OK t) ==>
     gas_focus_path memory (ctx, func) s n (func, t)) /\
  (!memory ctx func s n mid m leaf t.
     gas_marked_path memory ctx func s n (OK mid) /\
     gas_focus_path memory (ctx, func) mid m (leaf, t) ==>
     gas_focus_path memory (ctx, func) s (n + m) (leaf, t)) /\
  (!memory ctx func s callee entered n leaf t.
     gas_invoke_entry (ctx, func) s callee entered /\
     gas_focus_path memory (ctx, callee) entered n (leaf, t) ==>
     gas_focus_path memory (ctx, func) s n (leaf, t))
End

(* Counts include all completed segments and the focused callee prefix,
   but never an unexecuted suffix of an enclosing call. *)
Theorem gas_focus_path_suffix:
  !memory ctx func s n leaf t.
    gas_focus_path memory (ctx, func) s n (leaf, t) ==>
    t.vs_gas_readings = DROP n s.vs_gas_readings
Proof
  qsuff_tac
    `!memory p s n q. gas_focus_path memory p s n q ==>
       (SND q).vs_gas_readings = DROP n s.vs_gas_readings`
  >- (strip_tac >> rpt gen_tac >>
      first_x_assum (qspecl_then [`memory`, `(ctx, func)`, `s`, `n`, `(leaf, t)`] mp_tac) >>
      simp[]) >>
  ho_match_mp_tac gas_focus_path_ind >> rpt conj_tac
  >- (simp[] >> metis_tac[gas_marked_path_ok_suffix])
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      drule gas_marked_path_ok_suffix >>
      simp[rich_listTheory.DROP_DROP_T, ADD_COMM]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  drule gas_invoke_entry_readings >> simp[]
QED
