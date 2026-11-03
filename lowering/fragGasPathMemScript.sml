(* Counted fragment paths carrying the memory checks of the same steps,
   including callees and the runner's revert-forward exemption. *)
Theory fragGasPathMem
Ancestors
  fragGasPath gasCount fragExec fragExecMem memSafeRun unitTransformDefs
  venomExecSemantics venomExecProofs venomInstProofs venomState arithmetic list

Definition gas_path_mem_edge_def:
  gas_path_mem_edge ctx fn s n r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      n = gas_count_step fuel ctx inst s /\
      (revert_forward_at bb s.vs_inst_idx \/
       mem_safe_step fuel ctx inst s) /\
      ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
            ~t.vs_halted /\
            r = OK (t with vs_inst_idx := SUC s.vs_inst_idx)) \/
       (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
            t.vs_halted /\ r = Halt t) \/
       (?t target entered.
          middle = OK t /\ is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
          eval_phis t target.bb_instructions = OK entered /\
          ~entered.vs_halted /\
          r = OK (entered with vs_inst_idx :=
                    phi_prefix_length target.bb_instructions)) \/
       (exit_result middle /\ r = middle))
End

Inductive gas_path_mem:
  (!ctx fn s.
     ~s.vs_halted ==> gas_path_mem ctx fn s 0 (OK s)) /\
  (!ctx fn s n t m r.
     gas_path_mem_edge ctx fn s n (OK t) /\
     gas_path_mem ctx fn t m r ==>
     gas_path_mem ctx fn s (n + m) r) /\
  (!ctx fn s n r.
     gas_path_mem_edge ctx fn s n r /\ exit_result r ==>
     gas_path_mem ctx fn s n r)
End

Theorem edge_check_mono[local]:
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
  (!e. step_inst a ctx inst s <> Error e) /\ a <= b ==>
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step b ctx inst s)
Proof
  metis_tac[cj 1 mem_safe_fuel_mono_up]
QED

(* A normal landing transfers the existing conditional continuation check;
   a terminal path supplies its own safe run. *)
Theorem gas_path_mem_exec:
  !ctx fn s n r.
    gas_path_mem ctx fn s n r ==>
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ ~t.vs_halted /\
          !fuel out.
            run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
            ?fuel'. run_from fuel' ctx fn s = out /\
                    (mem_safe_run fuel ctx fn t ==>
                     mem_safe_run fuel' ctx fn s)) \/
     (exit_result r /\
      ?fuel. run_from fuel ctx fn s = r /\ mem_safe_run fuel ctx fn s))
Proof
  cheat
QED
