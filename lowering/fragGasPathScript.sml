(* Actual finite fragment paths with counts of all executed GAS instructions.
   Source-level explicit readings are selected by the lowering proofs. *)
Theory fragGasPath
Ancestors
  gasCount fragExec venomExecSemantics venomExecProofs venomState arithmetic list

Definition gas_path_edge_def:
  gas_path_edge ctx fn s n r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      n = gas_count_step fuel ctx inst s /\
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

Inductive gas_path:
  (!ctx fn s.
     ~s.vs_halted ==> gas_path ctx fn s 0 (OK s)) /\
  (!ctx fn s n t m r.
     gas_path_edge ctx fn s n (OK t) /\
     gas_path ctx fn t m r ==>
     gas_path ctx fn s (n + m) r) /\
  (!ctx fn s n r.
     gas_path_edge ctx fn s n r /\ exit_result r ==>
     gas_path ctx fn s n r)
End

Theorem gas_path_suffix:
  gas_path ctx fn s n r ==> gas_count_suffix n s r
Proof
  cheat
QED

Theorem gas_path_normal:
  gas_path ctx fn s n (OK t) ==>
  ~t.vs_halted /\
  !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r
Proof
  cheat
QED

Theorem gas_path_exit:
  gas_path ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r
Proof
  cheat
QED

Theorem gas_path_then:
  gas_path ctx fn s n (OK t) /\ gas_path ctx fn t m r ==>
  gas_path ctx fn s (n + m) r
Proof
  cheat
QED
