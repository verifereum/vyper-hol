Theory asmFinalizerPrefixPeepWindow
Ancestors
  asmSplice asmSymPc asmSymSem asmOptimizer asmSem arithmetic list

Overload asm_peep_window_with_target_bound[inferior] = ``\pre pat repl post D E.
  !env u. u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        !op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                 "CREATE2"} /\
          a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
          EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp op ==>
          i = 0 /\ repl <> [] /\ HD repl = HD pat) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. e <= E /\ sym_steps (pre ++ repl ++ post) env e u =
          SymOK (sym_with_pc
            (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a) /\
          (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
          (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc))``
