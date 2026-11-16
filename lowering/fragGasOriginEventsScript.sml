(* A source focus may stop inside INVOKE, before a terminal result exists. *)
Theory fragGasOriginEvents
Ancestors
  fragGasOrigin fragGasFocus fragExec gasEvents gasEventsFuel
  venomExecSemantics venomExecProofs venomInst venomInstProofs
  venomState list rich_list arithmetic pred_set

Theorem gas_invoke_entry_events_prefix:
  gas_invoke_entry (ctx,func) s callee entered ==>
  ?extra.
    (case lookup_block s.vs_current_bb func.fn_blocks of
       NONE => []
     | SOME bb =>
         gas_events_block (SUC n) ctx func.fn_name bb s ++
         case exec_block (SUC n) ctx bb s of
           OK u => if u.vs_halted then []
                   else gas_events_blocks (SUC n) ctx func u
         | _ => []) =
    (case lookup_block entered.vs_current_bb callee.fn_blocks of
       NONE => []
     | SOME bb =>
         gas_events_block n ctx callee.fn_name bb entered ++
         case exec_block n ctx bb entered of
           OK u => if u.vs_halted then []
                   else gas_events_blocks n ctx callee u
         | _ => []) ++ extra
Proof
  rw[gas_invoke_entry_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[] >>
  CONV_TAC (BINDER_CONV (LHS_CONV
    (ONCE_DEPTH_CONV (REWR_CONV gas_events_block_def)))) >>
  simp[gas_events_step_def, Once gas_events_blocks_def] >>
  simp[APPEND_ASSOC]
QED

Theorem gas_origin_focus_events_prefix:
  !memory explicit ctx func s marks leaf t.
    gas_origin_focus memory explicit (ctx,func) s marks (leaf,t) ==>
    ?fuel extra.
      MAP (\key. key IN explicit)
        (case lookup_block s.vs_current_bb func.fn_blocks of
           NONE => []
         | SOME bb =>
             gas_events_block fuel ctx func.fn_name bb s ++
             case exec_block fuel ctx bb s of
               OK u => if u.vs_halted then []
                       else gas_events_blocks fuel ctx func u
             | _ => []) = marks ++ extra
Proof
  (* Local proof target; removed by the origin-prefix proof task. *)
  cheat
QED
