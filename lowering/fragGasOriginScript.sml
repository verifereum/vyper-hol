(* Prefix marks are fixed by raw compilation's explicit GAS sites.
   The recorder and memory check use the very same instruction fuel. *)
Theory fragGasOrigin
Ancestors
  gasEvents gasCount fragGasMode fragGasPath fragGasPathMem fragGasFocus
  fragExec fragExecMem memSafeRun unitTransformDefs
  venomExecSemantics venomInst venomState list arithmetic pred_set

Definition gas_origin_edge_def:
  gas_origin_edge memory explicit ctx func s marks r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      marks = MAP (\key. key IN explicit)
        (gas_events_step fuel ctx func.fn_name inst s) /\
      (memory ==> revert_forward_at bb s.vs_inst_idx \/
                  mem_safe_step fuel ctx inst s) /\
      ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
            ~t.vs_halted /\
            r = OK (t with vs_inst_idx := SUC s.vs_inst_idx)) \/
       (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
            t.vs_halted /\ r = Halt t) \/
       (?t target entered.
          middle = OK t /\ is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          lookup_block t.vs_current_bb func.fn_blocks = SOME target /\
          eval_phis t target.bb_instructions = OK entered /\
          ~entered.vs_halted /\
          r = OK (entered with vs_inst_idx :=
                    phi_prefix_length target.bb_instructions)) \/
       (?lbl. is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
              middle = OK (jump_to lbl s) /\ r = middle) \/
       (exit_result middle /\ r = middle))
End

Inductive gas_origin_path:
  (!memory explicit ctx func s.
     ~s.vs_halted ==>
     gas_origin_path memory explicit ctx func s [] (OK s)) /\
  (!memory explicit ctx func s left mid right r.
     gas_origin_edge memory explicit ctx func s left (OK mid) /\
     gas_origin_path memory explicit ctx func mid right r ==>
     gas_origin_path memory explicit ctx func s (left ++ right) r) /\
  (!memory explicit ctx func s marks r.
     gas_origin_edge memory explicit ctx func s marks r /\
     exit_result r ==>
     gas_origin_path memory explicit ctx func s marks r)
End

Inductive gas_origin_focus:
  (!memory explicit ctx func s marks t.
     gas_origin_path memory explicit ctx func s marks (OK t) ==>
     gas_origin_focus memory explicit (ctx,func) s marks (func,t)) /\
  (!memory explicit ctx func s left mid right leaf t.
     gas_origin_path memory explicit ctx func s left (OK mid) /\
     gas_origin_focus memory explicit (ctx,func) mid right (leaf,t) ==>
     gas_origin_focus memory explicit (ctx,func) s (left ++ right) (leaf,t)) /\
  (!memory explicit ctx func s callee entered marks leaf t.
     gas_invoke_entry (ctx,func) s callee entered /\
     gas_origin_focus memory explicit (ctx,callee) entered marks (leaf,t) ==>
     gas_origin_focus memory explicit (ctx,func) s marks (leaf,t))
End

Theorem gas_origin_edge_erase:
  gas_origin_edge memory explicit ctx func s marks r ==>
  gas_path_edge ctx func s (LENGTH marks) r /\
  (memory ==> gas_path_mem_edge ctx func s (LENGTH marks) r)
Proof
  rewrite_tac[gas_origin_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (qx_choose_then `fuel` (qx_choose_then `bb`
    (qx_choose_then `inst` (qx_choose_then `middle` mp_tac)))) >>
  ntac 5 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_tac >>
  `LENGTH marks = gas_count_step fuel ctx inst s` by
    simp[gas_events_length] >>
  (conj_tac
   >- (rewrite_tac[gas_path_edge_def] >> conj_tac >- simp[] >>
       map_every qexists_tac [`fuel`, `bb`, `inst`, `middle`] >>
       gvs[] >> metis_tac[]) >>
   strip_tac >> rewrite_tac[gas_path_mem_edge_def] >>
   conj_tac >- simp[] >>
   map_every qexists_tac [`fuel`, `bb`, `inst`, `middle`] >>
   gvs[] >> metis_tac[])
QED

Theorem gas_origin_path_erase:
  !memory explicit ctx func s marks r.
    gas_origin_path memory explicit ctx func s marks r ==>
    gas_marked_path memory ctx func s (LENGTH marks) r
Proof
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `memory` >> gvs[gas_marked_path_def, LENGTH_APPEND] >>
  metis_tac[gas_origin_edge_erase, gas_path_rules, gas_path_mem_rules]
QED

Theorem gas_origin_focus_erase:
  !memory explicit p s marks q.
    gas_origin_focus memory explicit p s marks q ==>
    gas_focus_path memory p s (LENGTH marks) q
Proof
  ho_match_mp_tac gas_origin_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[LENGTH_APPEND] >>
  metis_tac[gas_origin_path_erase, gas_focus_path_rules]
QED
