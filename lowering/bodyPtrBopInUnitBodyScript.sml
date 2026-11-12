Theory bodyPtrBopInUnitBody
Ancestors
  bodyPtrBopInUnitMetadata moduleLowering stmtLowering emitHelper

(* The exact package environment and body action are named to cache separate
   compiler stages, without inventing an alternative runtime context. *)
Definition equality_package_cenv_def:
  equality_package_cenv =
    case equality_external_package of
    (lbl,ce,argv,min_cds,pay,nr,nkey,trans,isview,stmts,rty) => ce
End

Definition equality_external_body_def:
  equality_external_body = compile_external_function_body
    equality_package_cenv [] F 0 F T
    [Return (SOME equality_fixture)] (SOME (BaseT BoolT))
End

Theorem equality_body_opcodes:
  (case equality_external_body empty_compile_fixture of
   (u,st) => MAP (\i. i.inst_opcode) st.cs_current_insts =
    [ALLOCA; MSTORE; ADD; MSTORE; MLOAD; ALLOCA; MSTORE; ADD;
     MSTORE; MLOAD; EQ; ALLOCA; MSTORE; RETURN])
Proof
  EVAL_TAC
QED

(* A symbolic selector prevents irrelevant Keccak computation in code probes. *)
Definition equality_dispatch_state_def:
  equality_dispatch_state sel = SND
    (compile_selector_dispatch_linear [(sel,"fn_probe")] (fresh_label_output "fallback" 0)
      ((initial_compile_state "__entry") with cs_next_label := 1))
End

Definition equality_bodies_state_def:
  equality_bodies_state sel = SND
    (compile_external_fn_bodies [equality_external_package]
      (equality_dispatch_state sel))
End

Theorem equality_dispatch_counters:
  (equality_dispatch_state sel).cs_next_var = 6 /\
  (equality_dispatch_state sel).cs_next_id = 10 /\
  (equality_dispatch_state sel).cs_next_label = 4
Proof
  EVAL_TAC
QED

Theorem equality_bodies_boundary:
  (equality_bodies_state sel).cs_current_bb = "fn_probe" /\
  (equality_bodies_state sel).cs_next_var = 16 /\
  (equality_bodies_state sel).cs_next_id = 27 /\
  MAP (\i. (i.inst_id,i.inst_opcode,i.inst_operands,i.inst_outputs))
    (FILTER (\i. i.inst_opcode = EQ)
      (equality_bodies_state sel).cs_current_insts) = [(23,EQ,[Var "%10"; Var "%13"],["%14"])]
Proof
  EVAL_TAC
QED
