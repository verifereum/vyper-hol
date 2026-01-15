(*
 * Compiler State Helpers
 *
 * Fresh variable/label/inst-id generation for passes.
 *)

Theory compilerState
Ancestors
  list
  stringUtils irOps

Datatype:
  compiler_state = <|
    cs_next_var : num;
    cs_next_inst_id : num;
    cs_next_label : num
  |>
End

Definition fresh_var_def:
  fresh_var st =
    let v = mk_var_name st.cs_next_var in
    (v, st with cs_next_var := st.cs_next_var + 1)
End

Definition fresh_inst_id_def:
  fresh_inst_id st =
    let i = st.cs_next_inst_id in
    (i, st with cs_next_inst_id := st.cs_next_inst_id + 1)
End

Definition fresh_label_def:
  fresh_label suffix st =
    let l = mk_label_name st.cs_next_label suffix in
    (l, st with cs_next_label := st.cs_next_label + 1)
End

Definition init_state_for_function_def:
  init_state_for_function fn =
    <| cs_next_var := max_var_id_in_function fn + 1;
       cs_next_inst_id := max_inst_id_in_function fn + 1;
       cs_next_label := max_label_id_in_function fn + 1 |>
End

Definition max_var_id_in_context_def:
  max_var_id_in_context ctx =
    FOLDL (λacc fn. MAX acc (max_var_id_in_function fn)) 0 ctx.ctx_functions
End

Definition max_inst_id_in_context_def:
  max_inst_id_in_context ctx =
    FOLDL (λacc fn. MAX acc (max_inst_id_in_function fn)) 0 ctx.ctx_functions
End

Definition max_label_id_in_context_def:
  max_label_id_in_context ctx =
    FOLDL (λacc fn. MAX acc (max_label_id_in_function fn)) 0 ctx.ctx_functions
End

Definition init_state_for_context_def:
  init_state_for_context ctx =
    <| cs_next_var := max_var_id_in_context ctx + 1;
       cs_next_inst_id := max_inst_id_in_context ctx + 1;
       cs_next_label := max_label_id_in_context ctx + 1 |>
End

val _ = export_theory();
