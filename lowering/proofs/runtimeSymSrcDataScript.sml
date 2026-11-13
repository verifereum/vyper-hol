(* Runtime data metadata is independent of instruction packaging. *)
Theory runtimeSymSrcData
Ancestors
  compileVyper vyperCompiler list

Theorem extract_context_with_internals_data:
  extract_context_with_internals entry internal_fns st = SOME (ctx, data) ==>
  data = REVERSE st.cs_data_sections
Proof
  simp[extract_context_with_internals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
