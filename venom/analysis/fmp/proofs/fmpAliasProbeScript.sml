(* Production capture/escape queries, not the parameterized stack reference. *)
Theory fmpAliasProbe
Ancestors
  fmpAliasProps

Theorem fmp_escape_store_occurrences:
  fmp_escaping_operands (mk_inst 0 MSTORE [Var "p"; Var "p"] []) = ["p";"p"] /\
  fmp_escaping_operands (mk_inst 0 MSTORE [Var "p"; Lit 0w] []) = [] /\
  fmp_escaping_operands (mk_inst 0 MLOAD [Var "p"] ["x"]) = []
Proof
  EVAL_TAC
QED

Theorem fmp_escape_call_create_positions:
  fmp_escaping_operands (mk_inst 0 CALL
    [Lit 100w; Lit 1w; Lit 0w; Var "p"; Var "n"; Var "q"; Var "m"] ["ok"]) = [] /\
  fmp_escaping_operands (mk_inst 0 CREATE
    [Lit 0w; Var "p"; Var "n"] ["addr"]) = [] /\
  fmp_escaping_operands (mk_inst 0 CREATE2
    [Lit 0w; Var "p"; Var "n"; Var "salt"] ["addr"]) = ["salt"]
Proof
  EVAL_TAC
QED

Theorem fmp_capture_loop_closure:
  fmp_capture_closure
    [mk_inst 0 PHI [Label "entry"; Var "cap"; Label "loop"; Var "back"] ["head"];
     mk_inst 1 ASSIGN [Var "tail"] ["back"];
     mk_inst 2 SUB [Var "cap"; Var "offset"] ["tail"]] "cap" =
       SOME ["tail";"back";"head";"cap"]
Proof
  EVAL_TAC
QED

Theorem fmp_capture_single_output_only:
  fmp_capture_closure
    [mk_inst 0 ADD [Var "cap"; Lit 32w] ["x";"y"];
     mk_inst 1 BUMP [Var "cap"; Lit 32w] ["ptr";"fmp"]] "cap" = SOME ["cap"]
Proof
  EVAL_TAC
QED

Theorem fmp_live_derived_capture_veto:
  fmp_capture_query_veto
    [mk_inst 0 ASSIGN [Var "back"] ["head"];
     mk_inst 1 ADD [Var "cap"; Lit 32w] ["back"]] ["head"] "cap" /\
  ~fmp_capture_query_veto
    [mk_inst 0 ADD [Var "cap"; Lit 32w] ["back"];
     mk_inst 1 MLOAD [Var "back"] ["value"]] [] "cap" /\
  fmp_capture_query_veto
    [mk_inst 0 ADD [Var "cap"; Lit 32w] ["back"];
     mk_inst 1 MSTORE [Var "back"; Var "back"] []] [] "cap"
Proof
  EVAL_TAC
QED

Definition fmp_alias_fixture_def:
  fmp_alias_fixture =
    [mk_inst 10 DALLOCA [Lit 32w] ["p"];
     mk_inst 11 DALLOCA [Lit 32w] ["q"];
     mk_inst 12 ALLOCA [Lit 32w] ["static"];
     mk_inst 13 BUMP [Var "runner0"; Lit 32w] ["bumped";"runner"];
     mk_inst 14 GETFMP [] ["cap"];
     mk_inst 15 ASSIGN [Var "p"] ["copy"];
     mk_inst 16 ADD [Var "p"; Lit 31w] ["literal"];
     mk_inst 17 ADD [Var "p"; Var "offset"] ["dynamic"];
     mk_inst 18 SUB [Var "p"; Var "offset"] ["sub"];
     mk_inst 19 SUB [Var "offset"; Var "p"] ["reverse_sub"];
     mk_inst 20 ADD [Var "offset"; Var "p"] ["reverse_add"];
     mk_inst 21 ADD [Var "p"; Var "q"] ["two_ptrs"];
     mk_inst 22 PHI [Label "a"; Var "p"; Label "b"; Var "untracked"] ["known_phi"];
     mk_inst 23 PHI [Label "a"; Var "p"; Label "b"; Var "q"] ["ambiguous"]]
End

Theorem fmp_alias_fixture_result:
  fmp_base_analyze fmp_alias_fixture = SOME
    (FEMPTY |++ [("p",[10]);("q",[11]);("static",[12]);("bumped",[13]);
      ("cap",[]);("copy",[10]);("literal",[10]);("dynamic",[10]);
      ("sub",[10]);("reverse_sub",[]);("reverse_add",[10]);
      ("two_ptrs",[]);("known_phi",[10]);("ambiguous",[10;11])])
Proof
  EVAL_TAC
QED

Theorem fmp_alias_production_roots:
  IS_SOME (fmp_base_analyze fmp_alias_fixture) /\
  let env = THE (fmp_base_analyze fmp_alias_fixture) in
    fmp_dalloca_query fmp_alias_fixture env "p" = SOME 10 /\
    fmp_dalloca_query fmp_alias_fixture env "q" = SOME 11 /\
    fmp_bases env "bumped" = [13] /\
    fmp_bases env "runner" = [] /\ fmp_bases env "cap" = [] /\
    fmp_dalloca_query fmp_alias_fixture env "bumped" = NONE /\
    fmp_dalloca_query fmp_alias_fixture env "static" = NONE
Proof
  EVAL_TAC
QED

Theorem fmp_alias_production_arithmetic:
  let env = THE (fmp_base_analyze fmp_alias_fixture) in
    EVERY (\v. fmp_bases env v = [10])
      ["copy";"literal";"dynamic";"sub";"reverse_add";"known_phi"] /\
    fmp_bases env "reverse_sub" = [] /\
    fmp_bases env "two_ptrs" = [] /\
    fmp_bases env "ambiguous" = [10;11] /\
    fmp_dalloca_query fmp_alias_fixture env "ambiguous" = NONE /\
    fmp_dalloca_query fmp_alias_fixture env "untracked" = NONE
Proof
  EVAL_TAC
QED

Theorem fmp_alias_accumulated_negative_test:
  let env = fmp_accumulate_bases FEMPTY "p" [10] in
  let early = fmp_base_transfer
    (mk_inst 0 ADD [Var "p"; Var "later"] ["out"]) env in
  let discovered = fmp_accumulate_bases early "later" [11] in
  fmp_bases (fmp_base_transfer
    (mk_inst 0 ADD [Var "p"; Var "later"] ["out"]) discovered) "out" = [10]
Proof
  EVAL_TAC
QED

Theorem fmp_alias_loop_closes:
  let insts =
    [mk_inst 0 PHI [Label "entry"; Var "p"; Label "loop"; Var "back"] ["head"];
     mk_inst 1 ASSIGN [Var "tail"] ["back"];
     mk_inst 2 ADD [Var "head"; Var "offset"] ["tail"];
     mk_inst 3 DALLOCA [Lit 32w] ["p"]] in
  IS_SOME (fmp_base_analyze insts) /\
  EVERY (\v. fmp_bases (THE (fmp_base_analyze insts)) v = [3])
    ["p";"head";"tail";"back"]
Proof
  EVAL_TAC
QED

Theorem fmp_alias_liveness_and_pinning:
  let insts = fmp_alias_fixture ++
    [mk_inst 24 MSTORE [Var "q"; Var "q"] []] in
  let env = THE (fmp_base_analyze insts) in
  IS_SOME (fmp_base_analyze insts) /\
  fmp_allocation_live env insts ["dynamic"] 10 /\
  fmp_allocation_live env insts [] 11 /\
  ~fmp_allocation_live env insts [] 10
Proof
  EVAL_TAC
QED

Theorem fmp_alias_repeated_site_rejected:
  fmp_base_analyze
    [mk_inst 0 DALLOCA [Lit 32w] ["p"];
     mk_inst 0 DALLOCA [Lit 32w] ["q"]] = NONE
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpAliasProbe");
