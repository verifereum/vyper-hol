(* Saved-object acceptance gate for TASK064. This inspects kernel objects,
   not source proof strings or tag-only heuristics. E is owned by TASK063:
   remaining fixture hypotheses must be exactly members of its current
   expression package. Typed-copy hypotheses, cheats, and axioms are forbidden.
   This file neither evaluates bytecode nor registers parity rewrite rules. *)
Theory typedCopyAcceptance
Ancestors
  typedCopyAgreement typedCopyProducer typedCopyMetadata typedCopyDomain
  typedCopyCounterexample context exprLowering evalCompilerBytecodeParity
  compileVyper

fun ordinary_kernel_tag th =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in null axioms andalso List.all (fn s => s = "DISK_THM") oracles end;

fun check_closed_export (name, th) =
  if null (Thm.hyp th) andalso ordinary_kernel_tag th then ()
  else raise Fail ("TASK064 export is not closed/unadmitted: " ^ name);

val () = List.app check_closed_export
  [("context.compile_store_memory_typed_def", compile_store_memory_typed_def),
   ("context.compile_store_memory_typed_ind", compile_store_memory_typed_ind)];

val () = List.app (fn thy =>
  List.app (fn (name,th) => check_closed_export (thy ^ "." ^ name,th))
    (DB.theorems thy @ DB.definitions thy))
  ["typedCopyDomain", "typedCopyMetadata", "typedCopyProducer",
   "typedCopyCounterexample", "typedCopyAgreement"];

(* The seven helper clauses remain literally the frozen original clauses.
   Only the false unrestricted store clause receives the new invalid-domain
   boundary. The valid store dispatch is proved in typedCopyAgreement. *)
val frozen_original = boolSyntax.rhs (Thm.concl typed_eqs_def);
val frozen_helpers = tl (boolSyntax.strip_conj frozen_original);
val current_helpers = tl (boolSyntax.strip_conj
  (Thm.concl compile_store_memory_typed_def));
val () = if length frozen_helpers = 7 andalso length current_helpers = 7 andalso
  ListPair.allEq (fn (a,b) => Term.aconv a b) (frozen_helpers,current_helpers) then ()
  else raise Fail "TASK064 changed an original typed-copy helper clause";

val expression_hypotheses = Thm.hyp compile_expr_component_eq;
fun expression_hypothesis h =
  List.exists (fn e => Term.aconv h e) expression_hypotheses;

val saved_objects = List.concat (map (fn thy =>
  map (fn (name,th) => (thy ^ "." ^ name,th)) (DB.theorems thy))
  (Theory.ancestry "-"));
val full_parity_objects = List.filter (fn (name,th) =>
  String.isSuffix "_matches_python_oracle" name andalso
  boolSyntax.is_eq (Thm.concl th) andalso
  Term.same_const (fst (strip_comb (boolSyntax.lhs (Thm.concl th))))
    ``compile_vyper``) saved_objects;

val () = if length full_parity_objects = 101 then ()
  else raise Fail "TASK064 acceptance did not find exactly 101 full bytecode claims";
val () = List.app (fn (name,th) =>
  if ordinary_kernel_tag th andalso
     List.all expression_hypothesis (Thm.hyp th) then ()
  else raise Fail ("TASK064 parity contains C/foreign hypotheses or admission: " ^ name))
  full_parity_objects;
val () = print ("TASK064_ACCEPTANCE: owner C=0; all new exports hyp=0; " ^
  "seven original helper clauses unchanged; parity=101, C=0, E-only; closed=" ^
  Int.toString (length (List.filter (fn (_,th) => null (Thm.hyp th)) full_parity_objects)) ^
  "; E owner hypotheses=" ^ Int.toString (length expression_hypotheses) ^ "\n");
