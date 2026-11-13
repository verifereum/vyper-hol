(* Complete checked publication of the ordinary evaluator branch family. *)
Theory guardSourceOrdinary
Ancestors
  guardSourceOrdinarySchema guardSourceOrdinaryLists guardSourceOrdinaryValues
  guardSourceOrdinaryWrites
Libs
  guardSourceSchemaLib

(* Audit actual exports, not just a hand-maintained list of expected names. *)
val prefix = "finite_prefix_";
fun exports thy =
  map (fn (name,th) => (String.extract(name,size prefix,NONE),th))
    (List.filter (fn (name,_) => String.isPrefix prefix name) (DB.thms thy));
val manifest = guardSourceSchemaLib.manifest finite_prefix_evaluate_ind;
fun audit description expected actual =
  let
    val _ = if length expected = length actual andalso
               length (mk_set (map #1 actual)) = length actual
            then () else raise Fail (description ^ " coverage/uniqueness mismatch")
    val _ = List.app (fn (name,tm) =>
      case List.find (fn (n,_) => n = name) actual of
        SOME (_,th) => if aconv (concl th) tm then ()
                       else raise Fail (description ^ " statement mismatch: " ^ name)
      | NONE => raise Fail (description ^ " missing branch: " ^ name)) expected
  in () end;
val values_exports = exports "guardSourceOrdinaryValues";
val _ = audit "Values"
  (List.filter (fn (name,_) => guardSourceSchemaLib.owner name = "values") manifest)
  values_exports;
val ordinary_exports = values_exports @
  List.concat (map exports
    ["guardSourceOrdinaryLists", "guardSourceOrdinaryConditionals",
     "guardSourceOrdinaryLoops", "guardSourceOrdinaryWrites"]);
val ordinary_expected = List.filter
  (fn (name,_) => guardSourceSchemaLib.owner name <> "calls") manifest;
val _ = audit "Ordinary" ordinary_expected ordinary_exports;
val ordinary_ordered = map (fn (name,_) =>
  #2 (valOf (List.find (fn (n,_) => n = name) ordinary_exports))) ordinary_expected;

Theorem finite_prefix_ordinary_branches:
  ^(list_mk_conj (map #2 ordinary_expected))
Proof
  map_every (fn th => conj_tac >- ACCEPT_TAC th)
    (List.take(ordinary_ordered,length ordinary_ordered - 1)) >>
  ACCEPT_TAC (List.last ordinary_ordered)
QED
