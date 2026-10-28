structure sourceModuleLoaderLib :> sourceModuleLoaderLib = struct
open HolKernel boolLib bossLib JSONDecode sourceModuleDefsTheory

type loaded = {program:term, keys:term, nonreentrant_defaults:term,
               declaration_only:term, provenance:JSON.value}
fun required key decoder = andThen (sourceConstASTLib.optional_field key decoder)
  (fn SOME value => succeed value | NONE => fail ("source loader: missing " ^ key))
fun claim key expected = andThen (required key string) (fn actual =>
  if actual = expected then succeed () else fail ("source loader protocol: " ^ key))
fun strings xs = listSyntax.mk_list (List.map stringSyntax.fromMLstring xs,stringSyntax.string_ty)
fun flags xs = listSyntax.mk_list (List.map (fn b => if b then boolSyntax.T else boolSyntax.F) xs,
                                 type_of boolSyntax.T)
val source_capture = andThen (tuple3
  (claim "protocol" "vyper-hol/source-loader-v1",
   claim "phase" "annotate_python_ast-before-get_node",
   claim "vyper_pin" "cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c")) (fn _ =>
  andThen (tuple4 (required "keys" (array (array string)),
    required "nonreentrancy_by_default" (array bool),
    required "declaration_only" (array bool),
    tuple2 (required "annotated_ast" sourceSyntaxLib.annotated_ast,required "provenance" raw)))
  (fn (keys,nr,interfaces,(program,provenance)) =>
    if List.null keys orelse length nr <> length keys orelse length interfaces <> length keys orelse
       List.exists List.null keys orelse List.exists (List.exists (fn s => s = "")) keys then
      fail "source loader: incomplete namespace/policy registry"
    else succeed {program=program,
      keys=listSyntax.mk_list (List.map strings keys,type_of (strings [])),
      nonreentrant_defaults=flags nr,declaration_only=flags interfaces,provenance=provenance}));
(* Revalidate even hand-built ML artifacts. No policy is inferred from paths,
   bodies, compiler flags or provenance, and no incomplete list is truncated. *)
fun policies ({keys,nonreentrant_defaults,declaration_only,...}:loaded) = let
  val (ks,key_ty) = listSyntax.dest_list keys
  val (nr,_) = listSyntax.dest_list nonreentrant_defaults
  val (decl,_) = listSyntax.dest_list declaration_only
  val () = if length ks = length nr andalso length ks = length decl then ()
    else raise mk_HOL_ERR "sourceModuleLoaderLib" "policies" "policy registry length"
  fun entry (key,(n,d)) = pairSyntax.mk_pair (key,
    list_mk_comb (prim_mk_const {Thy="sourceModuleDefs",Name="SourceModulePolicy"},[n,d]))
  val policy_ty = mk_thy_type {Thy="sourceModuleDefs",Tyop="source_module_policy",Args=[]}
in listSyntax.mk_list (List.map entry (ListPair.zip (ks,ListPair.zip (nr,decl))),
     pairSyntax.mk_prod (key_ty,policy_ty)) end
fun load_file path = JSONDecode.decodeFile source_capture path
end
