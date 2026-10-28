Theory vyperTestLibTest
Libs vyperTestLib

fun source code = JSON.OBJECT [("source_code", JSON.STRING code)];

fun expect label expected jsons =
  if unsupported_source_reason_for jsons = expected then ()
  else raise Fail ("source classification: " ^ label);

val _ = expect "calldata len" NONE [source "return len(msg.data)"];
val _ = expect "calldata slice" NONE [source "return slice(msg.data, 0, 4)"];
val _ = expect "calldata raw_call" NONE
  [source "raw_call(target, msg.data, max_outsize=32)"];
val _ = expect "gas retained" (SOME "unsupported source pattern: msg.gas")
  [source "raw_call(target, msg.data, gas=msg.gas)"];
val _ = expect "explicit gas retained" (SOME "unsupported source pattern: gas=")
  [source "raw_call(target, msg.data, gas=1000)"];
val _ = expect "negative missing source" (SOME "missing source_code") [];
val _ = expect "blank source" (SOME "blank source_code") [source " \n"];

(* ===== Bounded theory partitions ===== *)

fun check label condition =
  if condition then () else raise Fail ("test partition: " ^ label);

fun check_partition_size n = let
  val indices = List.tabulate (n, fn i => i)
  val batches = partition_indexed test_batch_size indices
in
  check ("exact indices " ^ Int.toString n)
    (List.concat batches = List.map (fn i => (i,i)) indices);
  check "bounded nonempty batches"
    (List.all (fn batch => not (List.null batch) andalso
                           List.length batch <= test_batch_size) batches)
end;

val _ = List.app check_partition_size [0,1,99,100,101,200,739];
val _ = check "739 batch lengths"
  (List.map List.length (partition_indexed test_batch_size
     (List.tabulate (739, fn i => i))) = [100,100,100,100,100,100,100,39]);
val _ = check "reject zero batch size"
  ((partition_indexed 0 ([] : int list); false) handle Fail _ => true);
val _ = check "reject negative batch size"
  ((partition_indexed ~1 ([] : int list); false) handle Fail _ => true);

val _ = List.app (fn partition => check "canonical partition accepted"
  (valid_test_partition partition))
  [(1,0,1), (99,0,99), (100,0,100), (101,0,100), (101,100,1),
   (200,100,100), (739,0,100), (739,600,100), (739,700,39)];
val _ = List.app (fn partition => check "noncanonical partition rejected"
  (not (valid_test_partition partition)))
  [(0,0,0), (~1,0,1), (100,~100,100), (100,100,1),
   (101,0,99), (101,100,0), (101,100,2), (200,100,99),
   (739,700,1), (739,99,100), (739,700,100), (739,800,1)];

(* Reject a canonical range assigned to the wrong theory before touching JSON
   or defining anything. This test needs no exported files in the root build. *)
val _ = check "canonical range cannot be built under the wrong batch theory"
  ((make_definitions_for_partition
      ("partition_guard", "no-export-needed.json", 100, 100, 739); false)
   handle Fail message =>
     String.isPrefix
       "test partition theory mismatch: expected vyperTestDefs_partition_guard_batch_001, got "
       message);

(* ===== Generated script inventory ===== *)

val inventory_ids = "sample" :: List.tabulate (7, fn i =>
  "sample_batch_" ^ StringCvt.padLeft #"0" 3 (Int.toString (i + 1)));
val inventory_scripts = List.concat (List.map (fn id =>
  ["vyperTestDefs_" ^ id ^ "Script.sml", "vyperTest_" ^ id ^ "Script.sml"])
  inventory_ids);
val final_replay = "vyperTest_sample_batch_007Script.sml";
val final_defs = "vyperTestDefs_sample_batch_007Script.sml";
val _ = check_generated_script_inventory inventory_ids
  (".holbuild" :: "unrelatedScript.sml" :: List.rev inventory_scripts);
fun rejects_inventory entries =
  ((check_generated_script_inventory inventory_ids entries; false)
   handle Fail _ => true);
val _ = check "missing final replay is an error even when its Defs exists"
  (rejects_inventory (List.filter (fn name => name <> final_replay)
     inventory_scripts));
val _ = check "missing final Defs is an error"
  (rejects_inventory (List.filter (fn name => name <> final_defs)
     inventory_scripts));
val _ = check "omitted final batch pair is an error"
  (rejects_inventory (List.filter
     (fn name => name <> final_replay andalso name <> final_defs)
     inventory_scripts));
val _ = check "stale replay is an error"
  (rejects_inventory ("vyperTest_sample_batch_008Script.sml" :: inventory_scripts));
val _ = check "stale Defs is an error"
  (rejects_inventory
     ("vyperTestDefs_sample_batch_008Script.sml" :: inventory_scripts));
val _ = check_generated_script_inventory [] ["unrelatedScript.sml"];

(* Raw marker traces deliberately are not HOL-decodable. Selection/planning
   must not translate ASTs, cache bytes, or decode unrelated partitions. *)
fun item kind deps traces = JSON.OBJECT [
  ("item_type", JSON.STRING kind),
  ("deps", JSON.ARRAY (List.map JSON.STRING deps)),
  ("traces", JSON.ARRAY (List.map JSON.STRING traces))];

val fixture_a = JSON.OBJECT [
  ("item_type", JSON.STRING "fixture"),
  ("source_code", JSON.STRING "@external\ndef setup():\n    pass"),
  ("traces", JSON.ARRAY [JSON.STRING "deploy A", JSON.STRING "call A"])];
val fixture_b = item "fixture" [] ["deploy B", "set balance B"];
fun test_item i = item "test" ["export.json/b", "export.json/a"]
  ["deploy test " ^ Int.toString i, "call test " ^ Int.toString i];
val test_items = List.tabulate (739, fn i =>
  ("fixture_test_" ^ Int.toString i, test_item i));
val fixture_inputs = select_test_inputs
  (("a",fixture_a) :: test_items @ [("b",fixture_b)]);
val fixture_batches = partition_indexed test_batch_size fixture_inputs;

(* JSON.value contains real and is not an equality type. All synthetic input
   nodes are objects/arrays/strings; compare their complete structure. *)
fun same_json (JSON.STRING x, JSON.STRING y) = x = y
  | same_json (JSON.ARRAY xs, JSON.ARRAY ys) = ListPair.allEq same_json (xs,ys)
  | same_json (JSON.OBJECT xs, JSON.OBJECT ys) = ListPair.allEq
      (fn ((k,x),(l,y)) => k = l andalso same_json (x,y)) (xs,ys)
  | same_json _ = false;
fun same_input ((i,(name,jsons)),(j,(name',jsons'))) =
  i = j andalso name = name' andalso ListPair.allEq same_json (jsons,jsons');
val expected_fixture_inputs = List.tabulate (739, fn i =>
  (i, ("fixture_test_" ^ Int.toString (738 - i),
       [fixture_b, fixture_a, test_item (738 - i)])));
val _ = check "all fixture-expanded inputs exactly once, in global index order"
  (ListPair.allEq same_input
     (List.concat fixture_batches, expected_fixture_inputs));
val _ = check "fixture batches remain bounded"
  (List.map List.length fixture_batches = [100,100,100,100,100,100,100,39]);
val _ = check "unresolved fixture is an error, never a dropped test"
  ((select_test_inputs [("broken", test_item 0)]; false) handle Fail _ => true);
