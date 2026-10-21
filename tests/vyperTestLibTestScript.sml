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

fun item_type t = ("item_type", JSON.STRING t);
fun expect_scripts label expected items =
  if generates_scripts items = expected then ()
  else raise Fail ("script generation: " ^ label);

val _ = expect_scripts "selected test" true
  [("t", JSON.OBJECT [item_type "test",
                      ("source_code", JSON.STRING "return 1")])];
val no_deps = ("deps", JSON.ARRAY []);
val no_traces = ("traces", JSON.ARRAY []);
val _ = expect_scripts "no selected test" false
  [("t", JSON.OBJECT [item_type "test", no_deps]),
   ("f", JSON.OBJECT [item_type "fixture", no_traces])];
val _ = expect_scripts "malformed item" true
  [("t", JSON.OBJECT [item_type "test", no_deps]), ("m", JSON.OBJECT [])];
val _ = expect_scripts "unresolved fixture dependency" true
  [("t", JSON.OBJECT [item_type "test",
                      ("deps", JSON.ARRAY [JSON.STRING "missing"])])];
val _ = expect_scripts "excluded test with an unresolved dependency" false
  [("test_ecrecover_oog_handling",
    JSON.OBJECT [item_type "test",
                 ("deps", JSON.ARRAY [JSON.STRING "missing"])])];
val _ = expect_scripts "fixture whose traces fail to decode" true
  [("t", JSON.OBJECT [item_type "test", no_deps]),
   ("f", JSON.OBJECT [item_type "fixture",
                      ("traces", JSON.ARRAY [JSON.STRING "bad"])])];
val _ = expect_scripts "test without deps" true
  [("t", JSON.OBJECT [item_type "test"])];
