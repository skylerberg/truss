(* Fuzzing the code database's engine. This is a tool, not a test: run it by
   hand to look for a sequence of changes after which the engine holds a
   result that a new engine would not compute, and turn each one it finds
   into a focused test. See IMPLEMENTATION.md, "Testing", and DATABASE.md,
   "Checking the engine".

     dune exec stage0/tools/engine_fuzz/engine_fuzz.exe -- [--seed N] [--count N] [--steps N]

   Each run makes a graph of queries over a few inputs. What a query reads
   depends on what it has read so far, so its reads change as the inputs
   do; some queries divide their result, so that it often comes out the
   same; some are saved; and the queries are spread over the phases. The
   run then makes random steps: it sets or removes an input, asks for a
   result, releases one, brings the engine up to date, writes the state and
   opens it again, or opens a second engine from the same state and changes
   that. After each step the engine is audited against a new engine with no
   bases and the same inputs.

   It prints the seed and the steps of each run that fails, and exits with
   status 1 if there was one. *)

let inputs = 6
let nodes = 40
let phases = [| Query.Syntax; Declarations; Resolution; Interfaces; Bodies; Lowering; Keys |]
let phase_of index = index * Array.length phases / nodes
let value_input : (int, int) Query.input = Query.input ~name:"fuzz_input" ~show:string_of_int ()

(* A fixed mixing of integers, so that a node's reads are a function of its
   index and of what it has read, and of nothing else. *)
let mix a b c =
  let h = ref (a * 0x9E3779B1 lxor (b * 0x85EBCA77) lxor (c * 0xC2B2AE3D)) in
  h := !h lxor (!h lsr 15);
  h := !h * 0x2C1B3C6D;
  h := !h lxor (!h lsr 12);
  abs !h

(* One query for each phase, keyed by a node's index. A node reads inputs
   and nodes of lower index, which are of its phase or an earlier one. *)
let rec queries =
  lazy
    (Array.mapi
       (fun rank phase ->
         Query.query ~name:(Printf.sprintf "fuzz_%d" rank) ~phase
           ~saved:(rank mod 2 = 0)
           ~show:string_of_int compute)
       phases)

and compute database index =
  let total = ref index in
  for step = 0 to 2 + (index mod 3) do
    let choice = mix index step (!total mod 3) in
    if choice mod 4 = 0 || index = 0 then
      total :=
        !total + Option.value (Query.find database value_input (choice / 4 mod inputs)) ~default:7
    else
      let other = choice / 4 mod index in
      total := !total + Query.demand database (Lazy.force queries).(phase_of other) other
  done;
  (* Some results come out the same for many inputs. *)
  if index mod 3 = 0 then !total / 64 else !total land 0xFFFF

let node index = (Lazy.force queries).(phase_of index)
let version = "fuzz"

type world = {
  store : Store.t;
  mutable engine : Engine.t;
  mutable others : Engine.t list;  (** Engines opened from a state this one wrote *)
  mutable trail : string list;
}

let counter = ref 0

let fresh_store () =
  incr counter;
  let directory =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-engine-fuzz-%d-%d" (Unix.getpid ()) !counter)
  in
  ignore (Sys.command ("rm -rf " ^ Filename.quote directory));
  Store.open_ directory

let note world format = Printf.ksprintf (fun text -> world.trail <- text :: world.trail) format

let step world random =
  let engine =
    match world.others with
    | other :: _ when Random.State.int random 4 = 0 -> other
    | _ -> world.engine
  in
  let which = if engine == world.engine then "" else " in the second engine" in
  match Random.State.int random 12 with
  | 0 | 1 | 2 | 3 ->
      let key = Random.State.int random inputs and value = Random.State.int random 1000 in
      note world "set %d to %d%s" key value which;
      Engine.set engine value_input key value
  | 4 ->
      let key = Random.State.int random inputs in
      note world "remove %d%s" key which;
      Engine.remove engine value_input key
  | 5 | 6 | 7 ->
      let index = Random.State.int random nodes in
      note world "get %d%s" index which;
      ignore (Engine.get engine (node index) index)
  | 8 ->
      let index = Random.State.int random nodes in
      note world "release %d%s" index which;
      Engine.release engine (node index) index
  | 9 ->
      note world "stabilize%s" which;
      ignore (Engine.stabilize engine)
  | 10 -> (
      let full = Random.State.int random 4 = 0 in
      note world "write%s and open again" (if full then " the whole state" else "");
      let artifact = Engine.write ~full world.engine in
      match Engine.open_ world.store ~version ~bases:[] artifact with
      | Some opened ->
          if Sys.getenv_opt "FUZZ_DEBUG" <> None then
            List.iter
              (fun node ->
                match Engine.counterpart node opened with
                | None -> Printf.printf "  [open] %s is missing\n" (Engine.label node)
                | Some other ->
                    if not (Engine.same_outcome world.engine node opened other) then
                      Printf.printf "  [open] %s differs (own before: %b, own after: %b)\n"
                        (Engine.label node)
                        (List.memq node (Engine.differing world.engine))
                        (List.memq other (Engine.differing opened)))
              (Engine.nodes world.engine);
          world.engine <- opened
      | None -> note world "the store had no such state")
  | _ -> (
      note world "write and open a second engine";
      let artifact = Engine.write world.engine in
      match Engine.open_ world.store ~version ~bases:[] artifact with
      | Some opened -> world.others <- [ opened ]
      | None -> note world "the store had no such state")

let run ~seed ~steps =
  let random = Random.State.make [| seed |] in
  let store = fresh_store () in
  let engine = Engine.create () in
  Engine.attach engine store ~version;
  let world = { store; engine; others = []; trail = [] } in
  let failed = ref false in
  (try
     for _ = 1 to steps do
       if not !failed then begin
         step world random;
         List.iter
           (fun engine ->
             match Engine.audit ~flat:true engine with
             | [] -> ()
             | problems ->
                 failed := true;
                 Printf.printf "seed %d, after:\n  %s\n" seed
                   (String.concat "\n  " (List.rev world.trail));
                 List.iter (Printf.printf "    %s\n") problems;
                 if Sys.getenv_opt "FUZZ_DEBUG" <> None then begin
                   let own = Engine.differing engine in
                   Printf.printf "    holds: %s\n"
                     (String.concat " "
                        (List.map
                           (fun node ->
                             Printf.sprintf "%s<-[%s]" (Engine.label node)
                               (String.concat ","
                                  (List.map Engine.label (Engine.reads engine node))))
                           own));
                   Printf.printf "    all: %s\n"
                     (String.concat " " (List.map Engine.label (Engine.nodes engine)))
                 end)
           (world.engine :: world.others)
       end
     done
   with exception_ ->
     failed := true;
     Printf.printf "seed %d raised %s after:\n  %s\n" seed (Printexc.to_string exception_)
       (String.concat "\n  " (List.rev world.trail)));
  Store.close store;
  ignore (Sys.command ("rm -rf " ^ Filename.quote (Store.directory store)));
  !failed

let () =
  let seed = ref 1 and count = ref 200 and steps = ref 60 in
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, "N The first seed (1)");
      ("--count", Arg.Set_int count, "N How many runs (200)");
      ("--steps", Arg.Set_int steps, "N How many steps a run makes (60)");
    ]
    (fun argument -> raise (Arg.Bad ("unexpected " ^ argument)))
    "engine_fuzz [--seed N] [--count N] [--steps N]";
  let failures = ref 0 in
  for offset = 0 to !count - 1 do
    if run ~seed:(!seed + offset) ~steps:!steps then incr failures
  done;
  Printf.printf "%d of %d runs failed\n" !failures !count;
  if !failures > 0 then exit 1
