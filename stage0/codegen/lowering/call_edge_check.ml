let raise_bug format = Compiler_bug.raise_bug ~stage:"Call_edge_check" format
let is_runtime_call (path : Path.t) = Well_known.is Write_fully path

let list_code_supplied_to (interface : Interface.Lookups.t) path instantiation =
  match Interface.Impls.read_signature interface path with
  | Some (signature : Types.signature) ->
      Mir.Call_edges.list_code_supplied_to_generics interface signature.generics
        (Monomorphic.make_signature_substitution signature instantiation)
  | None -> []

let check (interface : Interface.Lookups.t) ~find_call_edges (item : Lowered.Item.t) fragment =
  match item with
  | Code { path = caller; instantiation; _ } -> (
      match find_call_edges caller with
      | None -> ()
      | Some call_edges ->
          let allowed =
            call_edges
            @ List.concat_map
                (fun callee -> Option.value (find_call_edges callee) ~default:[])
                call_edges
            @ list_code_supplied_to interface caller instantiation
          in
          List.iter
            (fun (called : Lowered.Item.t) ->
              match called with
              | Code { path = callee; _ }
                when not (is_runtime_call callee || List.exists (Path.equal callee) allowed) ->
                  raise_bug "%s calls %s, which is not among its call edges"
                    (Lowered.Item.to_string item) (Lowered.Item.to_string called)
              | _ -> ())
            (Emit_c.called fragment))
  | _ -> ()
