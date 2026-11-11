(* The scanner and layout run as one pipeline: layout requests each raw
   token from the scanner when it needs it. Only a file with brackets still
   open at its end is lexed twice, the second time with bracket recovery
   enabled. *)

let attempt source ~recovery =
  let diagnostics = Diagnostic.Collector.create () in
  let scanner = Scanner.create source diagnostics in
  let tokens, open_at_end =
    Layout.file ~source ~diagnostics ~recovery (fun () -> Scanner.next scanner)
  in
  (tokens, Diagnostic.Collector.to_list diagnostics, open_at_end)

let lex source =
  match attempt source ~recovery:false with
  | tokens, diagnostics, false -> (tokens, diagnostics)
  | _, _, true ->
      let tokens, diagnostics, _ = attempt source ~recovery:true in
      (tokens, diagnostics)
