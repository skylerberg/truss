let make_state () : State.lending_state = { part_type = None; lent_parts = [] }
let enter_method (context : State.context) ~part_type = context.lending.part_type <- Some part_type

let holds_where_lent (clause : Mir.formula) =
  Contracts.mentions_result clause && not (Contracts.mentions_final_result clause)

let find_part_sort (context : State.context) = Option.map Encoding.sort_of context.lending.part_type

let lend_part (context : State.context) (frame : State.frame) origin (mode : Language.Mode.t)
    ~handed ~lends_places ~write_back =
  let location = Facts.locate frame origin in
  match context.lending.part_type with
  | None -> Facts.raise_unsupported location Lent_part_outside_lending_method
  | Some part_type ->
      let lent = { frame with result = Some handed } in
      context.lending.lent_parts <-
        { lent_frame = lent; lent_origin = origin } :: context.lending.lent_parts;
      Validity.check_valid context lent location part_type handed ~deep:true ~moment:Part_lent;
      if mode = Language.Mode.Mut && lends_places then begin
        let final = Encoding.arrive lent "lent" part_type in
        Validity.assume_valid context lent part_type final;
        let written : State.frame = write_back lent final in
        { written with final_result = Some final }
      end
      else { lent with final_result = Some handed }

let list_lent_parts (context : State.context) = List.rev context.lending.lent_parts
let bind_final (frame : State.frame) final = { frame with final_result = Some final }

let read_final_result (frame : State.frame) =
  match frame.final_result with
  | Some final -> final
  | None ->
      Facts.raise_bug "`%s` reads `final(result)` where no lend has ended"
        (Resolve.Names.show_key frame.source.key)
